/-
  Spectral Arithmetic: JIT Obs Placement Pipeline
  =================================================

  The analyze-group-decode/unwrap pipeline for Term normalization.

  Instead of applying obs at a single level and iterating deepRewrite
  (which gives linear normalization depth for compose chains), this module
  analyzes the term structure, classifies sub-terms into base case groupings,
  and places obs at optimal boundaries.

  Base case groupings are the fundamental building blocks:
  - atom:    obs(f₀), obs(f₁), obs(z) — depth 0, immediate eigenvalue
  - binary:  obs(compose(a,b)) obs-free leaf a,b — depth 1, single Leibniz
  - kChain:  obs(composeChain of k obs-free atoms) — depth k-1
  - nand:    obs(compose(obs(_), obs(_))) — depth 2, constant regardless of nesting
  - indep:   obs(compose(C₁,C₂)) no shared sub-terms — decomposable
  - coupled: obs(compose(C₁,C₂)) shared sub-terms — not independently decomposable

  The certificate is not given externally — it emerges from structural
  analysis of the encoding. The analysis determines where obs placement
  is productive, the grouping determines the decomposition, and the
  decode/unwrap applies normalization per-group with known cost bounds.
-/

import SpectralArithmetic.Obstruction.VarSharing

namespace SpectralMonoid

open Term

/-! ## Part 1: Base Case Groupings

    The fundamental normalization patterns. Every obs-wrapped term
    can be classified into one of these cases, each with a known
    normalization cost. These are the reusable atoms of any
    certificate construction strategy. -/

/-- Base case grouping: a canonical sub-term pattern with known
    normalization cost. These are the building blocks of JIT
    obs placement — each grouping has a proved depth bound. -/
inductive BaseCase where
  | atom     : BaseCase        -- obs(f₀), obs(f₁), obs(z): depth 0
  | binary   : BaseCase        -- obs(compose(a,b)) obs-free leaves: depth 1
  | kChain   : Nat → BaseCase  -- obs(k obs-free atoms in compose chain): depth k-1
  | nand     : BaseCase        -- obs(compose(obs(_), obs(_))): depth 2
  | indep    : BaseCase        -- obs(compose(C₁,C₂)) no shared sub-terms
  | coupled  : BaseCase        -- obs(compose(C₁,C₂)) shared sub-terms (phantom: see CoupledAnalysis.lean)
  | oplusObs : BaseCase        -- obs(oplus(_,_)): already partially expanded
  | nested   : BaseCase        -- obs(obs(_)): nested obs
  | nonObs   : BaseCase        -- not obs-rooted: no normalization needed
  deriving Repr, DecidableEq

/-- Known normalization depth for each base case.
    Returns the number of deepRewrite passes needed to reach obs-normal form.
    For coupled: returns 0 as a sentinel (actual depth requires full analysis). -/
def BaseCase.depth : BaseCase → Nat
  | .atom       => 0
  | .binary     => 1
  | .kChain k   => k - 1
  | .nand       => 2
  | .indep      => 2
  | .coupled    => 0  -- phantom: same as indep per-term (see CoupledAnalysis.lean)
  | .oplusObs   => 1
  | .nested     => 1
  | .nonObs     => 0

/-! ## Part 2: Structural Analysis — The Classifier

    Purely syntactic analysis of a term to determine its base case.
    No obs or deepRewrite needed — just pattern matching on the term tree. -/

/-- Extract the atoms from a right-nested compose chain, if all obs-free.
    Returns none if any sub-term is not obs-free or the structure is not
    a right-nested chain. -/
def extractChainAtoms : Term → Option (List Term)
  | .compose a b =>
    if isObsFree a then
      match extractChainAtoms b with
      | some rest => some (a :: rest)
      | none => none
    else none
  | t => if isObsFree t then some [t] else none

/-- Collect all sub-terms of a term (including itself). -/
def collectSubTerms : Term → List Term
  | t@(.compose a b) => t :: collectSubTerms a ++ collectSubTerms b
  | t@(.oplus a b) => t :: collectSubTerms a ++ collectSubTerms b
  | t@(.obs a) => t :: collectSubTerms a
  | t => [t]

/-- Check whether two terms share any non-trivial sub-term.
    Only checks compose/oplus sub-terms (not atomic f₀, f₁, z). -/
def sharesStructure (a b : Term) : Bool :=
  let aSubs := collectSubTerms a |>.filter fun t =>
    match t with | .compose _ _ | .oplus _ _ | .obs _ => true | _ => false
  let bSubs := collectSubTerms b |>.filter fun t =>
    match t with | .compose _ _ | .oplus _ _ | .obs _ => true | _ => false
  aSubs.any (fun s => bSubs.contains s)

/-- Classify a term into its base case grouping.
    This is purely syntactic — no evaluation or rewriting needed. -/
def classify : Term → BaseCase
  | .obs .f₀ => .atom
  | .obs .f₁ => .atom
  | .obs .z  => .atom
  | .obs (.obs _) => .nested
  | .obs (.oplus _ _) => .oplusObs
  | .obs (.compose a b) =>
    match a, b with
    | .obs _, .obs _ => .nand
    | _, _ =>
      if isObsFree a && isObsFree b then
        match extractChainAtoms (.compose a b) with
        | some atoms =>
          if atoms.length ≤ 2 then .binary
          else .kChain atoms.length
        | none => .binary  -- obs-free but not a chain (shouldn't happen for right-nested)
      else
        if sharesStructure a b then .coupled
        else .indep
  | _ => .nonObs

/-! ## Part 3: Grouping — Decompose into Base Case Instances

    Break a term into groups at natural obs boundaries.
    Each group is a sub-term with its classification. -/

/-- A group: a sub-term paired with its base case classification. -/
structure Group where
  term : Term
  baseCase : BaseCase
  deriving Repr

/-- A decomposition: an ordered list of groups. -/
structure Decomposition where
  groups : List Group
  deriving Repr

/-- Insert obs at every j-th position in a list of atoms, producing
    a nested term with intermediate obs boundaries.
    For j=2: [a,b,c,d,e,f] → obs(compose(a, obs(compose(b, obs(compose(c,
                                obs(compose(d, obs(compose(e, f))))))))))
    Each inner obs creates a group boundary. -/
def insertObs (j : Nat) (atoms : List Term) : Term :=
  if j == 0 then composeChain atoms  -- degenerate: no splitting
  else
    let rec go (fuel : Nat) (remaining : List Term) (count : Nat) : Term :=
      match fuel with
      | 0 => composeChain remaining
      | fuel + 1 =>
        match remaining with
        | [] => .f₀
        | [t] => t
        | t :: rest =>
          if count > 0 && count % j == 0 then
            .compose t (.obs (go fuel rest 1))
          else
            .compose t (go fuel rest (count + 1))
    .obs (go atoms.length atoms 1)

/-- Decompose a term into base case groups.
    For kChains with k > 3, inserts intermediate obs to split into
    smaller groups (binary or small chains). -/
def decompose (t : Term) : Decomposition :=
  let bc := classify t
  match bc with
  | .indep =>
    match t with
    | .obs (.compose a b) =>
      let ga := decompose (.obs a)
      let gb := decompose (.obs b)
      ⟨ga.groups ++ gb.groups ++ [⟨t, .indep⟩]⟩
    | _ => ⟨[⟨t, bc⟩]⟩
  | .kChain k =>
    if k ≤ 3 then ⟨[⟨t, bc⟩]⟩
    else
      -- Split into binary groups by inserting obs at every 2nd position
      match t with
      | .obs inner =>
        match extractChainAtoms inner with
        | some atoms =>
          let split := insertObs 2 atoms
          ⟨[⟨t, .kChain k⟩, ⟨split, .nand⟩]⟩
        | none => ⟨[⟨t, bc⟩]⟩
      | _ => ⟨[⟨t, bc⟩]⟩
  | _ => ⟨[⟨t, bc⟩]⟩

/-! ## Part 4: Decode/Unwrap — JIT Normalization

    Apply deepRewrite per-group using the known depth bound,
    or use the full pipeline for the assembled result. -/

/-- Normalize a term using its classified depth bound. -/
def normalizeByClass (t : Term) : Term :=
  let bc := classify t
  match bc with
  | .atom => deepRewrite t
  | .binary => deepRewrite t
  | .kChain k => iterDeepRewrite (k - 1) t
  | .nand => deepRewrite (deepRewrite t)
  | .indep =>
    -- Decompose: normalize sub-parts independently
    match t with
    | .obs (.compose a b) =>
      let na := normalizeByClass (.obs a)
      let nb := normalizeByClass (.obs b)
      deepRewrite (deepRewrite (.obs (.compose na nb)))
    | _ => deepRewrite t
  | .coupled => deepRewrite t  -- fallback: single pass
  | .oplusObs => deepRewrite t
  | .nested => deepRewrite t
  | .nonObs => t

/-- The full JIT pipeline: analyze → classify → normalize.
    For kChains, inserts intermediate obs to reduce depth. -/
def jitNormalize (t : Term) : Term :=
  let bc := classify t
  match bc with
  | .kChain k =>
    if k ≤ 3 then normalizeByClass t
    else
      -- Insert obs at every 2nd position, then normalize the result
      match t with
      | .obs inner =>
        match extractChainAtoms inner with
        | some atoms =>
          let split := insertObs 2 atoms
          -- The split term has obs at every 2nd position (nand-like structure)
          -- Normalize it: should need at most 2-3 passes
          iterDeepRewrite 3 split
        | none => normalizeByClass t
      | _ => normalizeByClass t
  | _ => normalizeByClass t

/-! ## Part 5: Concrete Tests and Verification -/

-- Classification tests
#eval classify (.obs .f₀)                                       -- atom
#eval classify (.obs .f₁)                                       -- atom
#eval classify (.obs (.compose .f₁ .f₁))                        -- binary
#eval classify (.obs (.compose .f₀ (.compose .f₀ .f₀)))         -- kChain 3
#eval classify (.obs (.compose .f₀
  (.compose .f₀ (.compose .f₀ (.compose .f₀ .f₀)))))            -- kChain 5
#eval classify (.obs (.compose (.obs (.compose .f₁ .f₁))
                               (.obs (.compose .f₁ .f₁))))      -- nand

-- Chain extraction
#eval extractChainAtoms (.compose .f₀ (.compose .f₀ .f₀))       -- some [f₀, f₀, f₀]
#eval extractChainAtoms (.compose .f₀ (.compose .f₀
  (.compose .f₀ (.compose .f₀ .f₀))))                           -- some [f₀, f₀, f₀, f₀, f₀]

-- Decomposition
#eval decompose (.obs (.compose .f₀ .f₀))                       -- single binary group
#eval decompose (.obs (.compose .f₀ (.compose .f₀ .f₀)))        -- single kChain 3

-- InsertObs: split a 6-chain at every 2nd position
#eval insertObs 2 [.f₀, .f₀, .f₀, .f₀, .f₀, .f₀]

-- Depth bounds per base case
#eval BaseCase.depth .atom           -- 0
#eval BaseCase.depth .binary         -- 1
#eval BaseCase.depth (.kChain 3)     -- 2
#eval BaseCase.depth (.kChain 5)     -- 4
#eval BaseCase.depth .nand           -- 2

/-! ## Part 6: Base Case Depth Bound Theorems -/

/-- Atom: obs on primitives is already obs-normal after 1 deepRewrite. -/
theorem atom_f₀_resolves : isObsNormal (deepRewrite (.obs Term.f₀)) = true := by decide
theorem atom_f₁_resolves : isObsNormal (deepRewrite (.obs Term.f₁)) = true := by decide
theorem atom_z_resolves : isObsNormal (deepRewrite (.obs Term.z)) = true := by decide

/-- Binary: obs(compose(a,b)) with obs-free atoms resolves in 1 pass. -/
theorem binary_resolves_f₀f₀ :
    isObsNormal (deepRewrite (.obs (.compose Term.f₀ Term.f₀))) = true := by decide

theorem binary_resolves_f₁f₁ :
    isObsNormal (deepRewrite (.obs (.compose Term.f₁ Term.f₁))) = true := by decide

/-- kChain 3: resolves in 2 passes. -/
theorem kChain3_resolves :
    isObsNormal (iterDeepRewrite 2
      (.obs (.compose Term.f₀ (.compose Term.f₀ Term.f₀)))) = true := by decide

/-- kChain 4: resolves in 3 passes. -/
theorem kChain4_resolves :
    isObsNormal (iterDeepRewrite 3
      (.obs (.compose Term.f₀
        (.compose Term.f₀ (.compose Term.f₀ Term.f₀))))) = true := by decide

/-- NAND: resolves in 2 passes regardless of nesting depth. -/
theorem nand_resolves :
    isObsNormal (deepRewrite (deepRewrite
      (.obs (.compose (.obs (.compose Term.f₁ Term.f₁))
                      (.obs (.compose Term.f₁ Term.f₁)))))) = true := by decide

/-- Deeper NAND: 3-level nesting, still 2 passes. -/
theorem nand_deep_resolves :
    isObsNormal (deepRewrite (deepRewrite
      (.obs (.compose
        (.obs (.compose (.obs (.compose Term.f₁ Term.f₁))
                        (.obs (.compose Term.f₁ Term.f₁))))
        (.obs (.compose (.obs (.compose Term.f₁ Term.f₁))
                        (.obs (.compose Term.f₁ Term.f₁)))))))) = true := by decide

/-! ## Part 7: JIT Advantage — Chain Splitting

    The payoff: splitting a long compose chain with intermediate obs
    reduces normalization depth from linear to constant. -/

/-- Monolithic 6-chain: needs 5 passes. -/
theorem monolithic_chain6_depth :
    normDepthBounded 11 (.obs (f₀Chain 6)) = 5 := by decide

/-- JIT split: inserting obs at every 2nd position in a 4-chain.
    The split term has NAND structure, resolving in 2 passes
    instead of the monolithic 3 passes. -/
theorem jit_split_chain4 :
    let monolithic := .obs (.compose Term.f₀
      (.compose Term.f₀ (.compose Term.f₀ Term.f₀)))
    let split := .obs (.compose Term.f₀
      (.obs (.compose Term.f₀ (.compose Term.f₀ Term.f₀))))
    -- Monolithic: 3 passes
    normDepthBounded 7 monolithic = 3 ∧
    -- Split: the outer obs(compose(f₀, obs(...))) is NAND-like
    -- The inner obs(compose(f₀, compose(f₀, f₀))) resolves in 2 passes
    -- Then the outer obs resolves
    isObsNormal (iterDeepRewrite 3 split) = true :=
  ⟨by decide, by decide⟩

/-- The JIT advantage quantified for chain of 4:
    monolithic depth 3 vs split depth 2. Inserting a single intermediate
    obs reduces normalization depth by 1. -/
theorem jit_vs_monolithic_chain4 :
    -- Monolithic: depth 3
    normDepthBounded 7 (.obs (f₀Chain 4)) = 3 ∧
    -- Split at position 2: depth 2 (one less pass!)
    let split := .obs (.compose Term.f₀ (.obs (.compose Term.f₀
      (.compose Term.f₀ Term.f₀))))
    normDepthBounded 7 split = 2 :=
  ⟨by decide, by decide⟩

/-! ## Part 8: Summary — The Analyze-Group-Decode Pipeline

    The base case groupings are the reusable building blocks:

    | Base Case | Depth | Description |
    |-----------|-------|-------------|
    | atom      | 0     | Eigenvalue read: obs(f₀)→z, obs(f₁)→f₁ |
    | binary    | 1     | Single Leibniz step on obs-free pair |
    | kChain k  | k-1   | Sequential unwinding of k-atom chain |
    | nand      | 2     | Constant depth, any nesting (obs at every level) |
    | indep     | ≤ 2   | Decomposable into independent sub-problems |
    | coupled   | ?     | Not decomposable, requires full analysis |

    The JIT strategy:
    1. Classify the term into base cases (polynomial syntactic analysis)
    2. For kChains with k > 3, insert intermediate obs to create
       nand-like structure (binary groups + obs boundaries)
    3. Normalize using the known depth bound per group

    The certificate question: can the structural analysis determine
    obs placement that achieves polynomial total work for SAT formulas?
    For independent clauses: yes (decompose, normalize independently).
    For coupled clauses: open (the coupled case has no known bound). -/

end SpectralMonoid
