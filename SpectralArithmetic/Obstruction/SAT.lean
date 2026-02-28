/-
  Spectral Arithmetic: SAT Encoding as Term Structure
  ====================================================

  This file encodes k-SAT formulas as Terms in the framework's free algebra.
  The encoding is PURELY STRUCTURAL: the Term shape mirrors the SAT formula
  structure (compose for conjunction, nested compose for clauses), but eval
  does NOT correspond to Boolean satisfaction.

  The purpose is to study how deepRewrite (Leibniz extensionalization) behaves
  on SAT-structured terms — specifically, how normalization cost depends on
  clause width k and formula structure.

  Key design choices:
  - Literal, Clause, CNFFormula are separate types describing SAT instances
  - Boolean evaluation (evalLiteral, evalClause, evalCNF) uses standard Bool
  - Term encoding maps resolved formulas to Terms via literalToTerm/clauseToTerm
  - obs wrapping at the formula level creates Leibniz rewrite sites
  - No semantic correspondence is claimed between Term eval and Boolean satisfaction
-/

import SpectralArithmetic.Obstruction.Complexity

namespace SpectralMonoid

open Term

/-! ## Part 1: SAT Formula Structure

    Standard Boolean satisfiability structures, independent of the Term algebra.
    These describe the combinatorial objects; the Term encoding comes later. -/

/-- A literal is a variable index with polarity.
    pos = true means the variable appears positively (x_i).
    pos = false means the variable appears negated (NOT x_i). -/
structure Literal where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

/-- A clause is a disjunction (OR) of literals. -/
abbrev Clause := List Literal

/-- A CNF formula is a conjunction (AND) of clauses. -/
abbrev CNFFormula := List Clause

/-- An assignment maps variable indices to Boolean values. -/
abbrev Assignment := Nat → Bool

/-! ## Part 2: Boolean Evaluation (Standard SAT Semantics)

    These operate on Bool, not on Terms. They define what it means
    for an assignment to satisfy a formula. -/

/-- Evaluate a literal under an assignment. -/
def evalLiteral (σ : Assignment) (l : Literal) : Bool :=
  if l.pos then σ l.var else !σ l.var

/-- Evaluate a clause (OR of literals) under an assignment. -/
def evalClause (σ : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral σ)

/-- Evaluate a CNF formula (AND of clauses) under an assignment. -/
def evalCNF (σ : Assignment) (φ : CNFFormula) : Bool :=
  φ.all (evalClause σ)

/-- A formula is satisfiable if there exists a satisfying assignment. -/
def Satisfiable (φ : CNFFormula) : Prop :=
  ∃ σ : Assignment, evalCNF σ φ = true

/-! ## Part 3: Structural Predicates

    Properties of formulas that determine their complexity class. -/

/-- A formula is k-SAT if every clause has exactly k literals. -/
def isKSAT (k : Nat) (φ : CNFFormula) : Prop :=
  ∀ c ∈ φ, c.length = k

/-- The set of variable indices appearing in a clause. -/
def clauseVarsList (c : Clause) : List Nat :=
  c.map Literal.var

/-- The number of distinct variables in a formula. -/
def numVars (φ : CNFFormula) : Nat :=
  ((φ.flatMap clauseVarsList).eraseDups).length

/-- The number of clauses in a formula. -/
def numClauses (φ : CNFFormula) : Nat :=
  φ.length

/-! ## Part 4: Term Encoding

    Maps resolved SAT formulas to Terms. The encoding is structural:
    - A resolved literal maps to f₀ (true) or z (false)
    - A clause is a right-nested compose chain of its resolved literals
    - A formula wraps the compose of clause terms in obs, creating
      Leibniz rewrite sites

    The obs wrapping is the key: it is what makes deepRewrite
    (extensionalization) fire on the formula structure. Without obs,
    the terms are obs-free and deepRewrite is the identity. -/

/-- Encode a resolved literal as a Term.
    True (satisfied) → f₀ (the multiplicative identity).
    False (unsatisfied) → z (the annihilator).
    This uses the ring convention where f₀ = 1 and z = 0. -/
def literalToTerm (σ : Assignment) (l : Literal) : Term :=
  if evalLiteral σ l then .f₀ else .z

/-- Right-nested compose chain from a list of terms.
    compose(t₁, compose(t₂, ... compose(t_{k-1}, t_k)...))
    Empty list: f₀ (identity). Single term: that term. -/
def composeChain : List Term → Term
  | [] => .f₀
  | [t] => t
  | t :: ts => .compose t (composeChain ts)

/-- Encode a clause as a right-nested compose chain of resolved literals.
    compose(l₁, compose(l₂, ... compose(l_{k-1}, l_k)...))
    Empty clause maps to f₀ (vacuously true in AND interpretation).
    Single literal maps to itself (no compose wrapper). -/
def clauseToTerm (σ : Assignment) (c : Clause) : Term :=
  composeChain (c.map (literalToTerm σ))

/-- Inner compose chain of clause terms (no outer obs). -/
def formulaInner (σ : Assignment) : CNFFormula → Term
  | [] => .f₀
  | [c] => clauseToTerm σ c
  | c :: cs => .compose (clauseToTerm σ c) (formulaInner σ cs)

/-- Encode a CNF formula as obs of a right-nested compose chain of clause terms.
    obs(compose(C₁, compose(C₂, ... compose(C_{m-1}, C_m)...)))
    The outer obs creates a Leibniz rewrite site at every compose node.
    Empty formula maps to obs(f₀) (trivially satisfiable).
    Single clause maps to obs of that clause's term. -/
def formulaToTerm (σ : Assignment) (φ : CNFFormula) : Term :=
  .obs (formulaInner σ φ)

/-! ## Part 5: Structural Properties of the Encoding -/

/-- A resolved literal is always f₀ or z. -/
theorem literalToTerm_values (σ : Assignment) (l : Literal) :
    literalToTerm σ l = .f₀ ∨ literalToTerm σ l = .z := by
  unfold literalToTerm
  split
  · left; rfl
  · right; rfl

/-- termSize of a resolved literal is 1. -/
theorem literalToTerm_size (σ : Assignment) (l : Literal) :
    termSize (literalToTerm σ l) = 1 := by
  unfold literalToTerm
  split <;> simp [termSize]

/-- A resolved literal is obs-free. -/
theorem literalToTerm_isObsFree (σ : Assignment) (l : Literal) :
    isObsFree (literalToTerm σ l) = true := by
  unfold literalToTerm
  split <;> simp [isObsFree]

/-- composeChain of a single element is that element. -/
theorem composeChain_single (t : Term) : composeChain [t] = t := rfl

/-- composeChain of cons with >= 2 elements nests compose. -/
theorem composeChain_cons2 (t t' : Term) (ts : List Term) :
    composeChain (t :: t' :: ts) = .compose t (composeChain (t' :: ts)) := rfl

/-- composeChain of obs-free terms is obs-free. -/
theorem composeChain_isObsFree (ts : List Term)
    (hall : ∀ t ∈ ts, isObsFree t = true) :
    isObsFree (composeChain ts) = true := by
  induction ts with
  | nil => simp [composeChain, isObsFree]
  | cons t rest ih =>
    have ht : isObsFree t = true := hall t (List.mem_cons_self ..)
    match rest with
    | [] => exact ht
    | _ :: _ =>
      simp only [composeChain, isObsFree, Bool.and_eq_true]
      exact ⟨ht, ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))⟩

/-- clauseToTerm always produces obs-free terms. -/
theorem clauseToTerm_isObsFree (σ : Assignment) (c : Clause) :
    isObsFree (clauseToTerm σ c) = true := by
  unfold clauseToTerm
  apply composeChain_isObsFree
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨l, _, rfl⟩ := ht
  exact literalToTerm_isObsFree σ l

/-- deepRewrite is the identity on clause terms (they are obs-free). -/
theorem deepRewrite_clauseToTerm (σ : Assignment) (c : Clause) :
    deepRewrite (clauseToTerm σ c) = clauseToTerm σ c :=
  deepRewrite_obsFree _ (clauseToTerm_isObsFree σ c)

/-- termSize of clauseToTerm for a single literal is 1. -/
theorem clauseToTerm_size_single (σ : Assignment) (l : Literal) :
    termSize (clauseToTerm σ [l]) = 1 := by
  simp [clauseToTerm, composeChain, literalToTerm_size]

/-- termSize of clauseToTerm for two literals is 3. -/
theorem clauseToTerm_size_two (σ : Assignment) (l₁ l₂ : Literal) :
    termSize (clauseToTerm σ [l₁, l₂]) = 3 := by
  simp [clauseToTerm, composeChain, termSize, literalToTerm_size]

/-- termSize of clauseToTerm for three literals is 5. -/
theorem clauseToTerm_size_three (σ : Assignment) (l₁ l₂ l₃ : Literal) :
    termSize (clauseToTerm σ [l₁, l₂, l₃]) = 5 := by
  simp [clauseToTerm, composeChain, termSize, literalToTerm_size]

/-- formulaInner is obs-free. -/
theorem formulaInner_isObsFree (σ : Assignment) (φ : CNFFormula) :
    isObsFree (formulaInner σ φ) = true := by
  induction φ with
  | nil => simp [formulaInner, isObsFree]
  | cons c cs ih =>
    match cs with
    | [] =>
      simp only [formulaInner]
      exact clauseToTerm_isObsFree σ c
    | c' :: cs' =>
      simp only [formulaInner, isObsFree, Bool.and_eq_true]
      exact ⟨clauseToTerm_isObsFree σ c, ih⟩

/-- formulaToTerm always has obs at root. -/
theorem formulaToTerm_has_obs (σ : Assignment) (φ : CNFFormula) :
    ∃ t, formulaToTerm σ φ = .obs t := by
  exact ⟨formulaInner σ φ, rfl⟩

/-- formulaToTerm with at least 2 clauses has obs(compose(...)) at root,
    which is NOT obs-normal — it is a Leibniz rewrite site. -/
theorem formulaToTerm_not_obsNormal (σ : Assignment)
    (c₁ c₂ : Clause) (cs : List Clause) :
    isObsNormal (formulaToTerm σ (c₁ :: c₂ :: cs)) = false := by
  simp [formulaToTerm, formulaInner, isObsNormal]

/-- formulaToTerm for an empty formula is obs(f₀), which IS obs-normal. -/
theorem formulaToTerm_empty_obsNormal (σ : Assignment) :
    isObsNormal (formulaToTerm σ []) = true := by
  simp [formulaToTerm, formulaInner, isObsNormal]

/-! ## Part 6: Compose Chain Normalization Depth

    Key structural result: obs(composeChain [a₁, ..., aₖ]) with obs-free atoms
    has normalization depth k-1 (for k >= 2). This is fundamentally different
    from nestedObsCompose, which has constant depth 2.

    The difference: nestedObsCompose has obs at EVERY nesting level, so
    deepRewrite resolves all simultaneously bottom-up. A compose chain has
    compose nesting WITHOUT intervening obs, so the Leibniz expansion at
    the outer obs creates NEW obs(compose) sites at inner levels.

    Clause width k directly controls normalization depth. -/

/-- obs(compose(a, b)) with obs-free a, b has normalization depth 1. -/
theorem obs_compose_2_normDepth :
    normDepthBounded 3 (.obs (.compose Term.f₀ Term.f₀)) = 1 := by decide

/-- obs(compose(a, compose(b, c))) with obs-free atoms: normalization depth 2. -/
theorem obs_compose_3_normDepth :
    normDepthBounded 5
      (.obs (.compose Term.f₀ (.compose Term.f₀ Term.f₀))) = 2 := by
  decide

/-- obs(compose(a, compose(b, compose(c, d)))): normalization depth 3. -/
theorem obs_compose_4_normDepth :
    normDepthBounded 7
      (.obs (.compose Term.f₀
        (.compose Term.f₀ (.compose Term.f₀ Term.f₀)))) = 3 := by
  decide

/-- obs(compose chain of 5 atoms): normalization depth 4. -/
theorem obs_compose_5_normDepth :
    normDepthBounded 9
      (.obs (.compose Term.f₀
        (.compose Term.f₀
          (.compose Term.f₀ (.compose Term.f₀ Term.f₀))))) = 4 := by
  decide

/-! The pattern is clear: normalization depth = k - 1 for k atoms.
    The general theorem (by induction on k) is proved in Phase 3
    (Complexity.lean extension). These concrete instances serve as
    ground truth that the general proof must match. -/

end SpectralMonoid
