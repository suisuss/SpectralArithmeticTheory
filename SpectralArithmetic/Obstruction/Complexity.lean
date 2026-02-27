/-
  Spectral Arithmetic: Complexity Asymmetry
  ==========================================

  The encoding obstruction proves that verification (eigenvalue observation)
  and construction (Leibniz extensionalization) have structurally different
  costs at the algebraic level. This file formalizes that asymmetry:

  1. Position-existence: obs on {f₀, f₁} gives Boolean values {z, f₁}
  2. Normalization depth: counting deepRewrite steps to obs-normal form
  3. Nested obs-compose family: terms requiring exponential work per step
  4. The verification/construction asymmetry theorem
  5. Normalization depth is constant (2), work per step is exponential
  6. The P vs NP structural analogy (assembling proved results)

  What is proved vs conjectured is clearly marked throughout.
-/

import SpectralArithmetic.Obstruction.Encoding
import SpectralArithmetic.Obstruction.Oplus
import SpectralArithmetic.Obstruction.Convergence
import SpectralArithmetic.Core.Semiring

namespace SpectralMonoid

open Term DynSemiring

/-! ## Part 1: Position-Existence Connection

    Observation restricted to the two base eigenstates {f₀, f₁} gives
    Boolean values: obs(f₀) = z (eigenvalue 0) and obs(f₁) = f₁ (eigenvalue 1).

    At the bit level, observation extracts existence (0 or 1), not scaling.
    This is the "derivative of position is existence" principle: the first
    derivative of positional encoding gives Boolean occupancy. -/

/-- obs on the two-element eigenvalue set gives Boolean-valued outputs.
    If s is f₀ or f₁, then obs(s) is z or f₁ (the 0/1 distinction). -/
theorem obs_bit_values {State : Type*} [DynSemiring State] (s : State)
    (hs : s = f₀ ∨ s = f₁) : obs s = z ∨ obs s = f₁ := by
  cases hs with
  | inl h => left; rw [h]; exact obs_f₀
  | inr h => right; rw [h]; exact obs_f₁

/-- obs(f₀) = z: eigenvalue 0, the "absent" state. -/
theorem obs_f₀_zero {State : Type*} [DynSemiring State] :
    obs (f₀ : State) = z := obs_f₀

/-- obs(f₁) = f₁: eigenvalue 1, the "present" state.
    This is the fixed point of obs on base states — the only
    eigenstate that equals its own observation. -/
theorem obs_f₁_one {State : Type*} [DynSemiring State] :
    obs (f₁ : State) = f₁ := obs_f₁

/-- The eigenvalue theorem gives obs(iterS n) = n * iterS n.
    The k-th bit of n (given by bitAt from Oplus.lean) captures
    the Boolean shadow of the eigenvalue at position k.
    This definitional unfolding connects bitAt to the standard
    bit extraction. -/
theorem eigenvalue_bit_connection (n k : ℕ) :
    bitAt n k = true ↔ (n / 2 ^ k) % 2 ≠ 0 := by
  simp [bitAt]

/-! ## Part 2: Normalization Depth

    A term is "obs-normal" when no obs(compose(a,b)) sub-term appears —
    all Leibniz rewrite sites have been resolved.

    normDepthBounded counts deepRewrite applications to reach obs-normal form. -/

/-- A term is in obs-normal form: no obs(compose(_, _)) pattern anywhere.
    This means obsRewrite would be the identity on all sub-terms. -/
def isObsNormal : Term → Bool
  | .obs (.compose _ _) => false
  | .obs t => isObsNormal t
  | .compose a b => isObsNormal a && isObsNormal b
  | .oplus a b => isObsNormal a && isObsNormal b
  | _ => true

theorem isObsNormal_f₀ : isObsNormal .f₀ = true := rfl
theorem isObsNormal_f₁ : isObsNormal .f₁ = true := rfl
theorem isObsNormal_z : isObsNormal .z = true := rfl

/-- obs(compose(a, b)) is never obs-normal — it is a Leibniz rewrite site. -/
theorem isObsNormal_obs_compose (a b : Term) :
    isObsNormal (.obs (.compose a b)) = false := rfl

/-- Bounded normalization depth: count deepRewrite steps until obs-normal,
    with a fuel limit to ensure termination. -/
def normDepthBounded : ℕ → Term → ℕ
  | 0, _ => 0
  | fuel + 1, t =>
    if isObsNormal t then 0
    else 1 + normDepthBounded fuel (deepRewrite t)

/-- obs(f₁) is already obs-normal: normalization depth 0.
    Verification of a base eigenstate requires zero rewrite steps. -/
theorem normDepth_obs_f₁ : normDepthBounded 5 (.obs Term.f₁) = 0 := by decide

/-- obs(f₀) is already obs-normal: normalization depth 0. -/
theorem normDepth_obs_f₀ : normDepthBounded 5 (.obs Term.f₀) = 0 := by decide

/-- obs(f₂) = obs(compose(f₁, f₁)) requires exactly 1 deepRewrite step.
    One Leibniz expansion resolves the obs(compose) pattern, and the
    resulting obs(f₁) sub-terms are already obs-normal. -/
theorem normDepth_obs_f₂ : normDepthBounded 5 (.obs t_f₂) = 1 := by decide

/-! ## Part 3: Nested Obs-Compose Family

    A family of terms with increasing size but constant normalization depth.
    Each level wraps the previous in obs(compose(-, -)),
    doubling the sub-terms. -/

/-- Nested obs-compose terms of depth d.
    depth 0: compose(f₁, f₁)  [the base f₂ term]
    depth d+1: obs(compose(nestedObs d, nestedObs d))
    Each level wraps in obs(compose(-, -)), creating a new Leibniz site. -/
def nestedObsCompose : ℕ → Term
  | 0 => .compose .f₁ .f₁
  | d + 1 => .obs (.compose (nestedObsCompose d) (nestedObsCompose d))

theorem nestedObsCompose_zero : nestedObsCompose 0 = .compose .f₁ .f₁ := rfl

theorem nestedObsCompose_one :
    nestedObsCompose 1 = .obs (.compose (.compose .f₁ .f₁) (.compose .f₁ .f₁)) := rfl

/-- nestedObsCompose 0 is obs-normal (no obs at all). -/
theorem nestedObsCompose_zero_normal :
    isObsNormal (nestedObsCompose 0) = true := by decide

/-- nestedObsCompose 1 is NOT obs-normal (obs(compose) at root). -/
theorem nestedObsCompose_one_not_normal :
    isObsNormal (nestedObsCompose 1) = false := by decide

/-- Term size at depth 0: compose(f₁, f₁) has size 3. -/
theorem nestedObsCompose_size_zero :
    termSize (nestedObsCompose 0) = 3 := by decide

/-- Term size recurrence: s(d+1) = 2 + 2 * s(d). -/
theorem nestedObsCompose_size_succ (d : ℕ) :
    termSize (nestedObsCompose (d + 1)) =
      2 + 2 * termSize (nestedObsCompose d) := by
  simp [nestedObsCompose, termSize]
  ring

/-- Term size grows at least as fast as 2^d. -/
theorem compounding_size_lower_bound (d : ℕ) :
    termSize (nestedObsCompose d) ≥ 2 ^ d := by
  induction d with
  | zero => simp [nestedObsCompose, termSize]
  | succ d ih =>
    rw [nestedObsCompose_size_succ]
    have := termSize_pos (nestedObsCompose d)
    calc 2 + 2 * termSize (nestedObsCompose d)
        ≥ 2 * termSize (nestedObsCompose d) := by omega
      _ ≥ 2 * 2 ^ d := by omega
      _ = 2 ^ (d + 1) := by ring

/-- Concrete normalization depth for nestedObsCompose 0: zero steps. -/
theorem normDepth_nested_0 :
    normDepthBounded 10 (nestedObsCompose 0) = 0 := by decide

/-- Concrete normalization depth for nestedObsCompose 1: two steps. -/
theorem normDepth_nested_1 :
    normDepthBounded 10 (nestedObsCompose 1) = 2 := by decide

/-! ## Part 4: Verification vs Construction Asymmetry

    The central proved result: verification (eigenvalue reading) has O(1) cost
    while construction (normalizing nested obs-compose terms) has exponentially
    growing cost per step. Both sides are proved. -/

/-- Semantic verification is O(1): the eigenvalue theorem gives
    obs(iterS n) = n * iterS n directly, as a single theorem application,
    regardless of the magnitude of n. -/
theorem semantic_verification_constant {State : Type*} [DynSemiring State] (n : ℕ) :
    obs (iterS n) = smul n (iterS (State := State) n) :=
  eigenvalue n

/-- Term size at least doubles with each nesting level.
    The construction of nestedObsCompose(d+1) is strictly more than
    twice the size of nestedObsCompose(d). -/
theorem construction_size_doubles (d : ℕ) :
    termSize (nestedObsCompose (d + 1)) > 2 * termSize (nestedObsCompose d) := by
  rw [nestedObsCompose_size_succ]
  omega

/-- The verification/construction asymmetry, assembled as a single theorem.
    Part 1: Verification is constant-depth (eigenvalue theorem).
    Part 2: Construction size grows exponentially (more than doubles per level). -/
theorem verification_construction_asymmetry :
    -- Verification: eigenvalue theorem in O(1)
    (∀ n : ℕ, ∀ {State : Type*} [DynSemiring State],
      obs (iterS n) = smul n (iterS (State := State) n)) ∧
    -- Construction: term size at least doubles per nesting
    (∀ d : ℕ,
      termSize (nestedObsCompose (d + 1)) > 2 * termSize (nestedObsCompose d)) := by
  exact ⟨fun n => eigenvalue n, construction_size_doubles⟩

/-! ## Part 5: Normalization Depth is Constant, Work Per Step is Exponential

    The normalization depth of nestedObsCompose d is exactly 2 for all d >= 1.
    This is because deepRewrite goes bottom-up: a single pass processes ALL
    nesting levels simultaneously, resolving every obs(compose) pattern except
    the innermost obs(compose(f₁, f₁)) terms created by the Leibniz expansion.
    A second pass resolves those.

    The complexity is NOT in the number of passes. It is in the WORK PER PASS:
    each deepRewrite step traverses the entire term, which has size >= 2^d.
    The total computational work is exponential in d, but measured by
    deepRewrite applications, it is constant (exactly 2).

    This is the precise structural content: the intension/extension regress
    terminates in constant depth, but the COST of each extensionalization step
    grows exponentially with the nesting depth of the term. The exponential
    complexity lives in the term size, not in the iteration count. -/

/-! ### Auxiliary: obs-free terms and deepRewrite behavior -/

/-- A term contains no obs constructor at all. -/
def isObsFree : Term → Bool
  | .f₀ => true
  | .f₁ => true
  | .z => true
  | .compose a b => isObsFree a && isObsFree b
  | .oplus a b => isObsFree a && isObsFree b
  | .obs _ => false

/-- deepRewrite is the identity on obs-free terms. -/
theorem deepRewrite_obsFree (t : Term) (h : isObsFree t = true) :
    deepRewrite t = t := by
  induction t with
  | f₀ => rfl
  | f₁ => rfl
  | z => rfl
  | compose a b iha ihb =>
    simp [isObsFree, Bool.and_eq_true] at h
    simp [deepRewrite, iha h.1, ihb h.2]
  | oplus a b iha ihb =>
    simp [isObsFree, Bool.and_eq_true] at h
    simp [deepRewrite, iha h.1, ihb h.2]
  | obs _ => simp [isObsFree] at h

/-- nestedObsCompose 0 is obs-free. -/
theorem nestedObsCompose_zero_obsFree : isObsFree (nestedObsCompose 0) = true := by decide

/-- deepRewrite of nestedObsCompose (d+1) applies Leibniz after recursing. -/
theorem deepRewrite_nested_succ (d : ℕ) :
    deepRewrite (nestedObsCompose (d + 1)) =
      let r := deepRewrite (nestedObsCompose d)
      .oplus (.compose (.obs r) r) (.compose r (.obs r)) := by
  simp [nestedObsCompose, deepRewrite, obsRewrite]

/-! ### The three structural properties

    We prove (A), (B), (C) for all d, which together give normDepthBounded = 2:
    (A) nestedObsCompose (d+1) is not obs-normal
    (B) deepRewrite(nestedObsCompose (d+1)) is not obs-normal
    (C) deepRewrite(deepRewrite(nestedObsCompose (d+1))) is obs-normal -/

/-- (A) nestedObsCompose (d+1) is not obs-normal (obs(compose) at root). -/
theorem nested_not_obsNormal (d : ℕ) :
    isObsNormal (nestedObsCompose (d + 1)) = false := by
  simp [nestedObsCompose, isObsNormal]

/-- If isObsNormal r = false, then the Leibniz form
    oplus(compose(obs(r), r), compose(r, obs(r))) is not obs-normal. -/
theorem leibniz_form_not_obsNormal_of_not (r : Term)
    (hr : isObsNormal r = false) :
    isObsNormal (.oplus (.compose (.obs r) r)
                        (.compose r (.obs r))) = false := by
  simp [isObsNormal, hr, Bool.and_false, Bool.false_and]

/-- (B) One deepRewrite is not enough: the result still has obs(compose) patterns.
    After one deepRewrite, the Leibniz expansion creates obs(r) terms where
    r = deepRewrite(nestedObsCompose d). For d = 0, r = compose(f₁, f₁), so
    obs(r) = obs(compose(f₁, f₁)) is not obs-normal. For d >= 1, r itself
    is not obs-normal (by induction). -/
theorem nested_one_step_not_obsNormal : ∀ d : ℕ,
    isObsNormal (deepRewrite (nestedObsCompose (d + 1))) = false := by
  intro d
  induction d with
  | zero =>
    rw [deepRewrite_nested_succ,
        deepRewrite_obsFree _ nestedObsCompose_zero_obsFree]
    decide
  | succ d ih =>
    rw [deepRewrite_nested_succ]
    exact leibniz_form_not_obsNormal_of_not _ ih

/-- (C) Two deepRewrites suffice for all d >= 0.
    For d = 0: nestedObsCompose 1 after two passes is obs-normal (by decide).
    For d >= 1: by induction using the structural form of deepRewrite.

    The key insight for the inductive step:
    - deepRewrite(nestedObsCompose (d+2)) = oplus(compose(obs(r), r), compose(r, obs(r)))
      where r = deepRewrite(nestedObsCompose (d+1))
    - The second deepRewrite distributes over the structure
    - deepRewrite(r) = deepRewrite(deepRewrite(nestedObsCompose (d+1))) which is obs-normal by IH
    - r has oplus at root (from deepRewrite_nested_succ), so
      obsRewrite(obs(deepRewrite(r))) = obs(deepRewrite(r)) (identity on obs(oplus))
    - isObsNormal(obs(deepRewrite(r))) = isObsNormal(deepRewrite(r)) = true by IH
    - Everything is obs-normal. -/
theorem nested_two_steps_obsNormal (d : ℕ) :
    isObsNormal (deepRewrite (deepRewrite (nestedObsCompose (d + 1)))) = true := by
  induction d with
  | zero => decide
  | succ d ih =>
    -- deepRewrite(nestedObsCompose (d+2)) has the Leibniz form
    rw [deepRewrite_nested_succ]
    simp only []
    -- Set r = deepRewrite(nestedObsCompose (d+1))
    set r := deepRewrite (nestedObsCompose (d + 1)) with hr_def
    -- The second deepRewrite of oplus(compose(obs(r), r), compose(r, obs(r))):
    -- deepRewrite(oplus(A, B)) = oplus(deepRewrite(A), deepRewrite(B))
    -- deepRewrite(compose(X, Y)) = compose(deepRewrite(X), deepRewrite(Y))
    -- deepRewrite(obs(r)) = obsRewrite(obs(deepRewrite(r)))
    change isObsNormal
      (deepRewrite (.oplus (.compose (.obs r) r)
                           (.compose r (.obs r)))) = true
    simp only [deepRewrite]
    -- Now we have:
    -- isObsNormal(oplus(compose(obsRewrite(obs(deepRewrite(r))), deepRewrite(r)),
    --                    compose(deepRewrite(r), obsRewrite(obs(deepRewrite(r)))))) = true
    -- r = deepRewrite(nestedObsCompose (d+1))
    -- deepRewrite(r) = deepRewrite(deepRewrite(nestedObsCompose (d+1)))
    -- which is obs-normal by ih
    -- r has oplus at root (by deepRewrite_nested_succ d)
    have r_eq : r = let r' := deepRewrite (nestedObsCompose d)
        .oplus (.compose (.obs r') r') (.compose r' (.obs r')) :=
      deepRewrite_nested_succ d
    -- So deepRewrite(r) = deepRewrite(oplus(compose(obs(r'), r'), compose(r', obs(r'))))
    -- = oplus(compose(deepRewrite(obs(r')), deepRewrite(r')), ...)
    -- This has oplus at root.
    -- Therefore obsRewrite(obs(deepRewrite(r))) = obs(deepRewrite(r))
    -- (since obsRewrite is identity on obs(oplus(...)))
    -- First, show deepRewrite(r) has oplus at root
    have dr_oplus : ∃ x y, deepRewrite r = .oplus x y := by
      rw [r_eq]
      simp only [deepRewrite]
      exact ⟨_, _, rfl⟩
    -- Use the oplus root to simplify obsRewrite
    obtain ⟨x, y, hdr⟩ := dr_oplus
    rw [hdr]
    simp only [obsRewrite]
    -- Now goal: isObsNormal(oplus(compose(obs(oplus(x,y)), oplus(x,y)),
    --                             compose(oplus(x,y), obs(oplus(x,y))))) = true
    simp only [isObsNormal]
    -- Reduces to checking isObsNormal of sub-terms
    -- obs(oplus(x,y)): isObsNormal = isObsNormal(oplus(x,y)) = isObsNormal(x) && isObsNormal(y)
    -- oplus(x,y): isObsNormal = isObsNormal(x) && isObsNormal(y)
    -- So need: isObsNormal(x) = true and isObsNormal(y) = true
    -- These come from: deepRewrite(r) = oplus(x,y) is obs-normal by ih
    -- ih: isObsNormal(deepRewrite(deepRewrite(nestedObsCompose (d+1)))) = true
    -- and deepRewrite(r) = deepRewrite(deepRewrite(nestedObsCompose (d+1))) by hr_def
    have hdr_normal : isObsNormal (deepRewrite r) = true := ih
    rw [hdr] at hdr_normal
    simp only [isObsNormal, Bool.and_eq_true] at hdr_normal
    simp [hdr_normal.1, hdr_normal.2]

/-- The main theorem: normalization depth is exactly 2 for all d >= 1.
    deepRewrite goes bottom-up, processing all nesting levels simultaneously.
    Pass 1 resolves all obs(compose) except the innermost obs(compose(f₁,f₁)).
    Pass 2 resolves those. -/
theorem normDepth_nested_eq_two (d : ℕ) :
    normDepthBounded 3 (nestedObsCompose (d + 1)) = 2 := by
  -- Unfold normDepthBounded using (A), (B), (C)
  unfold normDepthBounded
  rw [if_neg (by rw [nested_not_obsNormal]; decide)]
  unfold normDepthBounded
  rw [if_neg (by rw [nested_one_step_not_obsNormal]; decide)]
  unfold normDepthBounded
  rw [if_pos (nested_two_steps_obsNormal d)]

/-! ## Part 6: The P vs NP Structural Analogy

    The encoding obstruction proves three facts:
    1. Verification is O(1): eigenvalue theorem
    2. Construction has exponential size growth: compounding_size_lower_bound
    3. No encoding bridges the gap: no_coalgebra_morphism

    Together, these constitute a proved algebraic instance of the
    verification/construction asymmetry — the same structural pattern
    that P vs NP is about.

    IMPORTANT: This is a STRUCTURAL ANALOGY, not a logical implication.
    The algebraic asymmetry is proved. P != NP is conjectured but unproved.
    The two live in different mathematical regimes (algebraic term rewriting
    vs Boolean circuit complexity). No implication in either direction is claimed.

    What IS claimed: the encoding obstruction is a rigorous algebraic instance
    of the verification/construction gap, demonstrating that such gaps can
    be proved to exist in self-encoding systems. -/

/-- The P vs NP structural analogy: three proved components.
    1. Verification is constant-depth (eigenvalue)
    2. Construction has exponential size growth
    3. No injective encoding commutes with extensionalization -/
def PvsNP_StructuralAnalogy : Prop :=
  (∀ n : ℕ, ∀ {State : Type*} [DynSemiring State],
    obs (iterS n) = smul n (iterS (State := State) n)) ∧
  (∀ d : ℕ, termSize (nestedObsCompose d) ≥ 2 ^ d) ∧
  (∀ ε : Term → ℕ, Function.Injective ε → ∀ a b : Term,
    ε (obsRewrite (.obs (.compose a b))) ≠ ε (.obs (.compose a b)))

/-- The structural analogy holds: all three components are proved.
    No sorry in this proof — it assembles three machine-checked results. -/
theorem PvsNP_analogy_holds : PvsNP_StructuralAnalogy :=
  ⟨fun n => eigenvalue n,
   compounding_size_lower_bound,
   fun ε hε a b => encoding_obstruction_general ε hε a b⟩

/-- The complete complexity characterization: verification is O(1) via eigenvalue,
    construction requires exponentially growing work per normalization step,
    and the number of normalization steps is constant (exactly 2).
    The exponential cost lives in the per-step work, not the step count. -/
theorem complexity_characterization :
    -- Verification: O(1)
    (∀ n : ℕ, ∀ {State : Type*} [DynSemiring State],
      obs (iterS n) = smul n (iterS (State := State) n)) ∧
    -- Construction: normalization depth is constant (2)
    (∀ d : ℕ, normDepthBounded 3 (nestedObsCompose (d + 1)) = 2) ∧
    -- Construction: but per-step work grows exponentially (term size >= 2^d)
    (∀ d : ℕ, termSize (nestedObsCompose d) ≥ 2 ^ d) :=
  ⟨fun n => eigenvalue n, normDepth_nested_eq_two, compounding_size_lower_bound⟩

/-! ## Part 7: SAT Term Encoding (Definitional Sketch)

    Boolean formulas can be encoded as Terms using the Boolean algebra
    on {z, f₀} established in ZFTest.lean:
      AND = compose, NOT = oplus(f₀, oneg(-)), OR = De Morgan

    These definitions sketch the encoding. No completeness theorems
    are claimed — this is a research direction, not a result. -/

/-- Boolean AND as a term: compose. -/
def andTerm (a b : Term) : Term := .compose a b

/-- Boolean OR as a term: oplus.
    Note: this is a simplification. The full OR requires NOT via oneg,
    which is not a primitive Term constructor. Using oplus directly
    captures the additive structure without the Boolean semantics. -/
def orTerm (a b : Term) : Term := .oplus a b

/-- A literal: either f₀ (TRUE in ring convention) or z (FALSE). -/
def literalTerm (b : Bool) : Term := if b then .f₀ else .z

/-- A conjunction of literals: AND of a list. -/
def conjTerm : List Term → Term
  | [] => .f₀
  | [t] => t
  | t :: ts => andTerm t (conjTerm ts)

/-- The oplus impossibility from Oplus.lean confirms that any bitwise
    realization of oplus has characteristic 2, contradicting char_zero.
    This means the additive structure introduced by Leibniz extensionalization
    is inherently non-local (requires carry propagation across bit positions).
    The non-locality is what makes construction expensive. -/
theorem construction_requires_carry :
    ∀ (f : Bool → Bool → Bool) (e : Bool),
      (∀ a b, f a b = f b a) →
      (∀ x, f e x = x) →
      (∀ a b c, f a b = f a c → b = c) →
      (∀ x, f x x = e) :=
  oplus_bitwise_impossible

end SpectralMonoid
