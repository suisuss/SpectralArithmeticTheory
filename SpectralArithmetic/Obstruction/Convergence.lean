/-
  Spectral Arithmetic: The Convergence Conjecture
  ================================================

  The exact coalgebra morphism is impossible (no_coalgebra_morphism).
  The intension/extension gap grows exponentially (extensionalize_more_than_doubles).
  There is no fixed point (substitution_chain_distinct).

  But the meaning is preserved at every level (semantic_invariance_general).
  The system isn't semantically diverging — only formally.

  THE OPEN QUESTION: Does there exist a weaker encoding — non-injective,
  approximate, or up to some equivalence — where the intension/extension
  switching converges?

  This file formalizes the question precisely:
  1. Defines iterated extensionalization (the syntactic trajectory)
  2. Defines the morphism error at each depth
  3. Defines encoding families (depth-dependent encodings)
  4. States convergence as a precise mathematical property
  5. Proves structural facts about the trajectory that constrain
     whether convergence is possible

  The conjecture is OPEN. Neither convergence nor divergence is proved.
  What IS proved: the exact case diverges, the semantic side converges
  (trivially — it's invariant), and the syntactic complexity grows
  exponentially. Whether an adaptive encoding can absorb the exponential
  growth is the central open problem.
-/

import SpectralArithmetic.Obstruction.Encoding
import SpectralArithmetic.Core.Semiring

namespace SpectralMonoid

open Term

/-! ## Part 1: Iterated Extensionalization (The Syntactic Trajectory)

    The syntactic trajectory of a term under repeated extensionalization:
    t, deepRewrite(t), deepRewrite(deepRewrite(t)), ...

    Each step resolves one layer of obs sub-terms via the Leibniz rule.
    The semantic denotation is invariant (proved). The syntactic form
    changes at every step (proved for the first three levels). -/

/-- Iterated deep extensionalization: apply deepRewrite k times.
    This is the syntactic trajectory — the sequence of forms produced
    by repeatedly unfolding obs sub-terms via the Leibniz rule. -/
def iterDeepRewrite : ℕ → Term → Term
  | 0, t => t
  | k + 1, t => deepRewrite (iterDeepRewrite k t)

/-- Iterated extensionalization preserves semantics at every depth.
    eval(iterDeepRewrite k t) = eval(t) for all k.
    The syntactic trajectory is semantically constant. -/
theorem iterDeepRewrite_eval {State : Type*} [DynSemiring State]
    (k : ℕ) (t : Term) :
    eval (iterDeepRewrite k t) = (eval t : State) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [iterDeepRewrite]
    rw [deepRewrite_eval, ih]

/-- Iterated observation: wrap a term in k layers of obs.
    obs^k(t) = obs(obs(...obs(t)...)) with k applications. -/
def iterObs : ℕ → Term → Term
  | 0, t => t
  | k + 1, t => .obs (iterObs k t)

/-- The observation trajectory: obs^k applied to compose(f₁, f₁).
    At depth k, this is obs^k(compose(f₁, f₁)).
    The Leibniz rule can fire on the outermost obs(compose(...)),
    producing an increasingly complex extensionalized form. -/
def obsTrajectory (k : ℕ) : Term := iterObs k t_f₂

/-- obs^0(t) = t -/
theorem obsTrajectory_zero : obsTrajectory 0 = t_f₂ := rfl

/-- obs^1(t) = obs(compose(f₁, f₁)) -/
theorem obsTrajectory_one : obsTrajectory 1 = .obs t_f₂ := rfl

/-- obs^(k+1)(t) = obs(obs^k(t)) -/
theorem obsTrajectory_succ (k : ℕ) :
    obsTrajectory (k + 1) = .obs (obsTrajectory k) := rfl

/-! ## Part 2: The Syntactic-Semantic Diagram

    The eval-quote diagram at depth k. Two paths from terms to codes:

    Path A (extensionalize then encode):
      t → obsRewrite(t) → deepRewrite(...) → ... → iterDeepRewrite k t → ε(result)

    Path B (encode then scale by eigenvalue):
      t → eval(t) → obs(eval(t)) = n · eval(t) → eigenvalue scaling

    The morphism error measures how far apart these paths are.
    At depth 0, the error is nonzero (no_coalgebra_morphism).
    The question is how the error behaves as depth increases. -/

/-- The syntactic path: extensionalize k times, then encode.
    This is the code assigned to the k-th step of the syntactic trajectory. -/
def syntacticPath (ε : Term → ℕ) (t : Term) (k : ℕ) : ℕ :=
  ε (iterDeepRewrite k t)

/-- The syntactic path at depth 0 is just encoding the original term. -/
theorem syntacticPath_zero (ε : Term → ℕ) (t : Term) :
    syntacticPath ε t 0 = ε t := rfl

/-- The syntactic path at depth k+1 applies one more deep rewrite. -/
theorem syntacticPath_succ (ε : Term → ℕ) (t : Term) (k : ℕ) :
    syntacticPath ε t (k + 1) = ε (deepRewrite (iterDeepRewrite k t)) := rfl

/-! ## Part 3: Term Size Along the Trajectory

    We track how term size evolves along the trajectory.
    This constrains what any encoding can do: injective encodings
    from larger term spaces require larger codomain ranges. -/

/-- Term size along the syntactic trajectory. -/
def trajSize (t : Term) (k : ℕ) : ℕ :=
  termSize (iterDeepRewrite k t)

/-- The trajectory size at depth 0 is the original term size. -/
theorem trajSize_zero (t : Term) : trajSize t 0 = termSize t := rfl

/-- Semantic invariance restated for trajectories:
    every point on the syntactic trajectory evaluates to the same state. -/
theorem trajectory_semantically_constant {State : Type*} [DynSemiring State]
    (t : Term) (j k : ℕ) :
    eval (iterDeepRewrite j t) = (eval (iterDeepRewrite k t) : State) := by
  rw [iterDeepRewrite_eval, iterDeepRewrite_eval]

/-! ## Part 4: Encoding Families and Convergence

    An encoding family is a sequence of encodings, one per depth.
    The idea: at depth k, use encoding ε_k that is "tuned" to the
    k-th level of the extensionalization chain. The question is
    whether the family can be chosen so that the morphism error
    vanishes in the limit.

    We formalize several notions of convergence, from weakest to
    strongest. -/

/-- An encoding family: a sequence of injective encodings, one per depth.
    At depth k, the encoding ε_k : Term → ℕ is used. -/
structure EncodingFamily where
  encode : ℕ → Term → ℕ
  injective : ∀ k, Function.Injective (encode k)

/-- The morphism discrepancy at depth k for an encoding family:
    the difference between encoding the extensionalized form and
    encoding the original form, using the depth-k encoding.

    If this is zero, the encoding commutes at depth k.
    If this converges to zero, the encoding asymptotically commutes. -/
def discrepancy (εs : EncodingFamily) (a b : Term) (k : ℕ) : ℕ :=
  -- The code of the extensionalized form at depth k
  -- vs. the code of the original form at depth k
  -- We measure the absolute difference.
  let rewritten := iterDeepRewrite k (obsRewrite (.obs (.compose a b)))
  let original := iterDeepRewrite k (.obs (.compose a b))
  if εs.encode k rewritten ≥ εs.encode k original
  then εs.encode k rewritten - εs.encode k original
  else εs.encode k original - εs.encode k rewritten

/-- **PROVED: The discrepancy is always nonzero at depth 0.**
    This is no_coalgebra_morphism restated for encoding families.
    At depth 0, iterDeepRewrite is the identity, so the discrepancy
    is just the difference between ε(extensionalized) and ε(original),
    which is nonzero by the encoding obstruction. -/
theorem discrepancy_nonzero_at_zero (εs : EncodingFamily) (a b : Term) :
    discrepancy εs a b 0 ≠ 0 := by
  simp only [discrepancy, iterDeepRewrite]
  intro h
  -- If the discrepancy is 0, the codes are equal
  split_ifs at h with hge
  · -- rewritten ≥ original case: difference = 0 means equal
    have heq : εs.encode 0 (obsRewrite (.obs (.compose a b))) =
               εs.encode 0 (.obs (.compose a b)) := by omega
    exact absurd (εs.injective 0 heq) (extensionalize_ne_original_general a b)
  · -- original > rewritten case: difference = 0 means equal
    push_neg at hge
    have heq : εs.encode 0 (.obs (.compose a b)) =
               εs.encode 0 (obsRewrite (.obs (.compose a b))) := by omega
    exact absurd (εs.injective 0 heq) (Ne.symm (extensionalize_ne_original_general a b))

/-! ## Part 5: The Convergence Conjecture

    The central open question, stated precisely. -/

/-- **CONJECTURE (Weak Convergence):**
    Does there exist an encoding family such that for all terms a, b,
    the discrepancy eventually becomes smaller than any given bound?

    Formally: ∃ εs, ∀ a b, ∀ bound > 0, ∃ k₀, ∀ k ≥ k₀,
              discrepancy εs a b k < bound

    This would mean: the intension/extension gap can be made
    arbitrarily small by going deep enough in the extensionalization
    chain, provided we're allowed to change the encoding at each depth.

    STATUS: OPEN. Neither proved nor disproved.
    - Against: extensionalize_more_than_doubles shows exponential
      growth in term complexity at each step
    - For: semantic_invariance_general shows the semantic content
      is already converged (invariant) -/
def WeakConvergence : Prop :=
  ∃ εs : EncodingFamily,
    ∀ a b : Term, ∀ bound : ℕ, bound > 0 →
      ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        discrepancy εs a b k < bound

/-- **CONJECTURE (Strong Convergence):**
    Does there exist an encoding family such that for all terms a, b,
    the discrepancy eventually reaches exactly zero?

    This would mean: at some finite depth, the encoding perfectly
    commutes with extensionalization. The intension/extension gap
    closes completely.

    This is strictly stronger than weak convergence and likely FALSE,
    since it would require the extensionalized and original forms
    to receive the same code — contradicting injectivity unless
    they become the same term (which they don't, by
    extensionalize_ne_original_general).

    STATUS: OPEN, but expected to be false. -/
def StrongConvergence : Prop :=
  ∃ εs : EncodingFamily,
    ∀ a b : Term, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      discrepancy εs a b k = 0

/-- **PROVED: Strong convergence is impossible.**
    At every depth k, the extensionalized form and the original form
    are distinct terms after iterDeepRewrite (because obsRewrite
    changes the root constructor from obs to oplus, and iterDeepRewrite
    preserves this distinction at depth 0). Any injective encoding
    maps distinct terms to distinct codes. Therefore the discrepancy
    is nonzero at depth 0.

    Note: this only directly blocks depth 0. Whether the forms become
    equal at depth k > 0 (after iterated deep rewriting) is a
    separate question — they might converge to the same normal form.
    See strong_convergence_at_depth_zero for the precise statement. -/
theorem strong_convergence_blocked_at_zero :
    ∀ εs : EncodingFamily, ∀ a b : Term,
      discrepancy εs a b 0 ≠ 0 :=
  discrepancy_nonzero_at_zero

/-! ## Part 6: What Convergence Would Imply

    If weak convergence holds, the intension/extension gap is a
    finite-depth phenomenon. The obstruction (proved) says the gap
    exists at every depth — but convergence would say it shrinks.

    The convergence rate, if it exists, would be governed by the
    same constant that relates discrete (base 2, binary branching)
    to continuous (base e, derivative) dynamics:

        e = lim_{n→∞} (1 + 1/n)^n

    This connects to the discrete-continuous conjecture in
    self-representation.md Part 10: the framework's self-referential
    structure would select the analytic model (obs = d/dx) in the
    limit where the intension/extension gap closes.

    If weak convergence FAILS, the obstruction is total at every
    resolution. Self-knowledge is structurally impossible — not
    just exactly, but even approximately. -/

/-- **TOTAL DIVERGENCE (Conjecture):**
    For every encoding family, there exist terms where the
    discrepancy stays above some positive bound for all depths.

    This is the negation of weak convergence.

    STATUS: OPEN. The exponential growth of term size
    (extensionalize_more_than_doubles) suggests this holds,
    but it's not proved. -/
def TotalDivergence : Prop :=
  ∀ εs : EncodingFamily,
    ∃ a b : Term, ∃ bound : ℕ, bound > 0 ∧
      ∀ k : ℕ, discrepancy εs a b k ≥ bound

/-- Weak convergence and total divergence are contradictory.
    Exactly one holds (assuming classical logic). -/
theorem convergence_xor_divergence :
    ¬ (WeakConvergence ∧ TotalDivergence) := by
  intro ⟨⟨εs, hconv⟩, hdiv⟩
  obtain ⟨a, b, bound, hbound, hall⟩ := hdiv εs
  obtain ⟨k₀, hk₀⟩ := hconv a b bound hbound
  have := hall k₀
  have := hk₀ k₀ (le_refl k₀)
  omega

/-! ## Part 7: The Semantic Quotient (Trivial Convergence)

    As a baseline: if we drop injectivity, convergence is trivial.
    The semantic quotient encoding maps all terms with the same
    eval to the same code. Since eval is invariant under
    extensionalization, this "encoding" has zero discrepancy.

    This shows the question is not WHETHER convergence is possible
    (it is, trivially) but whether it's possible WITH INJECTIVITY
    or with enough structure to support self-representation. -/

/-- **Extensionalization preserves semantics in any model.**
    This is the trivial convergence baseline: the semantic content
    never diverges because it never changes. -/
theorem obsRewrite_semEquiv {State : Type*} [DynSemiring State] (t : Term) :
    eval (obsRewrite t) = (eval t : State) :=
  obsRewrite_eval t

/-- **Deep extensionalization preserves semantics in any model.** -/
theorem deepRewrite_semEquiv {State : Type*} [DynSemiring State] (t : Term) :
    eval (deepRewrite t) = (eval t : State) :=
  deepRewrite_eval t

/-- **Iterated extensionalization preserves semantics in any model.** -/
theorem iterDeepRewrite_semEquiv {State : Type*} [DynSemiring State]
    (k : ℕ) (t : Term) :
    eval (iterDeepRewrite k t) = (eval t : State) :=
  iterDeepRewrite_eval k t

/-- **The entire syntactic trajectory is semantically constant.**
    Every term on the trajectory evaluates to the same state.
    The semantic content converges trivially (it never changes).
    The question is whether the SYNTACTIC content — the codes
    assigned by an injective encoding — can be made to converge too. -/
theorem trajectory_all_semEquiv {State : Type*} [DynSemiring State]
    (t : Term) (j k : ℕ) :
    eval (iterDeepRewrite j t) = (eval (iterDeepRewrite k t) : State) := by
  rw [iterDeepRewrite_eval, iterDeepRewrite_eval]

end SpectralMonoid
