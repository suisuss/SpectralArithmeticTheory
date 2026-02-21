/-
  Spectral Arithmetic: Term Algebra and Encoding Infrastructure
  =============================================================

  Defines the free term algebra over {compose, oplus, obs, f₀, f₁, z},
  an evaluation function into any DynSemiring, and the Leibniz rewrite
  rule as an oriented term transformation.

  This is the infrastructure for the encoding obstruction theorem.
-/

import SpectralArithmetic.Core.Semiring

namespace SpectralMonoid

/-! ## The Free Term Algebra -/

/-- Terms in the framework's language. -/
inductive Term where
  | f₀ : Term
  | f₁ : Term
  | z  : Term
  | compose : Term → Term → Term
  | oplus : Term → Term → Term
  | obs : Term → Term
  deriving DecidableEq, Repr

namespace Term

/-! ## Evaluation: Terms → State -/

/-- Evaluate a term in any DynSemiring. -/
def eval {State : Type*} [DynSemiring State] : Term → State
  | .f₀ => DynSemiring.toSpectralMonoid.f₀
  | .f₁ => DynSemiring.toSpectralMonoid.f₁
  | .z  => DynSemiring.toSpectralMonoid.z
  | .compose a b => SpectralMonoid.compose (eval a) (eval b)
  | .oplus a b => DynSemiring.oplus (eval a) (eval b)
  | .obs a => SpectralMonoid.obs (eval a)

/-! ## One-step Leibniz Rewrite -/

/-- Apply the Leibniz rule as a rewrite at the top level:
    obs(compose(a, b)) → oplus(compose(obs(a), b), compose(a, obs(b)))
    obs(f₁) → f₁
    obs(f₀) → z
    obs(z)  → z
    Otherwise, return the term unchanged. -/
def obsRewrite : Term → Term
  | .obs (.compose a b) =>
      .oplus (.compose (.obs a) b) (.compose a (.obs b))
  | .obs .f₁ => .f₁
  | .obs .f₀ => .z
  | .obs .z  => .z
  | t => t

/-! ## Correctness of Rewriting -/

/-- obsRewrite preserves evaluation: eval(obsRewrite(t)) = eval(t) for all t. -/
theorem obsRewrite_eval {State : Type*} [DynSemiring State] (t : Term) :
    eval (obsRewrite t) = (eval t : State) := by
  match t with
  | .obs (.compose a b) =>
    simp only [obsRewrite, eval]
    rw [← DynSemiring.leibniz]
  | .obs .f₁ =>
    simp only [obsRewrite, eval]
    exact (DynSemiring.toSpectralMonoid.obs_f₁).symm
  | .obs .f₀ =>
    simp only [obsRewrite, eval]
    exact (DynSemiring.obs_f₀).symm
  | .obs .z =>
    simp only [obsRewrite, eval]
    exact (DynSemiring.obs_z).symm
  | .obs (.obs _) => rfl
  | .obs (.oplus _ _) => rfl
  | .f₀ => rfl
  | .f₁ => rfl
  | .z => rfl
  | .compose _ _ => rfl
  | .oplus _ _ => rfl

/-! ## Key terms for the obstruction proof -/

/-- The term compose(f₁, f₁), representing f₂ -/
def t_f₂ : Term := .compose .f₁ .f₁

/-- obs(compose(f₁, f₁)) rewrites to oplus(compose(f₁, f₁), compose(f₁, f₁)) -/
theorem obsRewrite_t_f₂ :
    obsRewrite (.obs t_f₂) =
      .oplus (.compose (.obs .f₁) .f₁) (.compose .f₁ (.obs .f₁)) := by
  rfl

/-- The Leibniz expansion of obs(f₂) contains obs(f₁) sub-terms -/
theorem obsRewrite_t_f₂_has_obs :
    obsRewrite (.obs t_f₂) =
      .oplus (.compose (.obs .f₁) .f₁) (.compose .f₁ (.obs .f₁)) := rfl

end Term

end SpectralMonoid
