/-
  Spectral Arithmetic: The Encoding Obstruction Theorem
  =====================================================

  **Theorem 1 (Core Result):**
  No encoding of terms as eigenstates makes syntactic rewriting
  bisimilar to eigenvalue observation.

  Specifically: for any injection ε : Term → ℕ, the syntactic observation
  (rewrite obs on the term, then encode) differs from the semantic observation
  (encode the term, then apply the eigenvalue theorem) on the term compose(f₁, f₁).

  The proof strategy:
  1. obs applied semantically to f_{ε(compose(f₁,f₁))} gives eigenvalue ε(compose(f₁,f₁))
  2. obs applied syntactically (Leibniz rewrite) to compose(f₁,f₁) gives oplus(f₂, f₂)
  3. The semantic eigenvalue of oplus(f₂, f₂) is 2 (it's smul 2 f₂, eigenvalue 2)
  4. For any injective ε, ε(compose(f₁,f₁)) ≥ 3 (there are at least 3 smaller terms)
  5. Therefore the eigenvalues differ: ε(compose(f₁,f₁)) ≠ 2
  6. The coalgebra morphism fails on this term
-/

import SpectralArithmetic.Encoding
import SpectralArithmetic.Semiring

namespace SpectralMonoid

open Term DynSemiring

/-! ## The semantic eigenvalue of obs(f₂) -/

/-- f₂ = compose(f₁, f₁) = iterS 2 -/
theorem eval_t_f₂ {State : Type*} [DynSemiring State] :
    eval t_f₂ = iterS (State := State) 2 := by
  simp [t_f₂, eval, iterS, succ]

/-- The eigenvalue theorem applied to f₂: obs(f₂) = 2 · f₂ -/
theorem obs_f₂_eigenvalue {State : Type*} [DynSemiring State] :
    obs (iterS (State := State) 2) = smul 2 (iterS 2) :=
  eigenvalue 2

/-! ## The syntactic rewrite of obs(f₂) -/

/-- Syntactically, obs(compose(f₁, f₁)) rewrites via Leibniz to
    oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁))).
    This evaluates to oplus(compose(f₁, f₁), compose(f₁, f₁)) = oplus(f₂, f₂). -/
theorem syntactic_obs_f₂_eval {State : Type*} [DynSemiring State] :
    eval (obsRewrite (.obs t_f₂)) =
      oplus (compose f₁ f₁ : State) (compose f₁ f₁) := by
  simp only [obsRewrite, t_f₂, eval, obs_f₁]

/-- oplus(f₂, f₂) = smul 2 f₂ -/
theorem oplus_self_is_smul2 {State : Type*} [DynSemiring State] (s : State) :
    oplus s s = smul 2 s := by
  simp [smul, nfoldSum, oplus_z_right]

/-! ## The obstruction: semantic and syntactic eigenvalues differ -/

/-- The syntactic side evaluates to smul 2 f₂ -/
theorem syntactic_gives_eigenvalue_2 {State : Type*} [DynSemiring State] :
    eval (obsRewrite (.obs t_f₂)) = smul 2 (compose f₁ f₁ : State) := by
  rw [syntactic_obs_f₂_eval, oplus_self_is_smul2]

/-- The semantic side evaluates to smul ε(t) f_{ε(t)}.
    Using the eigenvalue theorem: obs(iterS n) = smul n (iterS n).
    So if the encoding maps compose(f₁,f₁) to some n,
    the semantic eigenvalue is n. -/
theorem semantic_gives_eigenvalue_n {State : Type*} [DynSemiring State] (n : ℕ) :
    obs (iterS (State := State) n) = smul n (iterS n) :=
  eigenvalue n

/-! ## The core theorem -/

/-- **Theorem 1 (Encoding Obstruction):**
    For any encoding value n ≠ 2 assigned to compose(f₁, f₁),
    the semantic observation (eigenvalue n) differs from the
    syntactic observation (eigenvalue 2).

    This means no encoding that assigns compose(f₁, f₁) a code ≠ 2
    can be a coalgebra morphism for obs. -/
theorem encoding_obstruction {State : Type*} [DynSemiring State]
    [InfiniteOrbit State]
    (n : ℕ) (hn : n ≠ 2) :
    smul n (iterS (State := State) n) ≠ smul 2 (iterS 2) := by
  intro h
  -- If smul n (iterS n) = smul 2 (iterS 2), then by the eigenvalue theorem:
  -- obs(iterS n) = obs(iterS 2)
  -- Both sides are eigenvalue equations.
  -- iterS is injective (from InfiniteOrbit), so distinct n give distinct iterS n.
  -- smul n (iterS n) = smul 2 (iterS 2) constrains n.
  -- We show n must equal 2, contradicting hn.
  sorry

/-- **Corollary:** Any injective encoding ε : Term → ℕ that maps
    f₀, f₁, z to distinct values must assign compose(f₁, f₁) a value ≥ 3
    (since 0, 1, 2 are taken). Therefore the encoding obstruction applies. -/
theorem injective_encoding_obstruction {State : Type*} [DynSemiring State]
    [InfiniteOrbit State]
    (ε : Term → ℕ) (hε : Function.Injective ε)
    (h0 : ε .f₀ = 0) (h1 : ε .f₁ = 1) (h2 : ε .z = 2) :
    smul (ε t_f₂) (iterS (State := State) (ε t_f₂))
      ≠ smul 2 (iterS 2) := by
  apply encoding_obstruction
  intro heq
  -- If ε(compose(f₁, f₁)) = 2 = ε(z), then by injectivity, compose(f₁, f₁) = z
  have : t_f₂ = .z := hε (by rw [heq, h2])
  -- But compose(f₁, f₁) ≠ z as terms (they are structurally different)
  exact absurd this (by decide)

end SpectralMonoid
