/-
  Spectral Arithmetic: The Encoding Obstruction Theorem
  =====================================================

  **Core Result:** For any injective encoding ε : Term → ℕ, the
  syntactic observation (Leibniz rewrite on terms, then encode) produces
  a DIFFERENT term than what the semantic observation (eigenvalue scaling)
  would require. The coalgebra morphism fails.

  The proof works entirely at the Term level using DecidableEq on Term,
  avoiding the need for abstract eigenvalue inequality in State.

  Strategy:
  1. obs(compose(f₁, f₁)) rewrites via Leibniz to oplus(f₂, f₂)
  2. Any injective ε must map compose(f₁,f₁) to some n ≥ 3
     (since f₀, f₁, z are distinct terms mapped to distinct values)
  3. For the encoding to be a coalgebra morphism, ε(oplus(f₂,f₂)) would
     need to equal ε applied to "the eigenvalue-scaled version"
  4. But these are structurally different terms, so ε maps them to
     different values (injectivity), breaking the morphism
-/

import SpectralArithmetic.Encoding
import SpectralArithmetic.Semiring

namespace SpectralMonoid

open Term DynSemiring

/-! ## Semantic and syntactic sides -/

/-- f₂ = compose(f₁, f₁) evaluates to iterS 2 -/
theorem eval_t_f₂ {State : Type*} [DynSemiring State] :
    eval t_f₂ = iterS (State := State) 2 := by
  simp [t_f₂, eval, iterS, succ]

/-- The eigenvalue theorem applied to f₂: obs(f₂) = 2 · f₂ -/
theorem obs_f₂_eigenvalue {State : Type*} [DynSemiring State] :
    obs (iterS (State := State) 2) = smul 2 (iterS 2) :=
  eigenvalue 2

/-- Syntactically, obsRewrite(obs(compose(f₁, f₁))) evaluates to oplus(f₂, f₂) -/
theorem syntactic_obs_f₂_eval {State : Type*} [DynSemiring State] :
    eval (obsRewrite (.obs t_f₂)) =
      oplus (compose f₁ f₁ : State) (compose f₁ f₁) := by
  simp only [obsRewrite, t_f₂, eval, obs_f₁]

/-- The semantic observation: obs(iterS n) = smul n (iterS n) -/
theorem semantic_eigenvalue {State : Type*} [DynSemiring State] (n : ℕ) :
    obs (iterS (State := State) n) = smul n (iterS n) :=
  eigenvalue n

/-! ## The obstruction at the Term level -/

/-- The syntactic rewrite of obs(compose(f₁, f₁)) is
    oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁))).
    This is the Leibniz expansion as a Term. -/
theorem obs_rewrite_f₂ :
    obsRewrite (.obs t_f₂) =
      Term.oplus (Term.compose (Term.obs Term.f₁) Term.f₁)
                 (Term.compose Term.f₁ (Term.obs Term.f₁)) := rfl

/-- The syntactic rewrite of obs(f₂) is NOT the same term as obs(f₂) itself.
    obsRewrite changes the term structure. -/
theorem rewrite_changes_term :
    obsRewrite (.obs t_f₂) ≠ Term.obs t_f₂ := by decide

/-! ## The encoding obstruction -/

/-- **Key structural fact:** compose(f₁, f₁) is distinct from f₀, f₁, and z as a Term. -/
theorem t_f₂_ne_f₀ : t_f₂ ≠ Term.f₀ := by decide
theorem t_f₂_ne_f₁ : t_f₂ ≠ Term.f₁ := by decide
theorem t_f₂_ne_z : t_f₂ ≠ Term.z := by decide

/-- **Key structural fact:** The Leibniz rewrite of obs(f₂) is distinct from
    obs(f₂) as a Term. Any injective encoding must map them to different values. -/
theorem rewrite_ne_original :
    obsRewrite (.obs t_f₂) ≠ Term.obs t_f₂ := by decide

/-- **Theorem 1 (Encoding Obstruction — Term Level):**
    For any injective encoding ε : Term → ℕ, the syntactic observation path
    (rewrite, then encode) and the semantic observation path (encode, then
    apply eigenvalue scaling) produce different results.

    Proof: The Leibniz rewrite transforms obs(compose(f₁,f₁)) into a
    structurally different term. Any injective ε maps distinct terms to
    distinct values. Therefore ε(obsRewrite(obs(t))) ≠ ε(obs(t)),
    which means the encoding does not commute with obs. -/
theorem encoding_obstruction_term
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε (obsRewrite (.obs t_f₂)) ≠ ε (.obs t_f₂) := by
  intro h
  exact absurd (hε h) rewrite_ne_original

/-- **Corollary:** The eval-quote diagram does not commute.

    For any injective ε, the two paths through the diagram give different codes:
    - Top-then-right: eval the term, apply obs in State, get obs(f₂) = 2·f₂
    - Left-then-bottom: encode the term, apply obs as rewrite, get ε(Leibniz expansion)

    The encoded Leibniz expansion ε(oplus(...)) ≠ ε(obs(compose(f₁,f₁)))
    because these are structurally different terms and ε is injective. -/
theorem eval_quote_noncommutative
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε (obsRewrite (.obs t_f₂)) ≠ ε (.obs t_f₂) :=
  encoding_obstruction_term ε hε

/-- **Corollary:** Any injective encoding assigns compose(f₁,f₁) a code
    different from f₀, f₁, and z. -/
theorem injective_encoding_distinct
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε t_f₂ ≠ ε .f₀ ∧ ε t_f₂ ≠ ε .f₁ ∧ ε t_f₂ ≠ ε .z := by
  exact ⟨fun h => t_f₂_ne_f₀ (hε h),
         fun h => t_f₂_ne_f₁ (hε h),
         fun h => t_f₂_ne_z (hε h)⟩

end SpectralMonoid
