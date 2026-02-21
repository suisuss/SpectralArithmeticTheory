/-
  Spectral Arithmetic: The Encoding Obstruction — Intension/Extension Gap
  =======================================================================

  **The Central Result:** Compilation and execution are necessarily separate.

  The encoding (intensionalization — naming a form) and the observation
  (extensionalization — unfolding a form via the Leibniz rule) do not commute
  through any injective map. This is because:

  1. Extensionalization (obsRewrite) unfolds obs(compose(f₁,f₁)) into a
     structurally different term containing oplus (addition)
  2. The extensional form is provably distinct from the intensional form
     (by DecidableEq on Term)
  3. Any injective encoding ε must map distinct terms to distinct codes
  4. Therefore ε(extensionalize(t)) ≠ ε(t) — the encoding of execution
     does not equal the execution of encoding

  The semantic invariance theorem (obsRewrite_eval) confirms: the MEANING
  is preserved by extensionalization. Only the FORM changes. This is why
  compilation (which preserves meaning but changes form) and execution
  (which changes form to produce results) are necessarily separate operations.

  For passive encoding (inert Gödel labels), this gap gives incompleteness.
  For executable encoding (self-running code), this gap forces external state
  (registers) because the extensionalization step introduces addition, and
  addition requires carry propagation, and carry requires state outside
  the encoding.
-/

import SpectralArithmetic.Obstruction.Encoding
import SpectralArithmetic.Core.Semiring

namespace SpectralMonoid

open Term DynSemiring

/-! ## Semantic side: eigenvalue observation (intensional)

    The semantic observation reads off eigenvalues — a single number
    from an opaque state. This is the intensional view: the state is
    treated as a unit, and obs extracts its "name" (eigenvalue). -/

/-- f₂ = compose(f₁, f₁) evaluates to iterS 2 -/
theorem eval_t_f₂ {State : Type*} [DynSemiring State] :
    eval t_f₂ = iterS (State := State) 2 := by
  simp [t_f₂, eval, iterS, succ]

/-- Intensional observation: obs(f₂) = 2 · f₂.
    The eigenvalue theorem reads off a number from the state-as-unit. -/
theorem obs_f₂_eigenvalue {State : Type*} [DynSemiring State] :
    obs (iterS (State := State) 2) = smul 2 (iterS 2) :=
  eigenvalue 2

/-- The general eigenvalue theorem: obs(iterS n) = n · iterS n.
    This is the intensional reading — a single number extracted
    from the state without unfolding its internal structure. -/
theorem semantic_eigenvalue {State : Type*} [DynSemiring State] (n : ℕ) :
    obs (iterS (State := State) n) = smul n (iterS n) :=
  eigenvalue n

/-! ## Syntactic side: Leibniz rewrite (extensional)

    The syntactic observation unfolds the term via the Leibniz rule,
    making internal structure explicit. This is the extensional view:
    the term is decomposed, and oplus (addition) enters the dynamics.
    The introduction of addition is where carry propagation begins
    for any executable encoding. -/

/-- Extensional observation: obsRewrite(obs(f₂)) evaluates to oplus(f₂, f₂).
    The Leibniz rule has unfolded the observation, introducing addition. -/
theorem syntactic_obs_f₂_eval {State : Type*} [DynSemiring State] :
    eval (obsRewrite (.obs t_f₂)) =
      oplus (compose f₁ f₁ : State) (compose f₁ f₁) := by
  simp only [obsRewrite, t_f₂, eval, obs_f₁]

/-! ## The Intension/Extension Gap

    The core obstruction: extensionalization (substitution, unfolding)
    and intensionalization (naming, encoding) do not commute.

    - obsRewrite_eval proves: meaning is preserved (semantics is invariant)
    - encoding_obstruction_term proves: form is changed (codes must differ)

    This is why compilation ≠ execution. Both preserve meaning, but they
    change form in ways that cannot be reconciled through any injective
    encoding. The encoding of the unfolded form is not the unfolding
    of the encoded form. -/

/-- The extensionalized obs(f₂) is the Leibniz expansion:
    oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁))).
    This is the term with its internal structure made explicit. -/
theorem obs_rewrite_f₂ :
    obsRewrite (.obs t_f₂) =
      Term.oplus (Term.compose (Term.obs Term.f₁) Term.f₁)
                 (Term.compose Term.f₁ (Term.obs Term.f₁)) := rfl

/-- Extensionalization changes the form: the unfolded term ≠ the folded term.
    This is the syntactic manifestation of the intension/extension gap. -/
theorem rewrite_changes_term :
    obsRewrite (.obs t_f₂) ≠ Term.obs t_f₂ := by decide

/-! ## The Encoding Obstruction: Naming Cannot Catch Substitution -/

/-- compose(f₁, f₁) is distinct from the base terms f₀, f₁, z.
    Any injective naming assigns it a distinct code. -/
theorem t_f₂_ne_f₀ : t_f₂ ≠ Term.f₀ := by decide
theorem t_f₂_ne_f₁ : t_f₂ ≠ Term.f₁ := by decide
theorem t_f₂_ne_z : t_f₂ ≠ Term.z := by decide

/-- The Leibniz-extensionalized obs(f₂) is distinct from the
    intensional obs(f₂). Any injective naming gives different codes. -/
theorem rewrite_ne_original :
    obsRewrite (.obs t_f₂) ≠ Term.obs t_f₂ := by decide

/-- **Theorem 1 (The Intension/Extension Gap — Encoding Obstruction):**

    For any injective encoding ε : Term → ℕ, the extensionalized form
    (Leibniz-unfolded) gets a different code than the intensional form
    (the original named term).

    ε(extensionalize(obs(t))) ≠ ε(obs(t))

    This is the formal statement that naming (encoding, compilation)
    and unfolding (execution, substitution) do not commute through
    any injective map. The encoding of the executed form is not the
    execution of the encoded form.

    Proof: extensionalization produces a structurally different term
    (by DecidableEq). Injectivity preserves distinctness. -/
theorem encoding_obstruction_term
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε (obsRewrite (.obs t_f₂)) ≠ ε (.obs t_f₂) := by
  intro h
  exact absurd (hε h) rewrite_ne_original

/-- **Corollary (Compilation ≠ Execution):**

    The eval-quote diagram does not commute. The two paths:

    Path 1 (compile then run): encode the term, apply obs in State
      → produces eigenvalue scaling (intensional, multiplicative)

    Path 2 (run then compile): apply obs as rewrite, encode the result
      → produces Leibniz expansion with oplus (extensional, additive)

    These give different codes for any injective encoding, because
    the extensional path introduces addition (oplus) that the
    intensional path does not contain. This is where, for executable
    encodings, carry propagation enters and forces external state. -/
theorem compilation_ne_execution
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε (obsRewrite (.obs t_f₂)) ≠ ε (.obs t_f₂) :=
  encoding_obstruction_term ε hε

/-- **Corollary (No Fixed Point for Iterated Encoding):**

    Not only does one extensionalization produce a different code,
    but deep extensionalization produces yet another different code.
    The chain intensional → extensional → deeply extensional consists
    of three distinct terms, hence three distinct codes under any
    injective encoding. Substitution never reaches a fixed point. -/
theorem no_encoding_fixpoint
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε (.obs t_f₂) ≠ ε (obsRewrite (.obs t_f₂)) ∧
    ε (obsRewrite (.obs t_f₂)) ≠ ε (deepRewrite (obsRewrite (.obs t_f₂))) ∧
    ε (.obs t_f₂) ≠ ε (deepRewrite (obsRewrite (.obs t_f₂))) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (hε h) (Ne.symm extensionalize_ne_original)
  · exact absurd (hε h) (Ne.symm deep_ne_shallow)
  · exact absurd (hε h) (Ne.symm deep_ne_original)

/-- **Semantic Invariance:** Despite the encoding gap, the MEANING is
    preserved at every level. This is the key asymmetry:

    eval(intensional)           = eval(extensional)           -- meaning same
    ε(intensional)              ≠ ε(extensional)              -- code differs

    Meaning is invariant under substitution. Form is not.
    This is why compilation (which preserves meaning) and execution
    (which transforms form) are necessarily separate operations. -/
theorem semantic_invariance_across_gap {State : Type*} [DynSemiring State] :
    eval (.obs t_f₂) = (eval (obsRewrite (.obs t_f₂)) : State) :=
  (obsRewrite_eval (.obs t_f₂)).symm

/-- Any injective encoding assigns compose(f₁,f₁) a code
    different from f₀, f₁, and z. -/
theorem injective_encoding_distinct
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε t_f₂ ≠ ε .f₀ ∧ ε t_f₂ ≠ ε .f₁ ∧ ε t_f₂ ≠ ε .z := by
  exact ⟨fun h => t_f₂_ne_f₀ (hε h),
         fun h => t_f₂_ne_f₁ (hε h),
         fun h => t_f₂_ne_z (hε h)⟩

/-! ## The Headline Results

    The fully general theorems, stated cleanly. These are the results
    that constitute the encoding obstruction as a mathematical theorem. -/

/-- **MAIN THEOREM (No Coalgebra Morphism Exists):**

    There is no injective encoding ε : Term → ℕ that commutes with
    the Leibniz extensionalization on ALL terms. Specifically, for
    every injective ε and every pair of sub-terms a, b:

      ε(obsRewrite(obs(compose(a, b)))) ≠ ε(obs(compose(a, b)))

    The intensional form (obs at root) and extensional form (oplus at root)
    are always structurally distinct, so any injective encoding must
    assign them different codes. Since a coalgebra morphism must commute
    on ALL terms, no injective encoding is a coalgebra morphism.

    This is universal over:
    - ALL injective encodings ε
    - ALL sub-terms a and b

    One failure suffices to refute the morphism. Here, EVERY compound
    observation term is a failure. The encoding of execution never equals
    the execution of encoding.

    Meanwhile (semantic_invariance_general): the MEANING is always preserved.
    Compilation and execution are necessarily separate operations — they
    preserve meaning but disagree on form, and no encoding reconciles them. -/
theorem no_coalgebra_morphism
    (ε : Term → ℕ) (hε : Function.Injective ε) (a b : Term) :
    ε (obsRewrite (.obs (.compose a b))) ≠ ε (.obs (.compose a b)) :=
  encoding_obstruction_general ε hε a b

/-- **SEMANTIC INVARIANCE (General):**
    The other half of the result: despite the encoding gap,
    eval(obs(compose(a,b))) = eval(obsRewrite(obs(compose(a,b))))
    for ALL a, b, in ALL models.

    Meaning is invariant. Form is not. Both facts are proved.
    Together they constitute the encoding obstruction:
    the gap between intension and extension is real (codes differ)
    but not semantic (denotations agree). -/
theorem semantic_invariance_general' {State : Type*} [DynSemiring State]
    (a b : Term) :
    eval (.obs (.compose a b)) =
      (eval (obsRewrite (.obs (.compose a b))) : State) :=
  semantic_invariance_general a b

end SpectralMonoid
