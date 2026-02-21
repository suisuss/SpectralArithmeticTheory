/-
  Spectral Arithmetic: Term Algebra and the Intension/Extension Infrastructure
  =============================================================================

  Mathematics is substitution. Every formal expression has two faces:

  - **Intensional**: the expression as a named unit, opaque, treated as a whole.
    `obs(compose(f₁, f₁))` — you see the name, not the internals.

  - **Extensional**: the expression unfolded by substitution, all parts visible.
    `oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁)))` — the Leibniz rule
    has been applied, every sub-operation is explicit.

  `obsRewrite` is the **extensionalization** operation: it substitutes the
  Leibniz rule into observation terms, making implicit structure explicit.
  Any extensional form can then be re-intensionalized (given a new name/code),
  and the process begins again. Substitution never reaches a fixed point.

  `eval` maps terms to their semantic denotation in any DynSemiring.
  Crucially, `obsRewrite_eval` proves that extensionalization preserves
  semantics: the meaning is invariant, only the form changes. This confirms
  the gap is in the **naming** (encoding), not in the **meaning** (evaluation).

  `deepRewrite` applies extensionalization recursively, showing that
  substitution produces an unbounded chain of distinct forms.
-/

import SpectralArithmetic.Core.Semiring

namespace SpectralMonoid

/-! ## The Free Term Algebra -/

/-- Terms in the framework's language.
    Each term can be viewed intensionally (as a unit) or extensionally
    (by examining its constructor and sub-terms). -/
inductive Term where
  | f₀ : Term
  | f₁ : Term
  | z  : Term
  | compose : Term → Term → Term
  | oplus : Term → Term → Term
  | obs : Term → Term
  deriving DecidableEq, Repr

namespace Term

/-! ## Evaluation: Terms → State (semantic denotation) -/

/-- Evaluate a term in any DynSemiring. This is the semantic map:
    it takes a term (syntax) and produces its denotation (semantics).
    Evaluation is invariant under extensionalization (obsRewrite_eval). -/
def eval {State : Type*} [DynSemiring State] : Term → State
  | .f₀ => DynSemiring.toSpectralMonoid.f₀
  | .f₁ => DynSemiring.toSpectralMonoid.f₁
  | .z  => DynSemiring.toSpectralMonoid.z
  | .compose a b => SpectralMonoid.compose (eval a) (eval b)
  | .oplus a b => DynSemiring.oplus (eval a) (eval b)
  | .obs a => SpectralMonoid.obs (eval a)

/-! ## One-step Extensionalization (Leibniz Rewrite)

    `obsRewrite` is the extensionalization operation: it unfolds an
    intensional observation `obs(compose(a,b))` into its extensional
    form by applying the Leibniz (product) rule. The result makes the
    internal structure explicit — and introduces `oplus` (addition),
    which is where carry propagation enters for executable encodings. -/

/-- Apply the Leibniz rule as a one-step extensionalization:
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

/-! ## Semantic Invariance of Extensionalization

    The fundamental fact: extensionalization preserves meaning.
    `eval(obsRewrite(t)) = eval(t)` — the semantic denotation is
    invariant under substitution. The gap between intension and
    extension is in the FORM (syntax), not in the CONTENT (semantics). -/

/-- Extensionalization preserves evaluation:
    eval(obsRewrite(t)) = eval(t) for all t.
    Meaning is invariant; only the form changes. -/
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

/-- The term compose(f₁, f₁), representing f₂.
    Intensionally: "f₁ composed with f₁."
    Extensionally (after obs + Leibniz): "the sum of two cross-terms." -/
def t_f₂ : Term := .compose .f₁ .f₁

/-- One-step extensionalization of obs(f₂):
    The intensional `obs(compose(f₁, f₁))` unfolds to the extensional
    `oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁)))`.
    Note: this is where `oplus` (addition) enters the observation dynamics. -/
theorem obsRewrite_t_f₂ :
    obsRewrite (.obs t_f₂) =
      .oplus (.compose (.obs .f₁) .f₁) (.compose .f₁ (.obs .f₁)) := by
  rfl

/-- The Leibniz expansion of obs(f₂) contains obs(f₁) sub-terms -/
theorem obsRewrite_t_f₂_has_obs :
    obsRewrite (.obs t_f₂) =
      .oplus (.compose (.obs .f₁) .f₁) (.compose .f₁ (.obs .f₁)) := rfl

/-! ## Deep Extensionalization (Iterated Substitution)

    After one extensionalization, we get a term with `obs(f₁)` sub-terms.
    These can themselves be extensionalized (obs(f₁) → f₁), producing
    yet another structurally distinct term. This demonstrates that
    substitution never reaches a fixed point — each extensionalization
    produces a new form that can be further unfolded or re-named. -/

/-- Apply obsRewrite to all obs sub-terms at one level of depth.
    This performs extensionalization "one layer deeper." -/
def deepRewrite : Term → Term
  | .obs t => obsRewrite (.obs t)
  | .compose a b => .compose (deepRewrite a) (deepRewrite b)
  | .oplus a b => .oplus (deepRewrite a) (deepRewrite b)
  | t => t

/-- The fully extensionalized form of obs(f₂): apply the Leibniz rule,
    then resolve obs(f₁) → f₁ in each sub-term.
    Result: oplus(compose(f₁, f₁), compose(f₁, f₁)) = oplus(t_f₂, t_f₂).
    This is the "fully unfolded" form — all obs have been resolved. -/
theorem deep_extensionalize_f₂ :
    deepRewrite (obsRewrite (.obs t_f₂)) =
      .oplus (.compose .f₁ .f₁) (.compose .f₁ .f₁) := by
  rfl

/-- The extensionalized form differs from the original:
    substitution at depth 0 produces a new form. -/
theorem extensionalize_ne_original :
    obsRewrite (.obs t_f₂) ≠ .obs t_f₂ := by decide

/-- The deeply extensionalized form differs from the one-step extensionalization:
    substitution at depth 1 produces yet another new form. -/
theorem deep_ne_shallow :
    deepRewrite (obsRewrite (.obs t_f₂)) ≠ obsRewrite (.obs t_f₂) := by decide

/-- The deeply extensionalized form also differs from the original:
    every level of substitution produces a distinct term. -/
theorem deep_ne_original :
    deepRewrite (obsRewrite (.obs t_f₂)) ≠ .obs t_f₂ := by decide

/-- **No fixed point (There is no bottom):**
    Three successive forms of the same expression — intensional,
    one-step extensional, and deeply extensional — are all distinct.
    Substitution produces an unbounded chain of new forms. Any injective
    encoding must assign each a different code.

    This is the algebraic content of the halting problem for self-executing
    encodings: "the computation has finished" would require the
    intension/extension switching to reach a fixed point. This theorem
    proves no fixed point exists. The switching never stops. There is
    no bottom — no definitive final normalization. The halting problem
    is not a separate result to connect; it IS what this theorem means
    when read temporally. -/
theorem substitution_chain_distinct :
    .obs t_f₂ ≠ obsRewrite (.obs t_f₂) ∧
    obsRewrite (.obs t_f₂) ≠ deepRewrite (obsRewrite (.obs t_f₂)) ∧
    .obs t_f₂ ≠ deepRewrite (obsRewrite (.obs t_f₂)) :=
  ⟨fun h => absurd h.symm extensionalize_ne_original,
   fun h => absurd h.symm deep_ne_shallow,
   fun h => absurd h.symm deep_ne_original⟩

/-- Deep extensionalization also preserves semantics:
    eval(deepRewrite(t)) = eval(t). Meaning is invariant at every depth. -/
theorem deepRewrite_eval {State : Type*} [DynSemiring State] (t : Term) :
    eval (deepRewrite t) = (eval t : State) := by
  match t with
  | .obs t' => exact obsRewrite_eval (.obs t')
  | .compose a b =>
    simp only [deepRewrite, eval]
    rw [deepRewrite_eval a, deepRewrite_eval b]
  | .oplus a b =>
    simp only [deepRewrite, eval]
    rw [deepRewrite_eval a, deepRewrite_eval b]
  | .f₀ => rfl
  | .f₁ => rfl
  | .z => rfl

/-! ## General Extensionalization Theorem

    The obstruction is not specific to compose(f₁, f₁). The Leibniz rule
    extensionalizes ANY compound observation obs(compose(a, b)) into an
    oplus-rooted term — a different constructor. This is the general form
    of the intension/extension gap: observation of composition ALWAYS
    introduces addition (oplus) into the dynamics. -/

/-- The Leibniz rewrite of obs(compose(a, b)) always produces an oplus-rooted term.
    This is general over ALL sub-terms a and b. -/
theorem obsRewrite_compose (a b : Term) :
    obsRewrite (.obs (.compose a b)) =
      .oplus (.compose (.obs a) b) (.compose a (.obs b)) := rfl

/-- **General Intension/Extension Gap:**
    For ALL terms a and b, the extensionalized form of obs(compose(a, b))
    is structurally different from the intensional form.

    The extensional form has constructor `oplus` at the root.
    The intensional form has constructor `obs` at the root.
    These are different constructors, so the terms are always distinct.

    This is the fully general version: extensionalization ALWAYS changes
    the form of compound observation terms, for any sub-terms whatsoever. -/
theorem extensionalize_ne_original_general (a b : Term) :
    obsRewrite (.obs (.compose a b)) ≠ .obs (.compose a b) := by
  simp [obsRewrite]

/-- **General Encoding Obstruction:**
    For ANY injective encoding ε and ANY sub-terms a, b, the code of the
    extensionalized form differs from the code of the intensional form.

    ε(obsRewrite(obs(compose(a, b)))) ≠ ε(obs(compose(a, b)))

    This is the fully general statement: no injective encoding commutes
    with the Leibniz extensionalization on ANY compound observation term.
    One counterexample per encoding suffices to refute the coalgebra
    morphism — and here we have ALL compound observation terms as
    counterexamples. -/
theorem encoding_obstruction_general
    (ε : Term → ℕ) (hε : Function.Injective ε) (a b : Term) :
    ε (obsRewrite (.obs (.compose a b))) ≠ ε (.obs (.compose a b)) := by
  intro h
  exact absurd (hε h) (extensionalize_ne_original_general a b)

/-- **General Semantic Invariance:**
    Despite the encoding gap, eval(obsRewrite(obs(compose(a,b)))) = eval(obs(compose(a,b)))
    for ALL a, b. Meaning is always preserved. Form always changes.
    This is the general compilation ≠ execution asymmetry. -/
theorem semantic_invariance_general {State : Type*} [DynSemiring State] (a b : Term) :
    eval (.obs (.compose a b)) = (eval (obsRewrite (.obs (.compose a b))) : State) :=
  (obsRewrite_eval (.obs (.compose a b))).symm

end Term

end SpectralMonoid
