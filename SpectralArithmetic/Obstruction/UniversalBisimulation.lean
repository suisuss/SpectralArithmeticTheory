/-
  Universal Bisimulation Boundary (Issue #55)
  ============================================

  Lifts the bisimulation characterization from the concrete spectral
  Term algebra (Bisimulation.lean) to the parameterized term algebras
  TermF C of Universal.lean: the boundary theorem holds over EVERY
  constant signature C and EVERY Leibniz algebra, matching the
  universality at which the paper states the encoding obstruction.

  Results (all sorry-free, no axioms):

  1. Tier 1, universal: for every signature and every Leibniz algebra,
     the graph of eval is a bisimulation between the syntactic
     observation system (TermF C, deepRewrite-after-obs, eval) and
     the semantic system (S, interpObs, id).
  2. Tier 2, universal: an observable o : TermF C -> O supports a
     bisimulation relating each term to its evaluation iff o is
     extensional for that algebra (factors through eval).
  3. The boundary's intensional side, universal: the root constructor
     observable is not even rewrite-invariant (the Leibniz rewrite
     changes obs-roots to add-roots — Universal.lean's
     leibniz_changes_form, relocated to the observable side), and no
     injective coding of TermF C is extensional for any algebra.
     The universal witness pair costs nothing: a term and its Leibniz
     rewrite are distinct (leibniz_changes_form) yet eval-equal in
     EVERY Leibniz algebra (leibnizRewrite_preserves_eval) — no
     model-specific identity like compose_f₀ is needed at this level.

  The strictness middle witness (rewrite-invariant but not
  extensional) is model-relative by nature; the concrete instance
  lives in Bisimulation.lean (isF₀ over the spectral Term algebra).
-/

import SpectralArithmetic.Obstruction.Universal
import SpectralArithmetic.Obstruction.Bisimulation

namespace UniversalObstruction

namespace TermF

open SpectralMonoid (ObsSystem Bisim)

variable {C : Type*} {S : Type*} {O : Type*}

/-! ## Part 1: The Universal Observation Systems -/

/-- The syntactic step on TermF C: apply obs, unfold via the Leibniz
    rewrite. The signature-generic counterpart of Bisimulation.lean's
    synStep. -/
def synStepF (t : TermF C) : TermF C := deepRewrite (.obs t)

/-- The syntactic step implements semantic observation through eval,
    in every Leibniz algebra. -/
theorem synStepF_eval (A : LeibnizAlgebra C S) (t : TermF C) :
    eval A (synStepF t) = A.interpObs (eval A t) := by
  unfold synStepF
  rw [deepRewrite_eval]
  simp only [eval]

/-- The syntactic observation system over an output map. -/
def synSysF (o : TermF C → O) : ObsSystem (TermF C) O where
  step := synStepF
  out := o

/-- The semantic observation system of a Leibniz algebra. -/
def semSysF (A : LeibnizAlgebra C S) (oS : S → O) : ObsSystem S O where
  step := A.interpObs
  out := oS

/-! ## Part 2: Tier 1, Universal -/

/-- **THE EVAL GRAPH IS A BISIMULATION, UNIVERSALLY:** over every
    signature C and every Leibniz algebra A, relating each term to
    its evaluation is a bisimulation. -/
def evalGraphBisimF (A : LeibnizAlgebra C S) :
    Bisim (synSysF (eval A)) (semSysF A id) where
  rel t s := eval A t = s
  out_eq h := h
  step_rel {t s} h := by
    change eval A (synStepF t) = A.interpObs s
    rw [synStepF_eval, h]

/-- The universal eval-graph bisimulation is total on terms. -/
theorem evalGraphBisimF_total (A : LeibnizAlgebra C S) (t : TermF C) :
    (evalGraphBisimF A).rel t (eval A t) := rfl

/-! ## Part 3: Tier 2, Universal — the Boundary -/

/-- An observable of TermF C is extensional for an algebra A if it
    factors through evaluation in A. -/
def ExtensionalF (A : LeibnizAlgebra C S) (o : TermF C → O) : Prop :=
  ∃ oS : S → O, ∀ t, o t = oS (eval A t)

/-- An observable supports a bisimulation for A if some semantic
    output map makes the two systems bisimilar with every term
    related to its evaluation. -/
def SupportsBisimF (A : LeibnizAlgebra C S) (o : TermF C → O) : Prop :=
  ∃ oS : S → O, ∃ B : Bisim (synSysF o) (semSysF A oS),
    ∀ t, B.rel t (eval A t)

/-- **THE UNIVERSAL BOUNDARY (Tier 2):** over every signature and
    every Leibniz algebra, an observable supports a bisimulation iff
    it is extensional. -/
theorem supportsBisimF_iff_extensionalF (A : LeibnizAlgebra C S)
    (o : TermF C → O) :
    SupportsBisimF A o ↔ ExtensionalF A o := by
  constructor
  · rintro ⟨oS, B, htot⟩
    exact ⟨oS, fun t => B.out_eq (htot t)⟩
  · rintro ⟨oS, ho⟩
    refine ⟨oS, ⟨fun t s => eval A t = s, ?_, ?_⟩, fun _ => rfl⟩
    · intro t s hrel
      change o t = oS s
      rw [ho t, hrel]
    · intro t s hrel
      change eval A (synStepF t) = A.interpObs s
      rw [synStepF_eval, hrel]

/-- Extensional observables respect evaluation. -/
theorem ExtensionalF.eval_congr {A : LeibnizAlgebra C S}
    {o : TermF C → O} (h : ExtensionalF A o)
    {t t' : TermF C} (he : eval A t = eval A t') : o t = o t' := by
  obtain ⟨oS, ho⟩ := h
  rw [ho t, ho t', he]

/-! ## Part 4: Rewrite Invariance, Universal -/

/-- Invariance under the eval-preserving Leibniz normalization. -/
def RewriteInvariantF (o : TermF C → O) : Prop :=
  ∀ t, o (deepRewrite t) = o t

/-- Extensional observables are rewrite-invariant, in every algebra. -/
theorem ExtensionalF.rewriteInvariantF {A : LeibnizAlgebra C S}
    {o : TermF C → O} (h : ExtensionalF A o) : RewriteInvariantF o := by
  obtain ⟨oS, ho⟩ := h
  intro t
  rw [ho, ho, deepRewrite_eval]

/-! ## Part 5: The Intensional Side, Universal

    The universal witness pair: a compound observation and its
    Leibniz rewrite. Distinct as terms (Universal.lean's root
    constructor change), eval-equal in every Leibniz algebra
    (semantic invariance). Both facts are already proved in
    Universal.lean; here they power the boundary. -/

/-- The root constructor of a TermF term. -/
inductive RootTagF where
  | const | comp | add | obs
  deriving DecidableEq, Repr

/-- Read the root constructor: the canonical intensional observable. -/
def rootTagF : TermF C → RootTagF
  | .const _ => .const
  | .comp _ _ => .comp
  | .add _ _ => .add
  | .obs _ => .obs

/-- The root constructor is not rewrite-invariant: deep rewriting
    turns any obs-of-comp root into an add root. Needs only one term
    of the signature to state. -/
theorem rootTagF_not_rewriteInvariantF (t₀ : TermF C) :
    ¬ RewriteInvariantF (rootTagF (C := C)) := by
  intro h
  have hw := h (.obs (.comp t₀ t₀))
  simp only [deepRewrite, leibnizRewrite, rootTagF] at hw
  exact RootTagF.noConfusion hw

/-- The root constructor is not extensional, for any algebra. -/
theorem rootTagF_not_extensionalF (A : LeibnizAlgebra C S) (t₀ : TermF C) :
    ¬ ExtensionalF A (rootTagF (C := C)) :=
  fun h => rootTagF_not_rewriteInvariantF t₀ h.rewriteInvariantF

/-- **NO INJECTIVE CODING IS EXTENSIONAL, UNIVERSALLY:** for every
    signature, every Leibniz algebra, and every injective
    ε : TermF C → ℕ, ε does not factor through eval. The witness is
    the universal pair: leibnizRewrite changes the term
    (leibniz_changes_form) but never the meaning
    (leibnizRewrite_preserves_eval). -/
theorem injective_not_extensionalF (A : LeibnizAlgebra C S)
    (t₀ : TermF C) (ε : TermF C → ℕ) (hε : Function.Injective ε) :
    ¬ ExtensionalF A ε := by
  rintro ⟨oS, ho⟩
  have heq : ε (leibnizRewrite (.obs (.comp t₀ t₀))) =
      ε (.obs (.comp t₀ t₀)) := by
    rw [ho (leibnizRewrite (.obs (.comp t₀ t₀))), ho (.obs (.comp t₀ t₀)),
      leibnizRewrite_preserves_eval]
  exact absurd (hε heq) (leibniz_changes_form t₀ t₀)

/-- **INJECTIVITY IS INTENSIONALITY, UNIVERSALLY:** no injective
    coding of any TermF C supports a bisimulation with any Leibniz
    algebra's semantics. This is Universal.lean's
    universal_encoding_obstruction relocated to where it has content:
    the bisimulation boundary excludes every intensional observable,
    and a faithful code is the maximally intensional one — over every
    signature at once. -/
theorem injective_no_bisimF (A : LeibnizAlgebra C S)
    (t₀ : TermF C) (ε : TermF C → ℕ) (hε : Function.Injective ε) :
    ¬ SupportsBisimF A ε :=
  fun h => injective_not_extensionalF A t₀ ε hε
    ((supportsBisimF_iff_extensionalF A ε).mp h)

/-! ## Part 6: Summary

    PROVED (sorry-free, no axioms), universally over all signatures C
    and all Leibniz algebras:

    | Theorem | Content |
    |---------|---------|
    | synStepF_eval | The syntactic step implements interpObs |
    | evalGraphBisimF (+ total) | Tier 1: the eval graph is a bisimulation |
    | supportsBisimF_iff_extensionalF | Tier 2: the boundary |
    | ExtensionalF.rewriteInvariantF | Extensional implies rewrite-invariant |
    | rootTagF_not_rewriteInvariantF | The intensional witness |
    | injective_not_extensionalF | No injective coding is extensional |
    | injective_no_bisimF | Injectivity is intensionality |

    Together with Bisimulation.lean (the concrete spectral instance,
    including the strict middle of the hierarchy) and
    QuotationCost.lean (the quantitative separation), this completes
    the formal content of paper section 5b at the same generality as
    section 4's universal obstruction. -/

end TermF

end UniversalObstruction
