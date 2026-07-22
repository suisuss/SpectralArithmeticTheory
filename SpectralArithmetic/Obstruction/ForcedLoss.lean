/-
  Forced Semantic Loss (Issue #68)
  ================================

  Is "computation forces semantic loss" a theorem or a tautology?
  This file separates the layers at maximum generality — plain types
  T (syntax) and S (meanings), no term algebra — and answers:
  definition-dependent, with the content located precisely.

  1. The slogan layer IS a tautology, and is proved as one. "Every
     non-identity meaning-preserving rewrite generates loss"
     (MeaningPreserving.loss_of_move) and its contrapositive
     "faithful semantics freezes every meaning-preserving rewrite"
     (MeaningPreserving.frozen_of_injective) are each one line, and
     injective_iff_meaningPreserving_frozen shows the pair is the
     definition of injectivity repackaged: eval is injective IFF
     every eval-preserving rewrite is the identity. Any pair of
     eval-identified terms converts into a moving rewrite and back.

  2. The content therefore lives in whether COMPUTATION supplies a
     non-identity meaning-preserving rewrite. StepEval defines
     computation without assuming meaning-preservation: a
     deterministic step, a normal-form map, reachability, normality.
     Step-invariance of evaluation is then DERIVED, not assumed
     (StepEval.nf_step: two normal forms on one deterministic orbit
     coincide), as is idempotence (StepEval.nf_idem). Forced loss
     for evaluation-to-normal-form semantics is a theorem with one
     honest hypothesis — some term is not normal
     (StepEval.forced_loss) — and movement of the step equals
     non-normality pointwise (StepEval.step_ne_iff_nf_ne).

  3. nf is universal among dynamics-respecting semantics: every
     step-invariant eval factors through nf
     (StepEval.invariant_factors), so nf's kernel is contained in
     every invariant kernel (StepEval.ker_nf_le) and the loss
     propagates to every semantics that respects the dynamics.

  4. The characterization: faithful semantics freezes computation.
     nf is injective iff the step is frozen iff every term is its
     own normal form (StepEval.injective_nf_iff_frozen,
     StepEval.frozen_iff_nf_id); an injective step-invariant
     semantics exists iff the step is frozen
     (exists_injective_meaningPreserving_iff_frozen). Two
     computation-free forms isolate the same content: an idempotent
     normalization is injective iff it is the identity
     (Idempotent.injective_iff_frozen), and a semantics with
     canonical representatives is injective iff every term is
     canonical iff it is a bijective relabeling of syntax
     (section_injective_iff_canonical, section_injective_iff_bijective).

  5. The escape hatch, formalized: the loss attaches to INVARIANCE
     (answers stable under steps), not to "respecting dynamics" as
     such. Equivariance — eval commuting with a semantic step —
     admits an injective semantics over EVERY dynamics
     (exists_injective_equivariant: the identity is equivariant);
     invariance is exactly equivariance with trivial semantic
     dynamics (meaningPreserving_iff_equivariant_id), and
     equivariance collapses back to invariance the moment semantic
     values are stable (Equivariant.meaningPreserving_of_stable).
     Reversible computation lives in this escape; it buys a faithful
     semantics by giving up the notion of an answer.

  6. Instantiation: the TermF/LeibnizAlgebra results are the special
     case eval := eval A, rewrite := leibnizRewrite.
     nontrivialSemantics_of_term is loss_of_move at the universal
     witness (nontrivialSemantics_via_forcedLoss); eval A is never
     injective on an inhabited term language (eval_not_injective);
     and the Leibniz rewrite is itself an idempotent, hence lossy,
     syntax-valued normalization (leibnizRewrite_idem,
     leibnizRewrite_loss, leibnizRewrite_not_injective). A minimal
     StepEval instance (natCountdown) witnesses non-vacuity of the
     computation structure.
-/

import SpectralArithmetic.Obstruction.Trilemma

namespace UniversalObstruction

namespace ForcedLoss

variable {T : Type*} {S : Type*}

/-! ## Part 1: The Slogan Layer, and Why It Is a Tautology -/

/-- A rewrite preserves meaning when evaluation cannot see it. This
    is simultaneously "the semantics respects the dynamics" (eval is
    invariant along steps) and "the rewrite is sound for eval". -/
def MeaningPreserving (eval : T → S) (r : T → T) : Prop :=
  ∀ t, eval (r t) = eval t

/-- Semantic loss: the kernel of eval is non-trivial — two distinct
    expressions share a meaning. The plain-type form of
    NontrivialSemantics. -/
def SemanticLoss (eval : T → S) : Prop :=
  ∃ t₁ t₂ : T, t₁ ≠ t₂ ∧ eval t₁ = eval t₂

/-- A rewrite is frozen when it never moves: it is pointwise the
    identity. -/
def Frozen (r : T → T) : Prop :=
  ∀ t, r t = t

/-- **(a) LOSS FROM A MOVING REWRITE:** a meaning-preserving rewrite
    that moves some term exhibits semantic loss. One line — the
    slogan at this generality is a tautology, and is labeled as
    such. -/
theorem MeaningPreserving.loss_of_move {eval : T → S} {r : T → T}
    (h : MeaningPreserving eval r) {t : T} (ht : r t ≠ t) :
    SemanticLoss eval :=
  ⟨r t, t, ht, h t⟩

/-- **(b) FAITHFUL SEMANTICS FREEZES REWRITES:** if eval is
    injective, every meaning-preserving rewrite is the identity.
    One line — injectivity applied to the preservation equation. -/
theorem MeaningPreserving.frozen_of_injective {eval : T → S} {r : T → T}
    (h : MeaningPreserving eval r) (hinj : Function.Injective eval) :
    Frozen r :=
  fun t => hinj (h t)

/-- **THE TAUTOLOGY, MADE EXACT:** eval is injective IFF every
    meaning-preserving rewrite is frozen. The backward direction
    converts any eval-identified pair into a moving rewrite, so (a)
    and (b) jointly say nothing beyond the definition of
    injectivity. Whatever content "computation forces loss" has must
    come from the claim that computation SUPPLIES a moving
    meaning-preserving rewrite. -/
theorem injective_iff_meaningPreserving_frozen (eval : T → S) :
    Function.Injective eval ↔
      ∀ r : T → T, MeaningPreserving eval r → Frozen r := by
  classical
  constructor
  · intro hinj r hr
    exact hr.frozen_of_injective hinj
  · intro h t₁ t₂ heq
    by_contra hne
    have hmp : MeaningPreserving eval (fun t => if t = t₁ then t₂ else t) := by
      intro t
      rcases eq_or_ne t t₁ with rfl | ht
      · simpa using heq.symm
      · simp [ht]
    have hfr := h _ hmp t₁
    simp at hfr
    exact hne hfr.symm

/-! ## Part 2: Computation Without Assumed Meaning-Preservation

    A computation system is a deterministic step together with an
    evaluation-to-normal-form map: every term reaches its normal
    form by iterating the step, and normal forms are step-fixed.
    Nothing here says the step preserves anything — that the
    normal-form semantics is invariant along steps is a THEOREM
    (nf_step), obtained from determinism: two step-fixed points on
    one orbit coincide. -/

/-- A deterministic, terminating computation system: a step
    function, a normal-form map, reachability of the normal form by
    iterated stepping, and stability of normal forms. -/
structure StepEval (T : Type*) where
  /-- The small-step dynamics. -/
  step : T → T
  /-- Evaluation to normal form. -/
  nf : T → T
  /-- Every term reaches its normal form by iterating the step. -/
  reach : ∀ t, ∃ n, step^[n] t = nf t
  /-- Normal forms are step-fixed. -/
  normal : ∀ t, step (nf t) = nf t

/-- Two step-fixed points on the same deterministic orbit coincide:
    once an orbit hits a fixed point it stays there. -/
theorem fixed_on_orbit {f : T → T} {t : T} {i j : ℕ}
    (hi : f (f^[i] t) = f^[i] t) (hj : f (f^[j] t) = f^[j] t) :
    f^[i] t = f^[j] t := by
  rcases le_total i j with h | h
  · have hj' : f^[j] t = f^[j - i] (f^[i] t) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]
    rw [hj', Function.iterate_fixed hi]
  · have hi' : f^[i] t = f^[i - j] (f^[j] t) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]
    rw [hi', Function.iterate_fixed hj]

/-- **MEANING-PRESERVATION IS DERIVED, NOT ASSUMED:** in a
    deterministic terminating system, evaluation is invariant along
    steps. The orbit of t and the orbit of step t are the same orbit,
    and both normal forms are fixed points on it. -/
theorem StepEval.nf_step (E : StepEval T) (t : T) :
    E.nf (E.step t) = E.nf t := by
  obtain ⟨n, hn⟩ := E.reach t
  obtain ⟨m, hm⟩ := E.reach (E.step t)
  have hm' : E.step^[m + 1] t = E.nf (E.step t) := by
    rw [Function.iterate_succ_apply]
    exact hm
  have hfixn : E.step (E.step^[n] t) = E.step^[n] t := by
    rw [hn]
    exact E.normal t
  have hfixm : E.step (E.step^[m + 1] t) = E.step^[m + 1] t := by
    rw [hm']
    exact E.normal (E.step t)
  rw [← hm', ← hn]
  exact fixed_on_orbit hfixm hfixn

/-- Evaluation to normal form is idempotent: normal forms evaluate
    to themselves. Also derived, from stability of normal forms. -/
theorem StepEval.nf_idem (E : StepEval T) (t : T) :
    E.nf (E.nf t) = E.nf t := by
  obtain ⟨m, hm⟩ := E.reach (E.nf t)
  rw [← hm, Function.iterate_fixed (E.normal t)]

/-- **MOVEMENT EQUALS NON-NORMALITY, POINTWISE:** the step moves a
    term iff that term is not its own normal form. "Non-degenerate
    computation" and "some term is not yet evaluated" are the same
    hypothesis. -/
theorem StepEval.step_ne_iff_nf_ne (E : StepEval T) (t : T) :
    E.step t ≠ t ↔ E.nf t ≠ t := by
  constructor
  · intro ht hn
    have h := E.normal t
    rw [hn] at h
    exact ht h
  · intro hn hs
    obtain ⟨n, hr⟩ := E.reach t
    rw [Function.iterate_fixed hs] at hr
    exact hn hr.symm

/-- **FORCED LOSS:** in a deterministic terminating computation
    system, one term the step moves forces the normal-form semantics
    to identify distinct terms — the witness is the step itself,
    since t and step t are distinct with equal normal forms. Unlike
    Part 1 this is not a repackaged definition: invariance of nf is
    supplied by nf_step, not hypothesized. -/
theorem StepEval.forced_loss (E : StepEval T) {t : T}
    (ht : E.step t ≠ t) : SemanticLoss E.nf :=
  MeaningPreserving.loss_of_move E.nf_step ht

/-! ## Part 3: nf Is Universal Among Invariant Semantics -/

/-- Invariance along one step extends to invariance along any run. -/
theorem MeaningPreserving.iterate {eval : T → S} {r : T → T}
    (h : MeaningPreserving eval r) (n : ℕ) (t : T) :
    eval (r^[n] t) = eval t := by
  induction n generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (r t)).trans (h t)

/-- **nf IS THE FINEST INVARIANT SEMANTICS:** every step-invariant
    evaluation factors through the normal form. -/
theorem StepEval.invariant_factors {eval : T → S} (E : StepEval T)
    (h : MeaningPreserving eval E.step) (t : T) :
    eval (E.nf t) = eval t := by
  obtain ⟨n, hn⟩ := E.reach t
  rw [← hn]
  exact h.iterate n t

/-- **KERNEL DOMINANCE:** the normal-form kernel is contained in the
    kernel of every step-invariant semantics — the loss forced on nf
    propagates to every semantics that respects the dynamics. The
    plain-type form of extensionalF_iff_ker_le's easy direction. -/
theorem StepEval.ker_nf_le {eval : T → S} (E : StepEval T)
    (h : MeaningPreserving eval E.step) {t₁ t₂ : T}
    (he : E.nf t₁ = E.nf t₂) : eval t₁ = eval t₂ := by
  rw [← E.invariant_factors h t₁, he, E.invariant_factors h t₂]

/-! ## Part 4: The Characterization — Faithful Iff Frozen Iff Relabeling -/

/-- If the step never moves, every term is its own normal form. -/
theorem StepEval.nf_eq_self_of_frozen (E : StepEval T)
    (hfr : Frozen E.step) (t : T) : E.nf t = t := by
  obtain ⟨n, hn⟩ := E.reach t
  rw [← hn]
  exact Function.iterate_fixed (hfr t) n

/-- **FAITHFUL SEMANTICS FREEZES COMPUTATION:** the normal-form
    semantics is injective iff the step is pointwise the identity. -/
theorem StepEval.injective_nf_iff_frozen (E : StepEval T) :
    Function.Injective E.nf ↔ Frozen E.step := by
  constructor
  · intro hinj t
    exact hinj (E.nf_step t)
  · intro hfr t₁ t₂ he
    rw [← E.nf_eq_self_of_frozen hfr t₁, he, E.nf_eq_self_of_frozen hfr t₂]

/-- A frozen step means evaluation is the identity relabeling of
    syntax — and conversely. -/
theorem StepEval.frozen_iff_nf_id (E : StepEval T) :
    Frozen E.step ↔ ∀ t, E.nf t = t := by
  constructor
  · exact E.nf_eq_self_of_frozen
  · intro h t
    have hs := E.normal t
    rw [h t] at hs
    exact hs

/-- **THE ESCAPE REQUIRES FROZEN COMPUTATION:** some injective
    step-invariant semantics exists iff the step never moves — and
    then the identity works, so the faithful semantics of a frozen
    system are exactly the relabelings of its syntax. Stated with
    codomain T; an injection into any codomain restricts to this
    case through its image. -/
theorem exists_injective_meaningPreserving_iff_frozen (step : T → T) :
    (∃ eval : T → T, Function.Injective eval ∧ MeaningPreserving eval step)
      ↔ Frozen step := by
  constructor
  · rintro ⟨eval, hinj, hmp⟩
    exact hmp.frozen_of_injective hinj
  · intro hfr
    exact ⟨id, fun _ _ h => h, hfr⟩

/-! ## Part 5: Computation-Free Forms — Retractions and Canonical
    Representatives

    Two ways to say "evaluation" without any step function. An
    idempotent normalization is a self-meaning-preserving rewrite
    (semantics valued in syntax); a section exhibits canonical
    representatives of meanings. Both force the same trade, showing
    the loss needs no dynamics at all — only a term that is not its
    own canonical form. -/

/-- An idempotent normalization: evaluating an evaluation changes
    nothing. Definitionally, f preserves its own meaning. -/
def Idempotent (f : T → T) : Prop :=
  ∀ t, f (f t) = f t

/-- Idempotence is self-meaning-preservation, definitionally. -/
theorem idempotent_iff_self_meaningPreserving (f : T → T) :
    Idempotent f ↔ MeaningPreserving f f :=
  Iff.rfl

/-- An idempotent normalization that moves some term is lossy. -/
theorem Idempotent.loss {f : T → T} (h : Idempotent f) {t : T}
    (ht : f t ≠ t) : SemanticLoss f :=
  MeaningPreserving.loss_of_move h ht

/-- **AN IDEMPOTENT IS INJECTIVE IFF IT IS THE IDENTITY:** the
    retraction form of "faithful semantics freezes computation". -/
theorem Idempotent.injective_iff_frozen {f : T → T} (h : Idempotent f) :
    Function.Injective f ↔ Frozen f :=
  ⟨fun hinj => MeaningPreserving.frozen_of_injective h hinj,
   fun hfr t₁ t₂ he => (hfr t₁).symm.trans (he.trans (hfr t₂))⟩

/-- With canonical representatives (a section q of eval), one
    non-canonical term forces loss: t and its canonical form are
    distinct and eval-equal. No step function appears. -/
theorem section_loss {eval : T → S} {q : S → T}
    (hq : ∀ s, eval (q s) = s) {t : T} (ht : q (eval t) ≠ t) :
    SemanticLoss eval :=
  ⟨q (eval t), t, ht, hq (eval t)⟩

/-- **FAITHFUL IFF EVERYTHING CANONICAL:** given canonical
    representatives, eval is injective iff every term is its own
    canonical form. -/
theorem section_injective_iff_canonical {eval : T → S} {q : S → T}
    (hq : ∀ s, eval (q s) = s) :
    Function.Injective eval ↔ ∀ t, q (eval t) = t :=
  ⟨fun hinj t => hinj (hq (eval t)),
   fun hcan t₁ t₂ he => (hcan t₁).symm.trans ((congrArg q he).trans (hcan t₂))⟩

/-- **FAITHFUL IFF RELABELING:** a semantics with canonical
    representatives is already surjective, so injectivity makes eval
    a bijection — the semantics is a relabeling of syntax. -/
theorem section_injective_iff_bijective {eval : T → S} {q : S → T}
    (hq : ∀ s, eval (q s) = s) :
    Function.Injective eval ↔ Function.Bijective eval :=
  ⟨fun h => ⟨h, fun s => ⟨q s, hq s⟩⟩, fun h => h.1⟩

/-! ## Part 6: The Equivariant Escape

    The honest boundary of the forced-loss claim. Invariance says
    meanings are STABLE under steps — computing does not change the
    answer. Equivariance says meanings TRACK steps — the semantic
    domain has its own dynamics and eval commutes with it. The loss
    theorems attach to invariance only: the identity map is
    injective and equivariant over any dynamics whatsoever, so
    "semantics respects the dynamics" in the equivariant sense
    forces nothing. Reversible and linear computation live here.
    The two notions coincide exactly when semantic values are
    stable — when the semantics deals in answers. -/

/-- eval is equivariant when it intertwines the syntactic step with
    a semantic step. -/
def Equivariant (eval : T → S) (step : T → T) (stepS : S → S) : Prop :=
  ∀ t, eval (step t) = stepS (eval t)

/-- Invariance is equivariance into a trivial semantic dynamics. -/
theorem meaningPreserving_iff_equivariant_id (eval : T → S) (step : T → T) :
    MeaningPreserving eval step ↔ Equivariant eval step id :=
  Iff.rfl

/-- **NO EQUIVARIANT LOSS THEOREM EXISTS:** over every dynamics,
    however non-degenerate, some injective semantics is equivariant
    — the identity, tracking the dynamics as itself. The forced-loss
    trade is created by stability of answers, not by respect for
    dynamics as such. -/
theorem exists_injective_equivariant (step : T → T) :
    ∃ stepS : T → T, ∃ eval : T → T,
      Function.Injective eval ∧ Equivariant eval step stepS :=
  ⟨step, id, fun _ _ h => h, fun _ => rfl⟩

/-- Equivariance collapses to invariance the moment the semantic
    dynamics is frozen: answers that cannot move are answers the
    computation cannot change. -/
theorem Equivariant.meaningPreserving_of_stable {eval : T → S}
    {step : T → T} {stepS : S → S} (h : Equivariant eval step stepS)
    (hs : Frozen stepS) : MeaningPreserving eval step :=
  fun t => (h t).trans (hs (eval t))

/-- An equivariant semantics sends step-fixed terms to stepS-fixed
    meanings: normal forms land in the stable part of the semantic
    dynamics. -/
theorem Equivariant.fixed_of_normal {eval : T → S} {step : T → T}
    {stepS : S → S} (h : Equivariant eval step stepS) {t : T}
    (ht : step t = t) : stepS (eval t) = eval t := by
  rw [← h t, ht]

/-! ## Part 7: Non-Vacuity of the Computation Structure -/

/-- Iterated decrement subtracts. -/
theorem sub_one_iterate (n t : ℕ) : (fun k => k - 1)^[n] t = t - n := by
  induction n generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    omega

/-- A minimal non-degenerate StepEval: countdown on ℕ. Every
    positive number is moved by the step, so the structure's
    hypotheses are jointly satisfiable with genuine computation. -/
def natCountdown : StepEval ℕ where
  step n := n - 1
  nf _ := 0
  reach t := ⟨t, by rw [sub_one_iterate]; omega⟩
  normal _ := rfl

/-- The countdown system exhibits forced loss, as it must. -/
theorem natCountdown_loss : SemanticLoss natCountdown.nf :=
  natCountdown.forced_loss (t := 1) (by decide)

end ForcedLoss

/-! ## Part 8: Instantiation — the Leibniz Setting Is the Special Case

    The TermF/LeibnizAlgebra results of Universal.lean and
    Trilemma.lean instantiate the plain-type layer with
    eval := eval A and rewrite := leibnizRewrite. What the Leibniz
    structure contributes is exactly the moving meaning-preserving
    rewrite that Part 1 shows is the sole carrier of content: the
    Leibniz law makes leibnizRewrite meaning-preserving in EVERY
    algebra, and the constructor change makes it move. -/

namespace TermF

open ForcedLoss

variable {C : Type*} {S : Type*}

/-- The Leibniz rewrite is meaning-preserving in every algebra —
    the semantic invariance of Universal.lean in the plain-type
    vocabulary. -/
theorem leibnizRewrite_meaningPreserving (A : LeibnizAlgebra C S) :
    MeaningPreserving (eval A) (leibnizRewrite (C := C)) :=
  leibnizRewrite_eval A

/-- Deep extensionalization is likewise meaning-preserving. -/
theorem deepRewrite_meaningPreserving (A : LeibnizAlgebra C S) :
    MeaningPreserving (eval A) (deepRewrite (C := C)) :=
  deepRewrite_eval A

/-- **THE EXISTING NON-TRIVIALITY THEOREM IS AN INSTANCE:**
    nontrivialSemantics_of_term is loss_of_move applied to the
    Leibniz rewrite at the universal witness term. -/
theorem nontrivialSemantics_via_forcedLoss (A : LeibnizAlgebra C S)
    (t₀ : TermF C) : NontrivialSemantics A :=
  (leibnizRewrite_meaningPreserving A).loss_of_move
    (leibniz_changes_form t₀ t₀)

/-- **EVALUATION IS NEVER FAITHFUL:** on an inhabited term language
    no Leibniz semantics is injective — the (b)-direction applied to
    the Leibniz rewrite, which cannot be frozen. -/
theorem eval_not_injective (A : LeibnizAlgebra C S) (t₀ : TermF C) :
    ¬ Function.Injective (eval A) := fun hinj =>
  leibniz_changes_form t₀ t₀
    ((leibnizRewrite_meaningPreserving A).frozen_of_injective hinj
      (.obs (.comp t₀ t₀)))

/-- The Leibniz rewrite is idempotent: its result is add-rooted or
    unchanged, and the rewrite only fires on obs-of-comp roots. It
    is therefore itself a syntax-valued normalization in the sense
    of Part 5. -/
theorem leibnizRewrite_idem : Idempotent (leibnizRewrite (C := C)) :=
  fun t =>
    match t with
    | .obs (.comp _ _) => rfl
    | .obs (.obs _) => rfl
    | .obs (.add _ _) => rfl
    | .obs (.const _) => rfl
    | .const _ => rfl
    | .comp _ _ => rfl
    | .add _ _ => rfl

/-- As an idempotent normalization, the Leibniz rewrite is lossy on
    any inhabited term language. -/
theorem leibnizRewrite_loss (t₀ : TermF C) :
    SemanticLoss (leibnizRewrite (C := C)) :=
  leibnizRewrite_idem.loss (leibniz_changes_form t₀ t₀)

/-- The Leibniz rewrite is not injective: it identifies each
    obs-of-comp term with its own expansion. -/
theorem leibnizRewrite_not_injective (t₀ : TermF C) :
    ¬ Function.Injective (leibnizRewrite (C := C)) := fun hinj =>
  leibniz_changes_form t₀ t₀
    (leibnizRewrite_idem.injective_iff_frozen.mp hinj (.obs (.comp t₀ t₀)))

end TermF

/-! ## Part 9: Summary

    PROVED (sorry-free, no axioms), over plain types:

    | Theorem | Content |
    |---------|---------|
    | MeaningPreserving.loss_of_move | (a) moving rewrite gives loss — tautology, labeled |
    | MeaningPreserving.frozen_of_injective | (b) faithful freezes rewrites — tautology, labeled |
    | injective_iff_meaningPreserving_frozen | (a)+(b) = the definition of injectivity |
    | StepEval.nf_step | invariance of evaluation DERIVED from determinism |
    | StepEval.nf_idem | idempotence of evaluation derived |
    | StepEval.step_ne_iff_nf_ne | non-degeneracy = a non-normal term |
    | StepEval.forced_loss | the theorem: one non-normal term forces loss |
    | StepEval.invariant_factors, ker_nf_le | nf is the finest invariant semantics |
    | StepEval.injective_nf_iff_frozen | faithful iff computation frozen |
    | StepEval.frozen_iff_nf_id | frozen iff evaluation is the identity |
    | exists_injective_meaningPreserving_iff_frozen | injective invariant semantics iff frozen |
    | Idempotent.injective_iff_frozen | retraction form of the trade |
    | section_loss, section_injective_iff_* | canonical-representative form; faithful = relabeling |
    | exists_injective_equivariant | the escape: equivariance forces nothing |
    | Equivariant.meaningPreserving_of_stable | the escape closes once answers are stable |
    | TermF instantiations | the Leibniz results are the special case |

    Verdict encoded by the file: at the slogan's generality the
    claim is a tautology (Part 1 proves it IS the definition of
    injectivity). The substantive theorem is Part 2's: for
    deterministic terminating computation, meaning-preservation of
    evaluation is derivable rather than assumable, so semantic loss
    follows from the existence of one unevaluated term. The honest
    boundary is Part 6's: semantics that track rather than stabilize
    — reversible computation — escape, at the price of having no
    answers. -/

end UniversalObstruction
