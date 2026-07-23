/-
  Forced Loss Core
  ================

  The slogan-layer definitions of ForcedLoss.lean, extracted into a
  file with NO imports.

  Why the extraction: instantiating MeaningPreserving on the
  FormalizedFormalLogic Foundation library's real PA terms
  (FoundationBridge.lean Part 3) requires loading Foundation's
  oleans, which cannot coexist with the `Mathlib.Tactic` closure
  that ForcedLoss.lean pulls in through Trilemma.lean (duplicate
  auto-generated equation lemmas; see TheoryInterfaces.lean for the
  same boundary). Keeping these definitions import-free lets the
  bridge prove the real-PA instance against the very same
  definitions the abstract development uses.

  Everything here is definitional or proved by anonymous
  constructor. ForcedLoss.lean re-exports these names by importing
  this file; no downstream reference changes.
-/

namespace UniversalObstruction

namespace ForcedLoss

universe u v

variable {T : Type u} {S : Type v}

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

end ForcedLoss

end UniversalObstruction
