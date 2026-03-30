/-
  Rotation Calculus: Constraints
  ===============================

  The unconstrained rotation rule always terminates in linear time.
  Complexity enters through the constraint parameter — a decidable predicate
  on adjacent element pairs that gates the rotation.

  The constrained rule:
    observe(pair(a, b)) → pair(b, observe(a))    if C(a, b)
    observe(pair(a, b)) → stuck                   if ¬C(a, b)
    observe(ground)     → ground

  The constraint is the only point where a binary decision occurs — where
  the rich structure of (a, b) is projected to a single bit. This is where
  information is lost, and where the P vs NP gap becomes visible.

  Decidability levels:
  - Level 0: trivial (always true) — everything contracts
  - Level 1: Boolean — NP-complete problems live here
  - Level 2: primitive recursive — richer, still total
  - Level 3: general recursive — halting problem enters
-/

import SpectralArithmetic.Rotation.Rewrite

namespace RotationCalculus

open Term

/-! ## Constraint definition -/

/-- A constraint is a decidable predicate on pairs of terms.
    It determines whether the rotation rule may fire. -/
structure Constraint where
  /-- The constraint predicate on the active element and the rest. -/
  check : Term → Term → Bool

/-! ## Constrained rewrite -/

/-- The result of a constrained step: either we rotated, got stuck, or reached ground. -/
inductive StepResult where
  | rotated : Term → StepResult
  | stuck : Term → Term → StepResult
  | done : StepResult
  deriving DecidableEq, Repr

/-- One step of constrained rotation. -/
def constrainedStep (C : Constraint) : Term → StepResult
  | .observe (.pair a b) =>
    if C.check a b then
      .rotated (.pair b (.observe a))
    else
      .stuck a b
  | .observe .ground => .done
  | _ => .done

/-- Whether a constrained step succeeded (rotated or reached ground). -/
def StepResult.succeeded : StepResult → Bool
  | .rotated _ => true
  | .done => true
  | .stuck _ _ => false

/-! ## Multi-step constrained reduction -/

/-- The outcome of a full constrained reduction. -/
inductive Outcome where
  /-- Successfully contracted to ground. All constraints passed. -/
  | contracted : Outcome
  /-- Got stuck at a constraint failure. -/
  | stuckAt : Term → Term → Outcome
  deriving DecidableEq, Repr

/-- Run constrained rotation until ground or stuck.
    `fuel` bounds the number of steps (for computability).
    In practice, fuel = size of the term suffices. -/
def run (C : Constraint) : Term → ℕ → Outcome
  | _, 0 => .contracted  -- out of fuel; treat as done
  | t, fuel + 1 =>
    match constrainedStep C t with
    | .rotated t' => run C t' fuel
    | .stuck a b => .stuckAt a b
    | .done => .contracted

/-- A term contracts under constraint C if running it produces `.contracted`. -/
def contracts (C : Constraint) (t : Term) : Prop :=
  ∃ n, run C t n = .contracted

/-! ## Trivial constraint (Level 0) -/

/-- The trivial constraint that always passes. -/
def Constraint.trivial : Constraint where
  check := fun _ _ => true

/-- Under the trivial constraint, the constrained step always rotates. -/
theorem trivial_always_rotates (a b : Term) :
    constrainedStep .trivial (.observe (.pair a b))
    = .rotated (.pair b (.observe a)) := by
  simp [constrainedStep, Constraint.trivial]

/-- Under the trivial constraint, observe(ground) contracts. -/
theorem trivial_contracts_ground :
    contracts .trivial (.observe .ground) :=
  ⟨1, by simp [run, constrainedStep]⟩

/-! ## Constraint from labeled elements -/

/-- A label is an abstract tag carried by elements.
    Different problems use different label types. -/
structure Labeled (Label : Type*) where
  label : Label
  content : Term

/-- Build a constrained rotation problem from labeled elements and
    an adjacency predicate on labels. -/
def Constraint.fromLabels {Label : Type*} [DecidableEq Label]
    (adjacent : Label → Label → Bool)
    (getLabel : Term → Option Label) : Constraint where
  check := fun a b =>
    match getLabel a, getLabel b with
    | some la, some lb => adjacent la lb
    | _, _ => true  -- non-labeled terms pass by default

/-! ## Verification and search -/

/-- Verification: given a specific arrangement, does it contract?
    This is the P question — run the rotation and check. -/
def verify (C : Constraint) (arrangement : Term) : Bool :=
  match run C (.observe arrangement) (arrangement.size + 1) with
  | .contracted => true
  | .stuckAt _ _ => false

/-- An arrangement is a permutation of elements into a nested term.
    For a flat list, this is a specific ordering. -/
def isArrangementOf (arrangement : Term) (elements : List Term) : Prop :=
  arrangement.toList.Perm elements

/-- The search problem: does ANY arrangement of the elements contract?
    This is the NP question. -/
def existsContractingArrangement (C : Constraint) (elements : List Term) : Prop :=
  ∃ arrangement : Term,
    isArrangementOf arrangement elements ∧
    contracts C (.observe arrangement)

/-! ## Constraint composition -/

/-- Conjunction of two constraints. Both must pass. -/
def Constraint.and (C₁ C₂ : Constraint) : Constraint where
  check := fun a b => C₁.check a b && C₂.check a b

/-- Disjunction of two constraints. At least one must pass. -/
def Constraint.or (C₁ C₂ : Constraint) : Constraint where
  check := fun a b => C₁.check a b || C₂.check a b

/-- Negation of a constraint. -/
def Constraint.not (C : Constraint) : Constraint where
  check := fun a b => !C.check a b

/-- The impossible constraint that always fails. -/
def Constraint.impossible : Constraint where
  check := fun _ _ => false

/-- Under the impossible constraint, no non-trivial term contracts. -/
theorem impossible_never_contracts (a b : Term) :
    constrainedStep .impossible (.observe (.pair a b))
    = .stuck a b := by
  simp [constrainedStep, Constraint.impossible]

/-! ## The information loss at the constraint -/

/-- The constraint projects (a, b) to a single bit.
    This captures the information loss: the full structure of the pair
    is reduced to pass/fail. The carried content (b) passes through
    unchanged, but the relationship between a and b is collapsed. -/
theorem constraint_is_projection (C : Constraint) (a b : Term) :
    (constrainedStep C (.observe (.pair a b)) = .rotated (.pair b (.observe a)))
    ↔ (C.check a b = true) := by
  constructor
  · intro h
    simp [constrainedStep] at h
    by_cases hc : C.check a b = true
    · exact hc
    · simp [hc] at h
  · intro h
    simp [constrainedStep, h]

end RotationCalculus
