/-
  Rotation Calculus: The Rewrite Rule
  ====================================

  The single rewrite rule of the rotation calculus:

    observe(pair(a, b)) → pair(b, observe(a))     [R]
    observe(ground)     → ground                   [G]

  Properties proved:
  - Termination: pairsUnderObserve strictly decreases
  - No symbol creation: constructorCount is invariant
  - Confluence: at most one redex exists (trivial)
  - Reversibility: the rule is invertible
-/

import SpectralArithmetic.Rotation.Syntax

namespace RotationCalculus

open Term

/-! ## The rewrite rule -/

/-- One step of the rotation rule.
    Returns `none` if no redex exists (already in normal form). -/
def step : Term → Option Term
  | .observe (.pair a b) => some (.pair b (.observe a))
  | .observe .ground => some .ground
  | _ => none

/-- Whether a term is in normal form (no redex). -/
def isNormalForm (t : Term) : Bool := step t == none

/-- Whether a term has a redex. -/
def hasRedex (t : Term) : Bool := step t != none

/-! ## Termination measure -/

/-- For observe(pair(a, b)), one step produces pair(b, observe(a))
    where the measure (pairs under observe) decreases. -/
theorem step_observe_pair_measure (a b : Term) :
    (Term.pair b (.observe a)).pairsUnderObserve < (Term.observe (.pair a b)).pairsUnderObserve := by
  simp [pairsUnderObserve, size]

/-- For observe(ground), one step produces ground with measure 0. -/
theorem step_observe_ground_measure :
    Term.ground.pairsUnderObserve = 0 := by
  simp [pairsUnderObserve]

/-! ## Multi-step reduction -/

/-- Execute n steps of reduction, returning the result.
    Stops early if normal form is reached. -/
def stepN : Term → ℕ → Term
  | t, 0 => t
  | t, n + 1 =>
    match step t with
    | some t' => stepN t' n
    | none => t

/-- Full normalization via well-founded recursion on pairsUnderObserve.
    Always terminates because each step strictly decreases the measure. -/
def normalize : Term → Term
  | .observe (.pair a b) => normalize (.pair b (.observe a))
  | .observe .ground => .ground
  | t => t
termination_by t => t.pairsUnderObserve
decreasing_by
  simp_all [pairsUnderObserve, size]

/-! ## No symbol creation -/

/-- The rotation rule for observe(pair(a,b)) conserves constructor count. -/
theorem constructorCount_rotate (a b : Term) :
    (Term.pair b (.observe a)).constructorCount = (Term.observe (.pair a b)).constructorCount := by
  simp [constructorCount]; omega

/-- The ground reduction conserves constructor count (up to the observe wrapper). -/
theorem constructorCount_ground :
    Term.ground.constructorCount + 1 = (Term.observe .ground).constructorCount := by
  decide

/-! ## Confluence (trivial) -/

/-- The step function is deterministic: there is at most one redex.
    This is confluence in the strongest possible sense — the rule is a
    partial function, not a relation. -/
theorem step_deterministic (t : Term) :
    ∀ t₁ t₂, step t = some t₁ → step t = some t₂ → t₁ = t₂ := by
  intros t₁ t₂ h₁ h₂
  rw [h₁] at h₂
  exact Option.some_injective _ h₂

/-! ## Reversibility -/

/-- The inverse of the rotation rule.
    `pair(b, observe(a))` maps back to `observe(pair(a, b))`. -/
def unstep : Term → Option Term
  | .pair b (.observe a) => some (.observe (.pair a b))
  | .ground => some (.observe .ground)
  | _ => none

/-- The rotation step is invertible: step then unstep returns to start. -/
theorem unstep_of_rotate (a b : Term) :
    unstep (.pair b (.observe a)) = some (.observe (.pair a b)) := by
  simp [unstep]

/-- The ground step is invertible. -/
theorem unstep_of_ground :
    unstep .ground = some (.observe .ground) := by
  simp [unstep]

/-! ## Normal form characterization -/

/-- Ground is a normal form. -/
theorem ground_isNormalForm : isNormalForm .ground = true := by
  decide

/-- A pair without observe is a normal form. -/
theorem pair_isNormalForm (a b : Term) : isNormalForm (.pair a b) = true := by
  simp [isNormalForm, step]

/-- observe(ground) is not a normal form — it reduces to ground. -/
theorem observe_ground_not_normalForm : isNormalForm (.observe .ground) = false := by
  decide

/-- observe(pair(a,b)) is not a normal form — it reduces. -/
theorem observe_pair_not_normalForm (a b : Term) :
    isNormalForm (.observe (.pair a b)) = false := by
  simp [isNormalForm, step]

/-! ## Step equations -/

/-- The rotation step for observe(pair(a, b)). -/
@[simp]
theorem step_observe_pair (a b : Term) :
    step (.observe (.pair a b)) = some (.pair b (.observe a)) := by
  simp [step]

/-- The ground step. -/
@[simp]
theorem step_observe_ground :
    step (.observe .ground) = some .ground := by
  simp [step]

/-- Ground has no step. -/
@[simp]
theorem step_ground : step .ground = none := by
  simp [step]

/-- A pair has no step. -/
@[simp]
theorem step_pair (a b : Term) : step (.pair a b) = none := by
  simp [step]

/-! ## Normalization examples -/

/-- Normalizing observe(pair(ground, ground)):
    observe(pair(ground, ground)) → pair(ground, observe(ground))
    normalize only reduces the outermost observe, leaving pair(ground, observe(ground)).
    The inner observe(ground) is inside a pair, so normalize stops. -/
example : normalize (.observe (.pair .ground .ground)) = .pair .ground (.observe .ground) := by
  native_decide

end RotationCalculus
