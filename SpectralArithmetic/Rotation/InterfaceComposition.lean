/-
  Interface Composition for Resolution Refutations (issue #45)
  ============================================================

  Modular SAT formulas admit short refutations when the inter-cluster
  interface is small. This file formalises the core composition lemma.

  Theorem (Interface Composition).
    Let F = F₁ ∪ F₂ where
      - F₁ uses only variables in (privateVars1 ∪ interface),
      - F₂ uses only variables in (privateVars2 ∪ interface),
      - privateVars1 ∩ privateVars2 = ∅.
    For each truth assignment α : interface → Bool, write F_i|α for
    the formula obtained by restricting F_i under α (drop satisfied
    clauses, drop falsified literals from the rest). If every F_i|α
    admits a resolution refutation of length ≤ L, then F admits a
    resolution refutation of length ≤ 2^|interface| · (2·L + 1).

  Why this matters for #45. For a chain of k clusters joined by a single
  bridge variable, |interface| = 1 between adjacent clusters, so the
  per-interface factor is constant (≤ 6). Recursing along the chain
  gives a resolution refutation of length poly(k) · 2^O(n) for Tseitin
  on chain-of-K_n — matching what solvers *should* find on modular
  instances and refuting the 2^Ω(k) lower-bound framing in #45.

  Phase A (this file): definitions + theorem statement. Proofs are `sorry`.
  Phase B: discharge the main theorem.
  Phase C: instantiate on chain-of-K_n modular Tseitin.
-/

import SpectralArithmetic.Rotation.Resolution
import SpectralArithmetic.Rotation.SATEncoding

set_option linter.style.longLine false

namespace RotationCalculus

open Term

/-! ## Interface decomposition -/

/-- A decomposition of a CNF formula into two sides sharing a variable
    interface. The private variable sets are disjoint; the interface is
    the shared boundary across which resolution must cross. -/
structure InterfaceDecomposition where
  formula1     : SATFormula
  formula2     : SATFormula
  interface    : List Nat
  privateVars1 : List Nat
  privateVars2 : List Nat
  deriving Repr

namespace InterfaceDecomposition

/-- Variables appearing in a single clause. -/
def clauseVars (c : SATClause) : List Nat := c.map (·.1)

/-- All variables of a formula (with duplicates). -/
def formulaVarsAll (F : SATFormula) : List Nat := F.flatMap clauseVars

/-- A clause is "on side 1" if every variable it mentions is either
    private to side 1 or on the interface. -/
def clauseOnSide1 (D : InterfaceDecomposition) (c : SATClause) : Prop :=
  ∀ v ∈ clauseVars c, v ∈ D.privateVars1 ∨ v ∈ D.interface

def clauseOnSide2 (D : InterfaceDecomposition) (c : SATClause) : Prop :=
  ∀ v ∈ clauseVars c, v ∈ D.privateVars2 ∨ v ∈ D.interface

/-- `D` is a valid decomposition of `F`. -/
def IsValid (D : InterfaceDecomposition) (F : SATFormula) : Prop :=
  (F = D.formula1 ++ D.formula2) ∧
  (∀ c ∈ D.formula1, D.clauseOnSide1 c) ∧
  (∀ c ∈ D.formula2, D.clauseOnSide2 c) ∧
  (∀ v, v ∈ D.privateVars1 → v ∉ D.privateVars2)

end InterfaceDecomposition

/-! ## Restriction of a formula under a partial assignment -/

/-- A partial assignment to variables. Each entry fixes one variable
    to a truth value. We do not assume completeness on any particular
    variable set. -/
abbrev PartialAssignment := List (Nat × Bool)

/-- Literal (v, p) is satisfied by assignment α iff α assigns v the value p. -/
def literalSat (α : PartialAssignment) (lit : Nat × Bool) : Bool :=
  α.any (fun (u, q) => u == lit.1 && q == lit.2)

/-- Literal (v, p) is falsified by α iff α assigns v the opposite value. -/
def literalFals (α : PartialAssignment) (lit : Nat × Bool) : Bool :=
  α.any (fun (u, q) => u == lit.1 && q != lit.2)

/-- Restrict a formula under α:
    - drop clauses containing a satisfied literal,
    - drop falsified literals from the rest. -/
def restrictFormula (F : SATFormula) (α : PartialAssignment) : SATFormula :=
  F.filterMap fun clause =>
    if clause.any (literalSat α) then none
    else some (clause.filter fun lit => !literalFals α lit)

/-! ## Enumerating interface assignments -/

/-- All 2^|B| truth assignments to the variables in B. -/
def allInterfaceAssignments : List Nat → List PartialAssignment
  | [] => [[]]
  | v :: rest =>
    let tail := allInterfaceAssignments rest
    tail.flatMap fun α => [(v, false) :: α, (v, true) :: α]

/-! ## Refutation-from-formula predicate

    A `Derivation` is a refutation of `F` if:
      - its conclusion is the empty clause,
      - each step's two premises are drawn either from `F` or from the
        results of earlier steps in the same derivation,
      - each step's `result` is the correct resolvent of its premises
        on the given pivot.
-/

/-- Premises of step `i` in `d` come from F or earlier results. -/
def stepPremisesValid (d : Derivation) (F : SATFormula) (i : Nat) : Prop :=
  match d.steps[i]? with
  | none => True
  | some step =>
    let prev := (d.steps.take i).map (·.result)
    ((step.clause1 ∈ F) ∨ (step.clause1 ∈ prev)) ∧
    ((step.clause2 ∈ F) ∨ (step.clause2 ∈ prev))

/-- Step `i`'s result equals `resolveOn` applied to its premises on its pivot. -/
def stepResultCorrect (d : Derivation) (i : Nat) : Prop :=
  match d.steps[i]? with
  | none => True
  | some step => step.result = resolveOn step.clause1 step.clause2 step.pivot

/-- `d` is a resolution refutation of `F`. -/
def RefutesFrom (d : Derivation) (F : SATFormula) : Prop :=
  d.conclusion = [] ∧
  (∀ i, i < d.steps.length →
    stepPremisesValid d F i ∧ stepResultCorrect d i)

/-! ## The composition theorem (statement only — Phase A) -/

/-- Shorthand: the length of a derivation. -/
def Derivation.length (d : Derivation) : Nat := d.steps.length

/-- **Theorem (Interface Composition) — Phase A statement.**

    Let D be a valid interface decomposition of F. Suppose for every
    truth assignment α over D.interface there exist resolution
    refutations of F₁|α and F₂|α, each of length at most L. Then there
    exists a resolution refutation of F of length at most
    `2^|interface| · (2·L + 1)`.

    The `+ 1` per assignment covers the case-split/merge step that
    combines the two refutations under that interface branch. -/
theorem interfaceComposition_length
    (F : SATFormula)
    (D : InterfaceDecomposition)
    (_hValid : D.IsValid F)
    (L : Nat)
    (_hSides :
      ∀ α ∈ allInterfaceAssignments D.interface,
        (∃ d1 : Derivation,
           RefutesFrom d1 (restrictFormula D.formula1 α) ∧
           d1.length ≤ L) ∧
        (∃ d2 : Derivation,
           RefutesFrom d2 (restrictFormula D.formula2 α) ∧
           d2.length ≤ L))
    : ∃ d : Derivation,
        RefutesFrom d F ∧
        d.length ≤ 2 ^ D.interface.length * (2 * L + 1) := by
  sorry

/-! ## Corollary for single-variable interfaces

    For |interface| = 1 (the chain-of-clusters single-bridge case),
    the bound simplifies to `2 · (2L + 1) = 4L + 2`, i.e. linear in L.
    This is the shape that makes chain-composition give poly(k).

    Stated separately so downstream code does not have to re-expose
    the 2^_ bookkeeping in the simple case. -/
theorem interfaceComposition_singleBridge
    (F : SATFormula)
    (D : InterfaceDecomposition)
    (_hValid : D.IsValid F)
    (_hSingleBridge : D.interface.length = 1)
    (L : Nat)
    (_hSides :
      ∀ α ∈ allInterfaceAssignments D.interface,
        (∃ d1 : Derivation,
           RefutesFrom d1 (restrictFormula D.formula1 α) ∧
           d1.length ≤ L) ∧
        (∃ d2 : Derivation,
           RefutesFrom d2 (restrictFormula D.formula2 α) ∧
           d2.length ≤ L))
    : ∃ d : Derivation,
        RefutesFrom d F ∧
        d.length ≤ 4 * L + 2 := by
  sorry

/-! ## Smoke test: definitions compute on small inputs -/

/-- Trivially UNSAT formula {x₀} ∧ {¬x₀} with trivial interface. -/
private def smokeFormula : SATFormula := [[(0, true)], [(0, false)]]

private def smokeDecomp : InterfaceDecomposition :=
  { formula1     := [[(0, true)]]
    formula2     := [[(0, false)]]
    interface    := [0]
    privateVars1 := []
    privateVars2 := [] }

#eval (allInterfaceAssignments smokeDecomp.interface).length
      -- expect 2

#eval (restrictFormula smokeDecomp.formula1 [(0, true)]).length
      -- expect 0 (clause satisfied)

#eval (restrictFormula smokeDecomp.formula1 [(0, false)]).length
      -- expect 1 (clause becomes empty — an immediate refutation of length 0)

end RotationCalculus
