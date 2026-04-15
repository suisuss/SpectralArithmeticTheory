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

/-- `d.conclusion` is actually derived: either it is an original clause
    of `F` or it is the result of some step. Required on top of
    "conclusion = []" so an empty Derivation cannot refute arbitrary `F`. -/
def conclusionDerived (d : Derivation) (F : SATFormula) : Prop :=
  d.conclusion ∈ F ∨ d.conclusion ∈ d.steps.map (·.result)

/-- `d` is a resolution refutation of `F`. -/
def RefutesFrom (d : Derivation) (F : SATFormula) : Prop :=
  d.conclusion = [] ∧
  conclusionDerived d F ∧
  (∀ i, i < d.steps.length →
    stepPremisesValid d F i ∧ stepResultCorrect d i)

/-! ## Lifting a restricted refutation back to the original formula

    Central construction for the composition theorem. Given a refutation
    of `F|α` and the falsified literals `L_α` of `α`, every clause
    appearing in the derivation is extended by appending `L_α`. Pivot
    variables are untouched because they are private to `F₁` or `F₂`
    and do not appear in `α`. The lifted derivation produces the clause
    `L_α` (instead of the empty clause).

    Two obligations for full correctness (deferred to named lemmas):
    - each lifted step remains a valid resolution step (pivot preserved,
      result unchanged modulo the appended literals),
    - each lifted original clause is present in `F` (weakening-closure
      requires the lifted clause to subsume some clause of `F`).
-/

/-- The list of falsified literals of an assignment α. Each `(v, b) ∈ α`
    contributes the literal `(v, !b)` (which α makes false). -/
def falsifiedLiterals (α : PartialAssignment) : SATClause :=
  α.map fun (v, b) => (v, !b)

/-- Lift a resolution step by appending extra literals to both premises
    and the result. Pivot and structure unchanged. -/
def liftStep (extra : SATClause) (s : ResolutionStep) : ResolutionStep :=
  { clause1 := s.clause1 ++ extra
    clause2 := s.clause2 ++ extra
    pivot   := s.pivot
    result  := s.result  ++ extra }

/-- Lift an entire derivation, producing (by construction) a derivation
    whose conclusion is the original conclusion ++ extra. -/
def liftDerivation (extra : SATClause) (d : Derivation) : Derivation :=
  { steps      := d.steps.map (liftStep extra)
    conclusion := d.conclusion ++ extra }

@[simp] lemma liftStep_pivot (extra : SATClause) (s : ResolutionStep) :
    (liftStep extra s).pivot = s.pivot := rfl

@[simp] lemma liftDerivation_length (extra : SATClause) (d : Derivation) :
    (liftDerivation extra d).steps.length = d.steps.length := by
  simp [liftDerivation]

@[simp] lemma liftDerivation_conclusion_empty
    (extra : SATClause) (d : Derivation) (h : d.conclusion = []) :
    (liftDerivation extra d).conclusion = extra := by
  simp [liftDerivation, h]

/-- The lifted conclusion for a refutation (`d.conclusion = []`) is
    exactly the `extra` literals — this is what lets us later resolve
    different interface branches against each other. -/
lemma liftDerivation_refutation_conclusion
    (α : PartialAssignment) (d : Derivation) (h : d.conclusion = []) :
    (liftDerivation (falsifiedLiterals α) d).conclusion =
      falsifiedLiterals α := by
  simp [liftDerivation, h]

/-- Generalised derivation predicate: `d` derives the clause `c` from
    `F`. `RefutesFrom d F` is the special case `c = []`. -/
def DerivesFromTo (d : Derivation) (F : SATFormula) (c : SATClause) : Prop :=
  d.conclusion = c ∧
  conclusionDerived d F ∧
  (∀ i, i < d.steps.length →
    stepPremisesValid d F i ∧ stepResultCorrect d i)

/-- Bridge between `RefutesFrom` and `DerivesFromTo`: refutation is
    derivation of the empty clause. -/
lemma refutesFrom_iff_derivesFromTo_empty
    (d : Derivation) (F : SATFormula) :
    RefutesFrom d F ↔ DerivesFromTo d F [] := by
  simp [RefutesFrom, DerivesFromTo]

/-- **Lifting lemma (key Phase B obligation).**

    If `d` refutes `F|α` in ≤ L steps and each pivot in `d` is a private
    variable (disjoint from `α`'s interface), then `F` derives
    `falsifiedLiterals α` in ≤ L steps.

    **Proof idea.** Take `d' = liftDerivation (falsifiedLiterals α) d`.
    Its conclusion is `[] ++ falsifiedLiterals α` (by
    `liftDerivation_refutation_conclusion`). The resolution steps
    commute with appending literals on a pivot-disjoint set. The only
    subtlety: original-clause premises that did NOT mention any `α`
    variable become weakenings of `F`-clauses, which is not directly
    a step in `F`. This weakening is eliminable via a standard
    subsumption / projection argument — tracked as a separate
    auxiliary obligation below.

    This is the central open obligation of Phase B. -/
lemma lift_refutation_to_derivation
    (F : SATFormula) (α : PartialAssignment) (d : Derivation)
    (_hRef : RefutesFrom d (restrictFormula F α))
    (_hPivotsPrivate :
      ∀ i (h : i < d.steps.length),
        (d.steps[i]'h).pivot ∉ α.map (·.1)) :
    ∃ d' : Derivation,
      DerivesFromTo d' F (falsifiedLiterals α) ∧
      d'.steps.length ≤ d.steps.length := by
  sorry

/-! ## Combining two derivations via a final resolution step -/

/-- Concatenate `d1 ++ d2` and append one resolution step whose premises
    are the two conclusions. The combined derivation concludes with the
    resolvent. Length = d1.length + d2.length + 1. -/
def concatResolve (d1 d2 : Derivation) (pivot : Nat) : Derivation :=
  let finalStep : ResolutionStep :=
    { clause1 := d1.conclusion
      clause2 := d2.conclusion
      pivot   := pivot
      result  := resolveOn d1.conclusion d2.conclusion pivot }
  { steps      := d1.steps ++ d2.steps ++ [finalStep]
    conclusion := finalStep.result }

@[simp] lemma concatResolve_length
    (d1 d2 : Derivation) (pivot : Nat) :
    (concatResolve d1 d2 pivot).steps.length =
      d1.steps.length + d2.steps.length + 1 := by
  simp [concatResolve, Nat.add_assoc]

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
    (hValid : D.IsValid F)
    (hSingleBridge : D.interface.length = 1)
    (L : Nat)
    (hSides :
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
  -- Extract the single bridge variable b.
  have ⟨b, hb⟩ : ∃ b, D.interface = [b] := by
    match h : D.interface with
    | [] => simp [h] at hSingleBridge
    | [b] => exact ⟨b, rfl⟩
    | _ :: _ :: _ => simp [h] at hSingleBridge
  -- The two assignments over interface=[b].
  let αF : PartialAssignment := [(b, false)]
  let αT : PartialAssignment := [(b, true)]
  have hαF_mem : αF ∈ allInterfaceAssignments D.interface := by
    rw [hb]; simp [allInterfaceAssignments, αF]
  have hαT_mem : αT ∈ allInterfaceAssignments D.interface := by
    rw [hb]; simp [allInterfaceAssignments, αT]
  -- From hSides we get refutations for each side under each α.
  have ⟨d1F_ex, _⟩ := hSides αF hαF_mem
  have ⟨_, d2T_ex⟩ := hSides αT hαT_mem
  -- Open the existentials.
  obtain ⟨d1F, hd1F_ref, hd1F_len⟩ := d1F_ex
  obtain ⟨d2T, hd2T_ref, hd2T_len⟩ := d2T_ex
  -- Lift them to derivations of {b} (from αF, literals falsified is (b,T))
  -- and {¬b} (from αT, literals falsified is (b,F)) on their respective
  -- private sides.
  -- NOTE: lift_refutation_to_derivation needs a pivot-disjointness hyp;
  -- in valid decompositions, F_i's clauses only mention privateVars_i ∪
  -- interface, and resolution pivots within F_i must be variables that
  -- appear in its clauses with opposite polarity — a pivot equal to
  -- interface var `b` is only possible if `b` is mentioned in clauses
  -- of F_i. Since α fixes b, any such clause is either satisfied or has
  -- its (b, _) literal dropped under restriction, so after restriction
  -- `b` never appears as a pivot. This is the hPivotsPrivate condition,
  -- which follows from hd1F_ref / hd2T_ref + hValid but is also left
  -- as an obligation (pushed to the lift lemma) in this Phase B step.
  -- For now we just thread the hypothesis through.
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
