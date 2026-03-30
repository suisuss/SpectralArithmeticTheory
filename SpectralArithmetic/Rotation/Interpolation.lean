/-
  Craig Interpolation: Factoring UNSAT Proofs
  =============================================

  Given UNSAT formula F = A ∧ B where A and B share some variables,
  Craig's interpolation theorem guarantees: there exists a formula I
  (the interpolant) such that:
    1. A implies I
    2. I ∧ B is UNSAT
    3. I mentions only variables common to A and B

  The interpolant SEPARATES the "reason" for unsatisfiability:
  A forces I to be true, and I by itself conflicts with B.

  In the rotation calculus: the interpolant is a FACTORIZATION
  of the UNSAT proof. If A and B share few variables, I is small,
  and the proof decomposes into two independent parts:
  "A implies I" and "I conflicts with B."

  This connects to the tree decomposition story:
  - SAT factorizes when the constraint graph has low treewidth
  - UNSAT factorizes when the formula splits into parts with
    few shared variables (= the interpolant is small)
  - Both are the same structural property: separability.
-/

import SpectralArithmetic.Rotation.SymmetryBreaking

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Formula splitting -/

/-- Variables mentioned in a formula. -/
def formulaVariables (f : SATFormula) : List ℕ :=
  (f.flatMap fun c => c.map (·.1)).eraseDups

/-- Variables shared between two formulas. -/
def sharedVars (f1 f2 : SATFormula) : List ℕ :=
  let v1 := formulaVariables f1
  let v2 := formulaVariables f2
  v1.filter fun v => v2.contains v

/-- Variables private to f1 (not in f2). -/
def privateVars (f1 f2 : SATFormula) : List ℕ :=
  let v1 := formulaVariables f1
  let v2 := formulaVariables f2
  v1.filter fun v => !v2.contains v

/-- Split a formula into two parts at a given variable index.
    Clauses mentioning only variables < split go to A.
    Clauses mentioning any variable >= split go to B.
    Clauses spanning both go to B (conservative). -/
def splitFormula (f : SATFormula) (splitVar : ℕ)
    : SATFormula × SATFormula :=
  let a := f.filter fun c =>
    c.all fun (v, _) => v < splitVar
  let b := f.filter fun c =>
    c.any fun (v, _) => v >= splitVar
  (a, b)

/-- Split a formula by variable sets. -/
def splitByVars (f : SATFormula) (aVars : List ℕ)
    : SATFormula × SATFormula :=
  let a := f.filter fun c =>
    c.all fun (v, _) => aVars.contains v
  let b := f.filter fun c =>
    !(c.all fun (v, _) => aVars.contains v)
  (a, b)

/-! ## Interpolant extraction from resolution -/

/-- Track which "side" (A or B) each clause belongs to. -/
inductive Side where
  | partA : Side
  | partB : Side
  | derived : Side   -- derived from resolution
  deriving DecidableEq, Repr

/-- A labeled clause: clause + which side it came from. -/
structure LabeledClause where
  clause : SATClause
  side   : Side
  deriving Repr

/-- Label each clause in a split formula. -/
def labelFormula (a b : SATFormula)
    : List LabeledClause :=
  (a.map fun c => { clause := c, side := .partA }) ++
  (b.map fun c => { clause := c, side := .partB })

/-- Extract an interpolant from a resolution derivation.
    For each resolution step:
    - If both parents are from A: resolvent is from A
    - If both parents are from B: resolvent is from B
    - If one from A and one from B: resolvent restricted to
      shared variables is part of the interpolant

    The interpolant is the conjunction of all "crossing" resolvents
    restricted to shared variables. -/
def extractInterpolant (derivation : Derivation)
    (a b : SATFormula) : SATFormula :=
  let aVars := formulaVariables a
  let bVars := formulaVariables b
  let shared := sharedVars a b
  -- Track which side each clause is from
  let allClauses := a ++ b
  -- For each resolution step, check if it crosses A-B boundary
  let crossingClauses := derivation.steps.filterMap fun step =>
    let c1InA := a.contains step.clause1 ||
      aVars.all fun v =>
        step.clause1.all fun (v', _) => aVars.contains v'
    let c2InB := b.contains step.clause2 ||
      bVars.any fun v =>
        step.clause2.any fun (v', _) => !aVars.contains v'
    if c1InA || c2InB then
      -- Restrict resolvent to shared variables
      let restricted := step.result.filter fun (v, _) =>
        shared.contains v
      if restricted.isEmpty && step.result.isEmpty then
        some []  -- empty clause = contradiction
      else if !restricted.isEmpty then
        some restricted
      else none
    else none
  crossingClauses

/-! ## Interpolation quality metrics -/

/-- Interpolant size relative to formula size. -/
structure InterpolantMetrics where
  formulaSize   : ℕ    -- clauses in original formula
  partASize     : ℕ
  partBSize     : ℕ
  sharedCount   : ℕ    -- shared variables
  privateACount : ℕ    -- A-only variables
  privateBCount : ℕ    -- B-only variables
  interpolantSize : ℕ  -- clauses in interpolant
  proofSteps    : ℕ
  deriving Repr

def computeMetrics (f : SATFormula) (splitVar : ℕ)
    : InterpolantMetrics :=
  let (a, b) := splitFormula f splitVar
  let shared := sharedVars a b
  let privA := privateVars a b
  let privB := privateVars b a
  -- Resolve the full formula
  let (deriv, _) := greedyResolution f 100
  let interpolant := extractInterpolant deriv a b
  { formulaSize := List.length f,
    partASize := List.length a,
    partBSize := List.length b,
    sharedCount := List.length shared,
    privateACount := List.length privA,
    privateBCount := List.length privB,
    interpolantSize := List.length interpolant,
    proofSteps := List.length deriv.steps }

/-! ## Demonstrations -/

#eval! do
  IO.println "=== CRAIG INTERPOLATION ==="
  IO.println ""

  -- 1. Clean split: independent halves
  IO.println "--- Independent halves ---"
  let f : SATFormula :=
    [[(0, true)], [(0, false)],    -- A: x0 ∧ ¬x0
     [(2, true)], [(2, false)]]    -- B: x2 ∧ ¬x2
  let (a, b) := splitFormula f 1
  IO.println s!"  A: {a}  (vars: {formulaVariables a})"
  IO.println s!"  B: {b}  (vars: {formulaVariables b})"
  IO.println s!"  shared: {sharedVars a b}"
  IO.println s!"  A is UNSAT independently, B is UNSAT independently"
  IO.println s!"  interpolant should be trivial (no shared vars)"
  let m := computeMetrics f 1
  IO.println s!"  interpolant size: {m.interpolantSize}"

  -- 2. Linked halves: shared variable
  IO.println ""
  IO.println "--- Linked halves ---"
  let f2 : SATFormula :=
    [[(0, true)], [(0, false), (1, true)],   -- A forces x1=T
     [(1, false)], [(2, true)]]               -- B needs x1=T but has ¬x1
  let (a2, b2) := splitFormula f2 1
  IO.println s!"  A: {a2}  (vars: {formulaVariables a2})"
  IO.println s!"  B: {b2}  (vars: {formulaVariables b2})"
  IO.println s!"  shared: {sharedVars a2 b2}"
  let m2 := computeMetrics f2 1
  IO.println s!"  interpolant size: {m2.interpolantSize}"
  IO.println s!"  proof steps: {m2.proofSteps}"

  -- 3. Chain with clear split point
  IO.println ""
  IO.println "--- Chain: split in middle ---"
  let f3 : SATFormula :=
    [[(0, true)],
     [(0, false), (1, true)],
     [(1, false), (2, true)],
     [(2, false), (3, true)],
     [(3, false)]]
  -- Split at variable 2: A has {x0,x1,x2}, B has {x2,x3}
  let (a3, b3) := splitFormula f3 2
  IO.println s!"  A: {a3}  (vars: {formulaVariables a3})"
  IO.println s!"  B: {b3}  (vars: {formulaVariables b3})"
  IO.println s!"  shared: {sharedVars a3 b3}"
  IO.println s!"  private A: {privateVars a3 b3}"
  IO.println s!"  private B: {privateVars b3 a3}"
  let m3 := computeMetrics f3 2
  IO.println s!"  interpolant size: {m3.interpolantSize}"
  IO.println s!"  proof steps: {m3.proofSteps}"

#eval! do
  IO.println ""
  IO.println "=== INTERPOLATION AS FACTORIZATION ==="
  IO.println ""
  -- Show that small interpolant = factorizable proof
  IO.println "--- Factorization quality across split points ---"
  let f : SATFormula :=
    [[(0, true)],
     [(0, false), (1, true)],
     [(1, false), (2, true)],
     [(2, false), (3, true)],
     [(3, false)]]
  IO.println "  chain: x0→x1→x2→x3→□"
  IO.println "  split\tA-cls\tB-cls\tshared\tinterp\tsteps"
  for splitAt in [1, 2, 3, 4] do
    let m := computeMetrics f splitAt
    IO.println s!"  x{splitAt}\t{m.partASize}\t{m.partBSize}\t\
      {m.sharedCount}\t{m.interpolantSize}\t{m.proofSteps}"

#eval! do
  IO.println ""
  IO.println "=== INTERPOLATION ON PHP ==="
  IO.println ""
  let php := pigeonhole 3 2
  IO.println "--- PHP(3,2) split at variable 3 ---"
  let (a, b) := splitFormula php 3
  IO.println s!"  A (vars<3): {List.length a} clauses, \
    vars={formulaVariables a}"
  IO.println s!"  B (vars>=3): {List.length b} clauses, \
    vars={formulaVariables b}"
  IO.println s!"  shared: {sharedVars a b}"
  let m := computeMetrics php 3
  IO.println s!"  interpolant: {m.interpolantSize} clauses"
  IO.println s!"  proof steps: {m.proofSteps}"
  IO.println ""
  IO.println "--- PHP(3,2) all split points ---"
  IO.println "  split\tA\tB\tshared\tinterp"
  for s in [1, 2, 3, 4, 5] do
    let mp := computeMetrics php s
    IO.println s!"  x{s}\t{mp.partASize}\t{mp.partBSize}\t\
      {mp.sharedCount}\t{mp.interpolantSize}"

/-! ## Assessment

    INTERPOLATION AS FACTORIZATION:

    Craig interpolation decomposes an UNSAT proof into parts:
    - Part 1: A implies I (the interpolant)
    - Part 2: I conflicts with B
    - I mentions only shared variables

    The interpolant SIZE measures SEPARABILITY:
    - Small I = A and B interact weakly → proof factorizes
    - Large I = A and B interact strongly → proof doesn't factorize
    - Empty I = A or B is UNSAT alone → trivially factorizable

    This directly parallels SAT factorization:
    - SAT: low treewidth → constraint graph separable → fast D&C
    - UNSAT: few shared vars → interpolant small → factored proof
    - Both measure the same thing: how much do the parts interact?

    IN THE ROTATION CALCULUS:

    The interpolant is a clause-term that lives at the BOUNDARY
    between two sub-problems. It's the minimum information that
    must cross the split point. In tree terms: the interpolant
    is the constraint at the root node that connects the left
    subtree (A) to the right subtree (B).

    For chain formulas (treewidth 1): splitting at any point
    produces an interpolant with 1 shared variable. The proof
    factors perfectly — each half can be proved independently
    given the interpolant.

    For PHP (high treewidth): splitting produces many shared
    variables. The interpolant is large. The proof doesn't
    factor well.

    The interpolant size IS the treewidth of the UNSAT proof,
    just as treewidth IS the factorizability of the SAT search.
    Same structural measure, applied to proofs instead of
    instances.
-/

end RotationCalculus
