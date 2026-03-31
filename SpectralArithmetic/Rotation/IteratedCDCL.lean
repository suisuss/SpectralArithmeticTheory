/-
  Iterated 1-UIP: Learn → Augment → Cascade → Repeat
  =====================================================

  The pipeline: run 1-UIP, augment the formula with learned
  clauses, run UP (with conflict detection), then iterate
  on the residual. Each round unlocks more free inference.

  First fix: UP must detect conflicting assignments (same
  variable assigned both true and false) and report UNSAT.
-/

import SpectralArithmetic.Rotation.CDCL1UIP

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## UP with conflict detection -/

/-- Result of UP with conflict detection. -/
inductive UPResult where
  | ok    : TacticState → ProofTrace → UPResult
  | conflict : ℕ → UPResult  -- conflicting variable
  deriving Repr

instance : Inhabited UPResult where
  default := .conflict 0

/-- Unit propagation that detects conflicting assignments.
    If variable v is assigned both true and false → UNSAT. -/
partial def upWithConflict (formula : SATFormula) (vars : List ℕ)
    (assign : List (ℕ × Bool)) : UPResult :=
  let units := findUnits formula
  let pures := findPureLiterals formula
    (vars.filter fun v => !assign.any fun (v', _) => v == v')
  let newUnits := units.filter fun (v, _) =>
    !assign.any fun (v', _) => v == v'
  let newPures := pures.filter fun (v, _) =>
    !assign.any fun (v', _) => v == v'
  let allNew := newUnits ++ newPures
  -- Check for conflicts: is any new assignment contradicted?
  let conflictVar := allNew.findSome? fun (v, p) =>
    if assign.any fun (v', p') => v == v' && p != p'
    then some v
    else
      -- Also check within allNew itself
      if allNew.any fun (v', p') => v == v' && p != p'
      then some v
      else none
  match conflictVar with
  | some cv => .conflict cv
  | none =>
    if allNew.isEmpty then
      -- Also check: does the formula contain the empty clause?
      if formula.any (·.isEmpty) then
        .conflict 0  -- empty clause = contradiction
      else
        .ok { formula := formula, vars := vars, assign := assign } []
    else
      let simplified := simplifyFormula formula allNew
      let newVars := vars.filter fun v =>
        !allNew.any fun (v', _) => v == v'
      let newAssign := assign ++ allNew
      -- Check for empty clause after simplification
      if simplified.any (·.isEmpty) then
        .conflict 0
      else
        upWithConflict simplified newVars newAssign

/-! ## Iterated 1-UIP pipeline -/

/-- One round: 1-UIP → augment → UP cascade.
    Returns (status, learned, cascade_size, residual). -/
def oneRound (formula : SATFormula) (vars : List ℕ)
    (assign : List (ℕ × Bool))
    : String × List SATClause × ℕ × SATFormula × List ℕ × List (ℕ × Bool) :=
  -- Run 1-UIP on current formula
  let freeVars := vars.filter fun v =>
    !assign.any fun (v', _) => v == v'
  if List.length freeVars == 0 then
    ("done", [], 0, formula, [], assign)
  else
    -- First check: is the formula SAT by naive CDCL?
    let (naiveFound, _, _) := cdclSearch formula freeVars assign
    if naiveFound then
      ("SAT", [], 0, formula, freeVars, assign)
    else
    let (_, _, learned) := satCDCL1UIP formula (List.length freeVars)
    let varMap := freeVars
    let remappedLearned := learned.map fun c =>
      c.map fun (v, p) =>
        match varMap[v]? with
        | some realV => (realV, p)
        | none => (v, p)
    let augmented := formula ++ remappedLearned
    -- UP with conflict detection
    match upWithConflict augmented freeVars assign with
    | .conflict _ =>
      ("UNSAT", remappedLearned, List.length freeVars, [], [], assign)
    | .ok state _ =>
      let cascadeSize := List.length freeVars - List.length state.vars
      ("residual", remappedLearned, cascadeSize,
       state.formula, state.vars, state.assign)

/-- The full iterated pipeline. Each round:
    1. Run 1-UIP CDCL
    2. Augment formula with learned clauses
    3. Run UP with conflict detection
    4. If UNSAT detected → done
    5. If SAT found → done
    6. If residual remains → repeat on residual -/
structure IterationLog where
  round      : ℕ
  status     : String
  learned    : ℕ
  learnedW   : List ℕ
  cascade    : ℕ
  residualV  : ℕ
  deriving Repr

def iteratedSolve (formula : SATFormula) (nVars : ℕ)
    (maxRounds : ℕ)
    : List IterationLog × Bool :=
  let rec go (f : SATFormula) (vars : List ℕ)
      (assign : List (ℕ × Bool))
      (logs : List IterationLog) (fuel : ℕ)
      : List IterationLog × Bool :=
    match fuel with
    | 0 => (logs, false)
    | fuel + 1 =>
      let (status, learned, cascade, resF, resV, resA) :=
        oneRound f vars assign
      let log : IterationLog :=
        { round := maxRounds - fuel,
          status := status,
          learned := List.length learned,
          learnedW := learned.map List.length,
          cascade := cascade,
          residualV := List.length resV }
      let newLogs := logs ++ [log]
      match status with
      | "UNSAT" => (newLogs, true)
      | "SAT" => (newLogs, false)
      | "done" => (newLogs, false)
      | _ =>  -- "residual"
        if List.length resV == 0 then
          (newLogs, false)  -- no more variables
        else if List.length resV == List.length vars then
          (newLogs, false)  -- no progress
        else
          go resF resV resA newLogs fuel
  go formula (List.range nVars) [] [] maxRounds

/-! ## Demonstrations -/

#eval! do
  IO.println "=== ITERATED 1-UIP PIPELINE ==="
  IO.println ""

  let test := fun (name : String) (f : SATFormula) (nv : ℕ) => do
    let (logs, proven) := iteratedSolve f nv 10
    IO.println s!"  {name}: proven_UNSAT={proven} rounds={List.length logs}"
    for log in logs do
      IO.println s!"    R{log.round}: {log.status} learned={log.learned} \
        widths={log.learnedW} cascade={log.cascade} \
        residual={log.residualV}vars"

  IO.println "--- Random UNSAT n=4 ---"
  for seed in [42, 123, 1001, 5555] do
    let f := random3SAT 4 20 seed
    let (sat, _) := flatBruteForce f 4
    if sat.isNone then
      test s!"rand-4-20-s{seed}" f 4

  IO.println ""
  IO.println "--- Structured ---"
  test "PHP(3,2)" (pigeonhole 3 2) 6
  test "chain-5" (chainFormula 5) 5
  test "tseitin-3" (tseitinCycle 3) 3

  IO.println ""
  IO.println "--- Random UNSAT n=6 ---"
  for seed in [42, 789, 1001] do
    let f := random3SAT 6 30 seed
    let (sat, _) := flatBruteForce f 6
    if sat.isNone then
      test s!"rand-6-30-s{seed}" f 6

  IO.println ""
  IO.println "--- Random SAT (should detect) ---"
  for seed in [456, 789] do
    let f := random3SAT 4 20 seed
    let (sat, _) := flatBruteForce f 4
    if sat.isSome then
      test s!"rand-4-20-s{seed}(SAT)" f 4

#eval! do
  IO.println ""
  IO.println "=== ITERATED vs SINGLE-ROUND ==="
  IO.println ""
  IO.println "instance\t\tnaive\t1UIP\titerated\tproven"
  for seed in [42, 123, 1001, 5555] do
    let f := random3SAT 4 20 seed
    let (sat, _) := flatBruteForce f 4
    if sat.isNone then
      let (_, costN, learnedN) := cdclSearch f (List.range 4) []
      let (_, cost1, learned1) := satCDCL1UIP f 4
      let (logs, proven) := iteratedSolve f 4 10
      let totalCost := logs.foldl (fun a (l : IterationLog) => a + l.learned + l.cascade) 0
      IO.println s!"  s{seed}\t\t\t{costN}({List.length learnedN}L)\t{cost1}({List.length learned1}L)\t{totalCost}\t{proven}"

/-! ## Assessment

    The iterated pipeline addresses the core gap:

    Round 1: 1-UIP produces short clauses (width 1-2)
    Round 1 UP: cascade resolves some variables
    Round 2: 1-UIP on RESIDUAL — the simplified formula
             may have NEW unit clauses from the cascade
    Round 2 UP: cascade resolves more variables
    ...repeat until UNSAT proven or no progress

    Each round compounds:
    - Learned clauses create UP opportunities
    - UP creates new unit clauses
    - New units create new learned clauses in the next round
    - Eventually the formula contracts to empty (UNSAT) or
      a satisfying assignment is found (SAT)

    The meta-system tracks each round's cascade depth.
    The cascade depth trajectory across rounds is the
    "learning curve" — how quickly the solver accumulates
    enough knowledge to solve the instance.

    Expected behavior:
    - Easy instances: 1 round (cascade resolves everything)
    - Medium instances: 2-3 rounds (each round unlocks more)
    - Hard instances: many rounds or no convergence
-/

end RotationCalculus
