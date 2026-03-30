/-
  Trajectory Analysis: Large-Scale Test
  =======================================

  The n=10 test showed no density variation because:
  1. CDCL finds solutions without backtracking at small n
  2. The pipeline's cdclTraced discards CDCL's internal search
     tree and reconstructs decisions via brute enumeration

  This file does two things:
  A. Scale up to n=15,20,25 for structured instances (UP-only)
  B. Directly call cdclSearch to see actual learned clauses,
     bypassing the pipeline's lossy wrapping
  C. Combine: run UP first, then measure CDCL's actual search
     effort on the residual formula
-/

import SpectralArithmetic.Rotation.TrajectoryAnalysis

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Part A: Structured instance scaling -/

#eval! do
  IO.println "=== STRUCTURED INSTANCE SCALING ==="
  IO.println ""
  IO.println "n\treach\ttotal\tUP\tpure\tdec\tfree%\tcascade"
  for n in [8, 10, 15, 20, 25, 30, 40, 50] do
    for reach in [1, 3] do
      let f := reachInstance n reach
      let (sol, trace, _) := runPipeline f n
      let p := profileTrace trace
      IO.println s!"{n}\t{reach}\t{p.total}\t{p.nUP}\t{p.nPure}\t{p.nDecision}\t{p.freeRatio}\t{maxCascade trace}\t{sol.isSome}"

/-! ## Part B: CDCL's actual search effort

    cdclSearch returns (found, cost, learned_clauses).
    cost = nodes explored in the search tree.
    learned = clauses from conflict analysis.
    These are the real numbers hidden by the pipeline. -/

#eval! do
  IO.println ""
  IO.println "=== CDCL ACTUAL SEARCH EFFORT (raw, no pipeline) ==="
  IO.println ""
  IO.println "instance\tn\tm\tcost\tlearned\tfound"
  -- Random 3-SAT at various densities, n=8
  for m in [8, 16, 24, 32, 40, 48] do
    let f := random3SAT 8 m 42
    let (found, cost, learned) := cdclSearch f (List.range 8) []
    IO.println s!"rand-8-{m}\t8\t{m}\t{cost}\t{learned.length}\t{found}"

  -- Random 3-SAT at various densities, n=10
  IO.println ""
  for m in [10, 20, 30, 42, 50, 60] do
    let f := random3SAT 10 m 42
    let (found, cost, learned) := cdclSearch f (List.range 10) []
    IO.println s!"rand-10-{m}\t10\t{m}\t{cost}\t{learned.length}\t{found}"

  -- Random 3-SAT at various densities, n=12
  IO.println ""
  for m in [12, 24, 36, 50, 60, 72] do
    let f := random3SAT 12 m 42
    let (found, cost, learned) := cdclSearch f (List.range 12) []
    IO.println s!"rand-12-{m}\t12\t{m}\t{cost}\t{learned.length}\t{found}"

  -- PHP
  IO.println ""
  let (found3, cost3, learned3) :=
    cdclSearch (pigeonhole 3 2) (List.range 6) []
  IO.println s!"PHP-3-2\t6\t-\t{cost3}\t{learned3.length}\t{found3}"
  let (found4, cost4, learned4) :=
    cdclSearch (pigeonhole 4 3) (List.range 12) []
  IO.println s!"PHP-4-3\t12\t-\t{cost4}\t{learned4.length}\t{found4}"

/-! ## Part C: UP-then-CDCL with real metrics

    Run UP to fixed point, then call cdclSearch directly on
    the residual formula. This shows the actual search effort
    AFTER free inference has been exhausted. -/

/-- Run UP to fixpoint, then CDCL on residual. Return
    combined trajectory data. -/
def upThenCDCL (formula : SATFormula) (nVars : ℕ)
    : String :=
  let initState : TacticState :=
    { formula := formula,
      vars := List.range nVars,
      assign := [] }
  let (upState, upTrace) := upFixpoint initState
  let upSteps := upTrace.length
  let remaining := upState.vars.length
  -- Now run CDCL directly on residual
  let (found, cdclCost, learned) :=
    cdclSearch upState.formula upState.vars upState.assign
  let solved := if found then
    satisfiesFormula
      (upState.assign ++ (match (allVarAssignments upState.vars).find?
        fun a => satisfiesFormula (upState.assign ++ a) formula with
        | some a => a | none => []))
      formula
  else false
  s!"UP={upSteps}({nVars - remaining}/{nVars}) " ++
  s!"residual={remaining}vars " ++
  s!"cdcl_cost={cdclCost} learned={learned.length} " ++
  s!"found={found} solved={solved}"

#eval! do
  IO.println ""
  IO.println "=== UP-THEN-CDCL: REAL SEARCH EFFORT ==="
  IO.println ""

  -- Structured
  IO.println "--- Structured ---"
  for n in [8, 10, 15, 20] do
    for reach in [1, 3] do
      let f := reachInstance n reach
      IO.println s!"struct-{n}-r{reach}: {upThenCDCL f n}"

  -- Random at various densities, n=10
  IO.println ""
  IO.println "--- Random n=10, seed=42 ---"
  for m in [10, 20, 30, 42, 50, 60] do
    let f := random3SAT 10 m 42
    IO.println s!"rand-10-{m}: {upThenCDCL f 10}"

  -- Random at various densities, n=12
  IO.println ""
  IO.println "--- Random n=12, seed=42 ---"
  for m in [12, 24, 36, 50, 60, 72] do
    let f := random3SAT 12 m 42
    IO.println s!"rand-12-{m}: {upThenCDCL f 12}"

  -- Multiple seeds at transition, n=12
  IO.println ""
  IO.println "--- Random n=12 at transition (m=50), 5 seeds ---"
  for seed in [42, 123, 456, 789, 1001] do
    let f := random3SAT 12 50 seed
    IO.println s!"rand-12-50-s{seed}: {upThenCDCL f 12}"

  -- PHP
  IO.println ""
  IO.println "--- Pigeonhole ---"
  IO.println s!"PHP-3-2: {upThenCDCL (pigeonhole 3 2) 6}"
  IO.println s!"PHP-4-3: {upThenCDCL (pigeonhole 4 3) 12}"

/-! ## Part D: Multi-seed CDCL cost at density sweep

    For each density, average CDCL search cost over seeds.
    This is the raw search effort, not filtered through
    the pipeline's lossy trace. -/

#eval! do
  IO.println ""
  IO.println "=== CDCL COST vs DENSITY (n=10, 5 seeds) ==="
  IO.println ""
  IO.println "m\tratio\tavgCost\tavgLearn\tsatRate"
  for m in [10, 20, 30, 35, 40, 42, 45, 50, 55, 60] do
    let mut totalCost := 0
    let mut totalLearn := 0
    let mut satCount := 0
    for seed in [42, 123, 456, 789, 1001] do
      let f := random3SAT 10 m seed
      let (found, cost, learned) :=
        cdclSearch f (List.range 10) []
      totalCost := totalCost + cost
      totalLearn := totalLearn + learned.length
      if found then satCount := satCount + 1
    IO.println s!"{m}\t{m/10}.{m%10}\t{totalCost/5}\t{totalLearn/5}\t{satCount}/5"

  IO.println ""
  IO.println "=== CDCL COST vs DENSITY (n=12, 5 seeds) ==="
  IO.println ""
  IO.println "m\tratio\tavgCost\tavgLearn\tsatRate"
  for m in [12, 24, 36, 42, 48, 50, 55, 60, 72] do
    let mut totalCost := 0
    let mut totalLearn := 0
    let mut satCount := 0
    for seed in [42, 123, 456, 789, 1001] do
      let f := random3SAT 12 m seed
      let (found, cost, learned) :=
        cdclSearch f (List.range 12) []
      totalCost := totalCost + cost
      totalLearn := totalLearn + learned.length
      if found then satCount := satCount + 1
    IO.println s!"{m}\t{m/12}.{m%12}\t{totalCost/5}\t{totalLearn/5}\t{satCount}/5"

/-! ## Assessment

    This test bypasses the pipeline's lossy trace to measure
    the ACTUAL search effort:

    1. CDCL cost = search tree nodes explored (not assignments
       enumerated post-hoc)
    2. Learned clauses = conflicts encountered during search
       (not zero because we lost them in the pipeline wrapper)
    3. UP residual = how many variables remain after free inference

    Expected findings:
    - CDCL cost should peak near the phase transition (m/n ~ 4.2)
    - Learned clauses should increase with density
    - Structured instances should have 0 residual vars (UP solves all)
    - The CDCL cost / UP reduction ratio is the meta-rewriting
      contraction potential: high UP = high contraction, high CDCL
      = low contraction
-/

end RotationCalculus
