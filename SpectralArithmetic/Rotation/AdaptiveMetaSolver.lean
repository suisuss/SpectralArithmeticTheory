/-
  Adaptive Meta-Solver: Monolithic/Composed Hybrid
  ==================================================

  Uses the meta-system's trajectory analysis to decide at runtime:
  - When to solve monolithically (long cascades → high contraction)
  - When to split and compose (short cascades → low contraction)
  - Where to split (minimize shared variables = small interpolant)

  The solver is recursive: each sub-problem gets the same
  adaptive treatment. The meta-trajectory of the full solve
  records which strategy was used at each level.
-/

import SpectralArithmetic.Rotation.ProofSystemTest

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Split point selection -/

/-- Count variables in a formula. -/
def countVars (f : SATFormula) : List ℕ :=
  (f.flatMap fun c => c.map (·.1)).eraseDups

/-- Split a formula at a variable threshold.
    Returns (A-clauses, B-clauses, shared-vars, bridge-clauses). -/
def splitAt (f : SATFormula) (threshold : ℕ)
    : SATFormula × SATFormula × List ℕ × SATFormula :=
  let a := f.filter fun c => c.all fun (v, _) => v < threshold
  let b := f.filter fun c => c.any fun (v, _) => v >= threshold
  let bridge := f.filter fun c =>
    (c.any fun (v, _) => v < threshold) &&
    (c.any fun (v, _) => v >= threshold)
  let aVars := countVars a
  let bVars := countVars b
  let shared := aVars.filter fun v => bVars.contains v
  (a, b, shared, bridge)

/-- Find the split point that minimizes shared variables. -/
def bestSplitPoint (f : SATFormula) (vars : List ℕ) : ℕ :=
  if List.length vars ≤ 2 then
    vars.head?.getD 0
  else
    let candidates := vars.drop 1 |>.dropLast
    let scored := candidates.map fun v =>
      let (_, _, shared, _) := splitAt f v
      (v, List.length shared)
    let best := scored.foldl (fun acc (v, s) =>
      match acc with
      | none => some (v, s)
      | some (_, bs) => if s < bs then some (v, s) else acc
    ) none
    match best with
    | some (v, _) => v
    | none => vars.head?.getD 0

/-! ## Adaptive solver -/

/-- Solver decision: what strategy to use. -/
inductive SolveStrategy where
  | cascade     : ℕ → SolveStrategy    -- UP solved n vars
  | split       : ℕ → SolveStrategy    -- split at variable
  | cdclFinish  : SolveStrategy         -- CDCL on residual
  | trivial     : SolveStrategy         -- already solved or empty
  deriving Repr

/-- A solve result: solution + strategy trace. -/
structure SolveResult where
  solved     : Bool
  assign     : List (ℕ × Bool)
  strategies : List SolveStrategy
  rawSteps   : ℕ
  metaEvents : ℕ
  deriving Repr

instance : Inhabited SolveResult where
  default := { solved := false, assign := [],
                strategies := [], rawSteps := 0, metaEvents := 0 }

/-- The adaptive meta-solver. -/
partial def metaSolve (formula : SATFormula) (vars : List ℕ)
    (depth : ℕ := 0) : SolveResult :=
  if List.length vars == 0 then
    -- No variables: check if formula is satisfied
    { solved := formula.all fun c => !c.isEmpty,
      assign := [],
      strategies := [.trivial],
      rawSteps := 0, metaEvents := 0 }
  else
    -- Phase 1: Monolithic UP
    let initState : TacticState :=
      { formula := formula, vars := vars, assign := [] }
    let (upState, upTrace) := upFixpoint initState
    let cascadeLen := List.length upTrace
    let remainingVars := upState.vars
    let residualRatio := if List.length vars > 0
      then List.length remainingVars * 100 / List.length vars
      else 0

    if List.length remainingVars == 0 then
      -- UP solved everything
      let ok := satisfiesFormula upState.assign formula
      { solved := ok,
        assign := upState.assign,
        strategies := [.cascade cascadeLen],
        rawSteps := cascadeLen,
        metaEvents := 1 }
    else if residualRatio ≤ 50 || List.length remainingVars ≤ 3 then
      -- Residual is small: finish with CDCL
      let (found, cdclAssign, cdclTrace) :=
        cdclSearchTraced upState.formula remainingVars upState.assign
      let cdclSteps := List.length cdclTrace
      if found then
        { solved := true,
          assign := cdclAssign,
          strategies := [.cascade cascadeLen, .cdclFinish],
          rawSteps := cascadeLen + cdclSteps,
          metaEvents := 2 }
      else
        { solved := false,
          assign := upState.assign,
          strategies := [.cascade cascadeLen, .cdclFinish],
          rawSteps := cascadeLen + cdclSteps,
          metaEvents := 2 }
    else
      -- Residual is large: try splitting
      let splitVar := bestSplitPoint upState.formula remainingVars
      let (partA, partB, shared, _) := splitAt upState.formula splitVar

      -- Solve part A recursively
      let aVars := remainingVars.filter (· < splitVar)
      let resultA := metaSolve partA aVars (depth + 1)

      -- Feed A's results into B
      let simpB := simplifyFormula partB resultA.assign
      let bVars := remainingVars.filter (· >= splitVar)
      let resultB := metaSolve simpB bVars (depth + 1)

      let combinedAssign := upState.assign ++ resultA.assign ++ resultB.assign
      let ok := satisfiesFormula combinedAssign formula

      { solved := ok,
        assign := combinedAssign,
        strategies := [.cascade cascadeLen,
          .split splitVar] ++ resultA.strategies ++ resultB.strategies,
        rawSteps := cascadeLen + resultA.rawSteps + resultB.rawSteps,
        metaEvents := 1 + resultA.metaEvents + resultB.metaEvents }

/-! ## Comparison framework -/

/-- Run all solver variants and compare. -/
def compareSolvers (name : String) (f : SATFormula) (nVars : ℕ)
    : IO Unit := do
  -- 1. Pure pipeline (monolithic)
  let (solPipe, tracePipe, _) := runPipeline f nVars
  let pMono := profileTrace tracePipe
  let msMono := buildTrajectory f nVars
  let mpMono := metaProfile msMono.trajectory
  let adaptive := metaSolve f (List.range nVars)
  let (resD, _) := greedyResolution f 500
  let resOk := resD.conclusion.isEmpty

  IO.println s!"  {name}:"
  IO.println s!"    pipeline: raw={pMono.total} meta={mpMono.totalEvents} \
    cascade={mpMono.cascadeTotal} solved={solPipe.isSome}"
  IO.println s!"    adaptive: raw={adaptive.rawSteps} meta={adaptive.metaEvents} \
    solved={adaptive.solved} strategies={repr adaptive.strategies}"
  if resOk then
    IO.println s!"    resolution: {List.length resD.steps} steps □=true"

/-! ## Demonstrations -/

#eval! do
  IO.println "=== ADAPTIVE META-SOLVER ==="
  IO.println ""

  -- Structured (should stay monolithic)
  IO.println "--- Structured (expect: monolithic cascade) ---"
  for n in [8, 10, 15, 20] do
    compareSolvers s!"struct-{n}-r3" (reachInstance n 3) n
  IO.println ""

  -- Random below transition (should cascade partially, then CDCL)
  IO.println "--- Random below transition ---"
  for seed in [42, 123] do
    compareSolvers s!"rand-10-20-s{seed}" (random3SAT 10 20 seed) 10
  IO.println ""

  -- Random at transition (should try splitting)
  IO.println "--- Random at transition ---"
  for seed in [42, 123] do
    compareSolvers s!"rand-10-42-s{seed}" (random3SAT 10 42 seed) 10
  IO.println ""

  -- Chain (monolithic cascade)
  IO.println "--- Chains ---"
  for n in [5, 8, 10] do
    compareSolvers s!"chain-{n}" (chainFormula n) n
  IO.println ""

  -- PHP (UNSAT — pipeline can't solve, resolution can)
  IO.println "--- PHP (UNSAT) ---"
  compareSolvers "PHP(3,2)" (pigeonhole 3 2) 6

#eval! do
  IO.println ""
  IO.println "=== SCALING: ADAPTIVE vs PIPELINE ==="
  IO.println ""
  IO.println "n\tpipe_raw\tpipe_meta\tadapt_raw\tadapt_meta\tadapt_strategy"
  for n in [8, 10, 12, 15, 20, 25, 30] do
    let f := reachInstance n 3
    let (_, tr, _) := runPipeline f n
    let ms := buildTrajectory f n
    let mp := metaProfile ms.trajectory
    let ad := metaSolve f (List.range n)
    let strat := match ad.strategies.head? with
      | some (.cascade k) => s!"cascade({k})"
      | some (.split v) => s!"split({v})"
      | _ => "other"
    IO.println s!"{n}\t{List.length tr}\t\t{mp.totalEvents}\t\t{ad.rawSteps}\t\t{ad.metaEvents}\t\t{strat}"

#eval! do
  IO.println ""
  IO.println "=== META ON COMPOSED ==="
  IO.println ""
  -- Show that the adaptive solver's strategy trace IS a meta-trajectory
  IO.println "--- Chain-10 adaptive decomposition ---"
  let chain := chainFormula 10
  let ad := metaSolve chain (List.range 10)
  IO.println s!"  solved: {ad.solved}"
  IO.println s!"  raw: {ad.rawSteps} meta: {ad.metaEvents}"
  IO.println s!"  strategy trace:"
  for s in ad.strategies do
    IO.println s!"    {repr s}"
  -- Compare with monolithic
  let ms := buildTrajectory chain 10
  let mp := metaProfile ms.trajectory
  IO.println s!"  monolithic meta: {mp.totalEvents} events"
  IO.println s!"  adaptive meta: {ad.metaEvents} events"

  -- Random — where splitting might help
  IO.println ""
  IO.println "--- Random n=10 m=20 adaptive ---"
  for seed in [42, 123, 456] do
    let f := random3SAT 10 20 seed
    let ad := metaSolve f (List.range 10)
    let ms := buildTrajectory f 10
    let mp := metaProfile ms.trajectory
    IO.println s!"  seed={seed}: adaptive={ad.rawSteps}raw/{ad.metaEvents}meta \
      pipeline={mp.totalEvents}meta solved={ad.solved}"
    IO.println s!"    strategies: {repr ad.strategies}"

/-! ## Assessment

    The adaptive meta-solver combines three capabilities:

    1. CASCADE DETECTION: run UP, measure how many variables
       it forces. High cascade → stay monolithic. Low → split.

    2. SPLIT SELECTION: find the variable that minimizes shared
       variables across the cut. This is the interpolant size
       heuristic — small interpolant = clean factorization.

    3. RECURSIVE COMPOSITION: each sub-problem gets the same
       treatment. A sub-problem with a long cascade stays
       monolithic. A sub-problem with a short cascade splits
       further. The recursion bottoms out at CDCL.

    The strategy trace IS a meta-trajectory: each decision
    (cascade, split, cdcl) is a meta-event. The meta-events
    form a tree: the root is the initial decision, branches
    are sub-problem decisions after splitting.

    This tree IS the proof structure for SAT:
    - CASCADE nodes = deterministic inference (free)
    - SPLIT nodes = problem decomposition (factorization)
    - CDCL nodes = search (irreducible work)

    The contraction ratio of the strategy tree measures the
    solver's efficiency: many CASCADE nodes and few CDCL nodes
    = high contraction = easy instance. Few CASCADE nodes and
    many CDCL nodes = low contraction = hard instance.

    For UNSAT, the same structure applies to resolution proofs:
    - CASCADE = unit resolution chain
    - SPLIT = independent sub-derivations
    - CDCL = search-driven clause learning

    The solver, the proof, and the trajectory analysis all use
    the same term structure and the same contraction operations.
-/

end RotationCalculus
