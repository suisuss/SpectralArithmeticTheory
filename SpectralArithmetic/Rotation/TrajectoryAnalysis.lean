/-
  Trajectory Analysis: Do structured and hard instances have
  visibly different trajectory signatures?
  ==========================================================

  Hypothesis: if meta-rewriting (contracting the trajectory itself)
  is useful, structured instances should have trajectories that
  factorize (cascade-dominated, few decisions) while hard instances
  should have non-factorizable trajectories (decision-dominated,
  many learned clauses, no clear structure).

  This file tests the hypothesis BEFORE building the full
  meta-rewriting system.

  Measurements:
  1. Free ratio: (UP + pure) / total steps
  2. Decision ratio: decisions / total steps
  3. Cascade depth: max consecutive UP steps
  4. Formula direction: did clause count grow (learned > eliminated)?
  5. Phase structure: where in the trace do decisions cluster?
  6. Factorization potential: ratio of independent variable clusters
-/

import SpectralArithmetic.Rotation.Pipeline

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Trajectory metrics -/

/-- Extract step counts from a proof trace. -/
structure TraceProfile where
  total      : ℕ
  nUP        : ℕ
  nPure      : ℕ
  nAbs       : ℕ
  nLearn     : ℕ
  nDecision  : ℕ
  nConflict  : ℕ
  nBacktrack : ℕ
  deriving Repr

def profileTrace (trace : ProofTrace) : TraceProfile :=
  { total := trace.length,
    nUP := trace.filter (fun s => match s with | .unitProp _ _ => true | _ => false) |>.length,
    nPure := trace.filter (fun s => match s with | .pureLiteral _ _ => true | _ => false) |>.length,
    nAbs := trace.filter (fun s => match s with | .abstraction _ _ => true | _ => false) |>.length,
    nLearn := trace.filter (fun s => match s with | .learnedClause _ => true | _ => false) |>.length,
    nDecision := trace.filter (fun s => match s with | .decision _ _ => true | _ => false) |>.length,
    nConflict := trace.filter (fun s => match s with | .conflict _ => true | _ => false) |>.length,
    nBacktrack := trace.filter (fun s => match s with | .backtrack _ => true | _ => false) |>.length }

/-- Free inference ratio: what fraction of the proof was deterministic? -/
def TraceProfile.freeRatio (p : TraceProfile) : ℕ :=
  if p.total == 0 then 100
  else (p.nUP + p.nPure) * 100 / p.total

/-- Decision ratio: what fraction required search? -/
def TraceProfile.decisionRatio (p : TraceProfile) : ℕ :=
  if p.total == 0 then 0
  else p.nDecision * 100 / p.total

/-- Max consecutive UP steps (cascade depth). -/
def maxCascade (trace : ProofTrace) : ℕ :=
  let (maxRun, _) := trace.foldl (fun (best, cur) step =>
    match step with
    | .unitProp _ _ | .pureLiteral _ _ => (max best (cur + 1), cur + 1)
    | _ => (best, 0)) (0, 0)
  maxRun

/-- Phase structure: split trace into phases by decision boundaries.
    Returns list of phase lengths (steps between decisions). -/
def phaseStructure (trace : ProofTrace) : List ℕ :=
  let (phases, current) := trace.foldl (fun (acc, cur) step =>
    match step with
    | .decision _ _ => (acc ++ [cur], 0)
    | _ => (acc, cur + 1)) ([], 0)
  phases ++ [current]

/-- Formula growth: count learned clauses vs abstractions.
    Positive = formula grew (UNSAT-like). Negative = shrank. -/
def formulaGrowth (p : TraceProfile) : Int :=
  (p.nLearn : Int) - (p.nAbs : Int)

/-- Variable independence estimate: fraction of variables
    resolved by UP (independent of search decisions). -/
def independenceRatio (trace : ProofTrace) (nVars : ℕ) : ℕ :=
  if nVars == 0 then 100
  else
    let upVars := trace.filter (fun s => match s with
      | .unitProp _ _ | .pureLiteral _ _ => true
      | _ => false) |>.length
    upVars * 100 / nVars

/-- Free pre: steps before first decision. -/
def freePre (trace : ProofTrace) : ℕ :=
  (trace.takeWhile fun s => match s with
    | ProofStep.decision _ _ => false | _ => true).length

/-! ## Pretty printing -/

def showProfile (name : String) (p : TraceProfile)
    (trace : ProofTrace) (nVars : ℕ) (solved : Bool) : String :=
  let phases := phaseStructure trace
  let nPhases := phases.filter (· > 0) |>.length
  let fp := freePre trace
  s!"{name}: total={p.total} free={p.freeRatio}% " ++
  s!"dec={p.decisionRatio}% cascade={maxCascade trace} " ++
  s!"pre={fp} phases={nPhases} " ++
  s!"growth={formulaGrowth p} " ++
  s!"indep={independenceRatio trace nVars}% " ++
  s!"solved={solved} " ++
  s!"[UP={p.nUP} pure={p.nPure} abs={p.nAbs} " ++
  s!"learn={p.nLearn} dec={p.nDecision} " ++
  s!"confl={p.nConflict} bt={p.nBacktrack}]"

/-- Show a single proof step as a tag. -/
def stepTag (step : ProofStep) : String :=
  match step with
  | .unitProp v p => s!"UP({v}={p})"
  | .pureLiteral v p => s!"PURE({v}={p})"
  | .abstraction id vars => s!"ABS({id},{vars})"
  | .learnedClause c => s!"LEARN({c.length}lits)"
  | .decision v p => s!"DECIDE({v}={p})"
  | .conflict c => s!"CONFLICT({c.length}lits)"
  | .backtrack v => s!"BACKTRACK({v})"

/-! ## Test 1: Structured vs Random vs UNSAT -/

#eval! do
  IO.println "=== TRAJECTORY SIGNATURE COMPARISON ==="
  IO.println ""

  IO.println "--- Structured (reach=1, path-like) ---"
  for n in [8, 10, 12] do
    let f := reachInstance n 1
    let (sol, trace, _) := runPipeline f n
    let p := profileTrace trace
    IO.println (showProfile s!"struct-{n}-r1" p trace n sol.isSome)

  IO.println ""
  IO.println "--- Structured (reach=3, moderate) ---"
  for n in [8, 10, 12] do
    let f := reachInstance n 3
    let (sol, trace, _) := runPipeline f n
    let p := profileTrace trace
    IO.println (showProfile s!"struct-{n}-r3" p trace n sol.isSome)

  IO.println ""
  IO.println "--- Random 3-SAT below transition (m/n ~ 2) ---"
  for seed in [42, 123, 456, 789, 1001] do
    let n := 10; let m := 20
    let f := random3SAT n m seed
    let (sol, trace, _) := runPipeline f n
    let p := profileTrace trace
    IO.println (showProfile s!"rand-{n}-{m}-s{seed}" p trace n sol.isSome)

  IO.println ""
  IO.println "--- Random 3-SAT at transition (m/n ~ 4.2) ---"
  for seed in [42, 123, 456, 789, 1001] do
    let n := 10; let m := 42
    let f := random3SAT n m seed
    let (sol, trace, _) := runPipeline f n
    let p := profileTrace trace
    IO.println (showProfile s!"rand-{n}-{m}-s{seed}" p trace n sol.isSome)

  IO.println ""
  IO.println "--- Random 3-SAT above transition (m/n ~ 6) ---"
  for seed in [42, 123, 456, 789, 1001] do
    let n := 10; let m := 60
    let f := random3SAT n m seed
    let (sol, trace, _) := runPipeline f n
    let p := profileTrace trace
    IO.println (showProfile s!"rand-{n}-{m}-s{seed}" p trace n sol.isSome)

  IO.println ""
  IO.println "--- Pigeonhole (UNSAT, provably hard) ---"
  let f := pigeonhole 3 2
  let nv := 6
  let (sol, trace, _) := runPipeline f nv
  let p := profileTrace trace
  IO.println (showProfile "PHP-3-2" p trace nv sol.isSome)

  let f' := pigeonhole 4 3
  let nv' := 12
  let (sol', trace', _) := runPipeline f' nv'
  let p' := profileTrace trace'
  IO.println (showProfile "PHP-4-3" p' trace' nv' sol'.isSome)

/-! ## Test 2: Cascade depth vs density sweep -/

#eval! do
  IO.println ""
  IO.println "=== CASCADE DEPTH vs DENSITY ==="
  IO.println "n=10, seed=42, varying clause count"
  IO.println ""
  IO.println "m\tratio\tfree%\tdec%\tcascade\tpre\tlearn\tphases\tgrowth\tsolved"
  for m in [10, 15, 20, 25, 30, 35, 40, 42, 45, 50, 55, 60] do
    let n := 10
    let f := random3SAT n m 42
    let (sol, trace, _) := runPipeline f n
    let p := profileTrace trace
    let phases := (phaseStructure trace).filter (· > 0) |>.length
    let fp := freePre trace
    let r10 := m * 10 / n
    IO.println s!"{m}\t{r10/10}.{r10%10}\t{p.freeRatio}\t{p.decisionRatio}\t{maxCascade trace}\t{fp}\t{p.nLearn}\t{phases}\t{formulaGrowth p}\t{sol.isSome}"

/-! ## Test 3: Phase structure visualization -/

#eval! do
  IO.println ""
  IO.println "=== TRACE STEP SEQUENCE ==="
  IO.println ""

  IO.println "--- Structured (n=8, reach=1) ---"
  let f := reachInstance 8 1
  let (_, trace, _) := runPipeline f 8
  let mut idx := 0
  for step in trace do
    IO.println s!"  step {idx}: {stepTag step}"
    idx := idx + 1

  IO.println ""
  IO.println "--- Random hard (n=8, m=34, seed=42) ---"
  let f' := random3SAT 8 34 42
  let (_, trace', _) := runPipeline f' 8
  let mut idx' := 0
  for step in trace' do
    IO.println s!"  step {idx'}: {stepTag step}"
    idx' := idx' + 1

/-! ## Test 4: Factorization potential -/

#eval! do
  IO.println ""
  IO.println "=== FACTORIZATION: FREE PREFIX LENGTH ==="
  IO.println ""

  let instances : List (String × SATFormula × ℕ) := [
    ("struct-8-r1", reachInstance 8 1, 8),
    ("struct-8-r3", reachInstance 8 3, 8),
    ("struct-10-r1", reachInstance 10 1, 10),
    ("struct-10-r3", reachInstance 10 3, 10),
    ("rand-8-16-s42", random3SAT 8 16 42, 8),
    ("rand-8-32-s42", random3SAT 8 32 42, 8),
    ("rand-10-20-s42", random3SAT 10 20 42, 10),
    ("rand-10-42-s42", random3SAT 10 42 42, 10),
    ("rand-10-60-s42", random3SAT 10 60 42, 10),
    ("PHP-3-2", pigeonhole 3 2, 6),
    ("PHP-4-3", pigeonhole 4 3, 12)]

  for (name, formula, n) in instances do
    let (sol, trace, _) := runPipeline formula n
    let fp := freePre trace
    let p := profileTrace trace
    let pct := if p.total > 0 then fp * 100 / p.total else 100
    IO.println s!"{name}: pre={fp}/{p.total} ({pct}%) cascade={maxCascade trace} solved={sol.isSome}"

/-! ## Test 5: Multi-seed statistics at transition -/

#eval! do
  IO.println ""
  IO.println "=== MULTI-SEED TRAJECTORY STATS (n=10) ==="
  IO.println ""

  for m in [20, 30, 42, 50, 60] do
    let seeds : List ℕ := [42, 123, 456, 789, 1001,
                            2024, 3141, 4242, 5555, 6789]
    let mut sumFree := 0; let mut sumDec := 0
    let mut sumCasc := 0; let mut sumPre := 0
    let mut sumLearn := 0; let mut satCnt := 0
    for seed in seeds do
      let sf := random3SAT 10 m seed
      let (sol, trace, _) := runPipeline sf 10
      let p := profileTrace trace
      sumFree := sumFree + p.freeRatio
      sumDec := sumDec + p.decisionRatio
      sumCasc := sumCasc + maxCascade trace
      sumPre := sumPre + freePre trace
      sumLearn := sumLearn + p.nLearn
      if sol.isSome then satCnt := satCnt + 1
    let cnt := seeds.length
    IO.println s!"m={m} r={m/10}.{m%10}: \
      avgFree={sumFree/cnt}% avgDec={sumDec/cnt}% \
      avgCascade={sumCasc/cnt} avgPre={sumPre/cnt} \
      avgLearn={sumLearn/cnt} sat={satCnt}/{cnt}"

/-! ## Assessment

    What to look for in the results:

    HYPOTHESIS 1 (factorization):
    Structured instances should have free prefix = 100% of trace
    (all variables resolved by UP, zero decisions). Hard random
    instances should have short free prefixes.

    If confirmed: meta-rewriting can exploit this. The cascade is
    a single "macro-step" that contracts the trajectory from n
    steps to 1. The decision-free prefix is the factorizable part.

    If refuted: the trajectory structure doesn't separate instance
    classes. Meta-rewriting at the trajectory level won't help.

    HYPOTHESIS 2 (formula direction):
    SAT instances should have negative growth (formula shrinks:
    abstractions remove clauses). UNSAT instances should have
    positive growth (formula grows: learned clauses add structure).

    HYPOTHESIS 3 (cascade depth as complexity proxy):
    Cascade depth should correlate inversely with instance hardness.
    Long cascades = easy (propagation does the work). Short/no
    cascades = hard (search does the work).

    HYPOTHESIS 4 (phase structure):
    Structured instances: one long cascade phase, zero decisions.
    Hard instances: many short phases separated by decisions.
    The phase count is a proxy for "how many independent choices
    the solver had to make" = the irreducible search component.

    If all four hypotheses confirm, the meta-rewriting system
    should:
    1. Detect cascade-dominated trajectories and contract them
    2. Track formula direction as a SAT/UNSAT signal
    3. Use cascade depth to predict contraction potential
    4. Count decision phases as irreducible complexity measure
-/

end RotationCalculus
