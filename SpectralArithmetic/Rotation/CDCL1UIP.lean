/-
  CDCL with 1-UIP Conflict Analysis
  ===================================

  The current CDCL learns full assignment negations (width n).
  1-UIP (First Unique Implication Point) learns SHORT clauses
  by analyzing WHY the conflict occurred.

  The implication graph tracks:
  - Decision variables: assigned by choice (no reason)
  - Propagated variables: assigned by unit propagation (reason = clause)

  Conflict analysis:
  1. Start with the conflicting clause
  2. Resolve backward through the implication graph
  3. Stop at the 1-UIP: the point where only ONE variable from
     the current decision level remains
  4. The resulting clause is the learned clause

  The learned clause is typically much shorter than the full
  assignment — often width 1 or 2 for structured formulas.
-/

import SpectralArithmetic.Rotation.ChainAnalysis

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Implication graph -/

/-- Why a variable was assigned. -/
inductive AssignReason where
  | decision : ℕ → AssignReason        -- decision level
  | propagated : SATClause → AssignReason  -- forced by this clause
  deriving Repr

/-- An assignment with its reason and decision level. -/
structure TrackedAssign where
  var    : ℕ
  pol    : Bool
  level  : ℕ          -- decision level when assigned
  reason : AssignReason
  deriving Repr

/-- The implication graph: all assignments with reasons. -/
abbrev ImplGraph := List TrackedAssign

/-- Find the reason for a variable's assignment. -/
def findReason (graph : ImplGraph) (v : ℕ)
    : Option TrackedAssign :=
  graph.find? fun ta => ta.var == v

/-- Get the decision level of a variable. -/
def assignLevel (graph : ImplGraph) (v : ℕ) : ℕ :=
  match findReason graph v with
  | some ta => ta.level
  | none => 0

/-! ## Unit propagation with reason tracking -/

/-- Find unit clauses in the current formula under partial assignment.
    A clause is unit if all but one literal are falsified.
    Returns (variable, polarity, reason_clause). -/
def findUnitReasons (formula : SATFormula)
    (assign : List (ℕ × Bool))
    : List (ℕ × Bool × SATClause) :=
  formula.filterMap fun clause =>
    -- Count unfalsified literals
    let unfalsified := clause.filter fun (v, p) =>
      !(assign.any fun (v', p') => v == v' && p != p')
    -- Count unassigned literals among unfalsified
    let unassigned := unfalsified.filter fun (v, _) =>
      !(assign.any fun (v', _) => v == v')
    if List.length unassigned == 1 then
      match unassigned with
      | [(v, p)] => some (v, p, clause)
      | _ => none
    else none

/-- Unit propagation with implication graph tracking.
    Returns (new assignments, updated graph). -/
def propagateWithReasons (formula : SATFormula)
    (assign : List (ℕ × Bool)) (graph : ImplGraph)
    (level : ℕ) : List (ℕ × Bool) × ImplGraph :=
  let units := findUnitReasons formula assign
  let newAssigns := units.filter fun (v, _, _) =>
    !(assign.any fun (v', _) => v == v')
  let newGraph := newAssigns.foldl (fun g (v, p, clause) =>
    g ++ [{ var := v, pol := p, level := level,
             reason := .propagated clause }]
  ) graph
  let newAssign := newAssigns.map fun (v, p, _) => (v, p)
  (newAssign, newGraph)

/-- UP to fixpoint with reason tracking. -/
partial def propagateFixpoint (formula : SATFormula)
    (assign : List (ℕ × Bool)) (graph : ImplGraph)
    (level : ℕ) : List (ℕ × Bool) × ImplGraph :=
  let (newAssigns, newGraph) :=
    propagateWithReasons formula assign graph level
  if newAssigns.isEmpty then (assign, newGraph)
  else
    propagateFixpoint formula (assign ++ newAssigns) newGraph level

/-! ## 1-UIP conflict analysis -/

/-- Analyze a conflict to produce a 1-UIP learned clause.

    Algorithm:
    1. Start with the conflicting clause (all literals falsified)
    2. Count literals at the current decision level
    3. While count > 1:
       a. Pick a literal at the current level that was propagated
       b. Resolve with its reason clause (remove the literal,
          add the reason clause's other literals)
       c. Recount literals at the current level
    4. The result is the 1-UIP clause -/
def analyze1UIP (conflictClause : SATClause) (graph : ImplGraph)
    (currentLevel : ℕ) : SATClause :=
  -- Start with the conflict clause (negated — these are the literals
  -- that must appear in the learned clause)
  let rec go (clause : SATClause) (fuel : ℕ) : SATClause :=
    match fuel with
    | 0 => clause
    | fuel + 1 =>
      -- Count literals at the current decision level
      let atCurrentLevel := clause.filter fun (v, _) =>
        assignLevel graph v == currentLevel
      if List.length atCurrentLevel <= 1 then
        -- 1-UIP reached: only one literal from current level
        clause.eraseDups
      else
        -- Find a propagated literal at current level to resolve
        let resolvable := atCurrentLevel.find? fun (v, _) =>
          match findReason graph v with
          | some { reason := .propagated _, .. } => true
          | _ => false
        match resolvable with
        | none => clause.eraseDups  -- all decisions, can't resolve further
        | some (rv, rp) =>
          -- Get the reason clause
          match findReason graph rv with
          | some { reason := .propagated reasonClause, .. } =>
            -- Resolve: remove rv from clause, add reasonClause's
            -- other literals (negated, since they forced rv)
            let without_rv := clause.filter fun (v, _) => v != rv
            let from_reason := reasonClause.filter fun (v, _) => v != rv
            -- The reason clause's literals (except rv) contributed to
            -- forcing rv, so their NEGATIONS go in the learned clause
            let negated := from_reason.map fun (v, p) => (v, !p)
            go (without_rv ++ negated) fuel
          | _ => clause.eraseDups
  -- Start: negate the conflict clause (the conflict tells us which
  -- literals are false, the learned clause says "not all of these")
  let initial := conflictClause.map fun (v, p) => (v, !p)
  let raw := go initial (List.length graph + 1)
  -- Clean up: remove duplicate variables, remove tautologies
  let deduped := raw.eraseDups
  -- Remove complementary pairs (x and ¬x in same clause = tautology)
  let isTautology := deduped.any fun (v, p) =>
    deduped.any fun (v', p') => v == v' && p != p'
  if isTautology then
    -- Remove one side of each complementary pair
    let cleaned := deduped.filter fun (v, p) =>
      !(deduped.any fun (v', p') => v == v' && p != p' && !p)
    cleaned
  else deduped

/-! ## CDCL with 1-UIP -/

/-- CDCL search with 1-UIP conflict analysis.
    Tracks implication graph for learned clause minimization. -/
partial def cdcl1UIP (formula : SATFormula) (vars : List ℕ)
    (assign : List (ℕ × Bool)) (graph : ImplGraph)
    (level : ℕ)
    : Bool × ℕ × List SATClause × ImplGraph :=
  -- Unit propagation with reason tracking
  let (propAssign, propGraph) :=
    propagateFixpoint formula assign graph level
  -- Check for conflict
  let conflict := findConflict formula propAssign
  match conflict with
  | some conflictClause =>
    -- Conflict! Analyze with 1-UIP
    let learned := analyze1UIP conflictClause propGraph level
    (false, 1, [learned], propGraph)
  | none =>
    match vars.filter fun v =>
      !(propAssign.any fun (v', _) => v == v') with
    | [] =>
      -- All assigned, no conflict → SAT
      (true, 1, [], propGraph)
    | v :: rest =>
      -- Decision: try v = true
      let decGraph := propGraph ++
        [{ var := v, pol := true, level := level + 1,
           reason := .decision (level + 1) }]
      let trueAssign := propAssign ++ [(v, true)]
      let (foundT, costT, learnedT, _) :=
        cdcl1UIP formula rest trueAssign decGraph (level + 1)
      if foundT then (true, costT + 1, learnedT, propGraph)
      else
        -- Backtrack: try v = false with learned clauses
        let formula' := formula ++ learnedT
        let decGraph2 := propGraph ++
          [{ var := v, pol := false, level := level + 1,
             reason := .decision (level + 1) }]
        let falseAssign := propAssign ++ [(v, false)]
        let (foundF, costF, learnedF, _) :=
          cdcl1UIP formula' rest falseAssign decGraph2 (level + 1)
        (foundF, costT + costF + 1,
         learnedT ++ learnedF, propGraph)

/-- Wrapper: CDCL with 1-UIP. -/
def satCDCL1UIP (formula : SATFormula) (nVars : ℕ)
    : Bool × ℕ × List SATClause :=
  let vars := List.range nVars
  let (found, cost, learned, _) :=
    cdcl1UIP formula vars [] [] 0
  (found, cost, learned)

/-! ## Demonstrations -/

#eval! do
  IO.println "=== CDCL 1-UIP vs NAIVE ==="
  IO.println ""
  IO.println "formula\t\t\tnaive_L\tnaive_W\t1UIP_L\t1UIP_W\t1UIP_cost"

  let compare := fun (name : String) (f : SATFormula) (nv : ℕ) => do
    let (_, costN, learnedN) := cdclSearch f (List.range nv) []
    let naiveWidths := learnedN.map List.length
    let (found1, cost1, learned1) := satCDCL1UIP f nv
    let uipWidths := learned1.map List.length
    let avgNW := if naiveWidths.isEmpty then 0
      else naiveWidths.foldl (· + ·) 0 / List.length naiveWidths
    let avgUW := if uipWidths.isEmpty then 0
      else uipWidths.foldl (· + ·) 0 / List.length uipWidths
    IO.println s!"  {name}\t\t{List.length learnedN}\t{avgNW}\t{List.length learned1}\t{avgUW}\t{cost1}({found1})"

  -- Structured
  compare "PHP(3,2)" (pigeonhole 3 2) 6
  compare "chain-5" (chainFormula 5) 5
  compare "tseitin-3" (tseitinCycle 3) 3

  IO.println ""
  -- Random UNSAT n=4
  for seed in [42, 123, 1001, 5555] do
    let f := random3SAT 4 20 seed
    let (sat, _) := flatBruteForce f 4
    if sat.isNone then
      compare s!"rand-4-20-s{seed}" f 4

#eval! do
  IO.println ""
  IO.println "=== 1-UIP LEARNED CLAUSES: CAN GREEDY USE THEM? ==="
  IO.println ""
  for seed in [42, 123, 1001] do
    let f := random3SAT 4 20 seed
    let (sat, _) := flatBruteForce f 4
    if sat.isNone then
      let (_, _, learned1) := satCDCL1UIP f 4
      IO.println s!"--- rand-4-20-s{seed} ---"
      IO.println s!"  1-UIP learned: {List.length learned1} clauses"
      let widths := learned1.map List.length
      IO.println s!"  widths: {widths}"
      -- Feed to greedy
      let augmented := f ++ learned1
      let (gd, _) := greedyResolution augmented 500
      IO.println s!"  greedy(orig+1UIP): {List.length gd.steps} □={gd.conclusion.isEmpty}"
      if gd.conclusion.isEmpty then
        let (breaks, maxChain, _, _) :=
          analyzeChain gd.steps augmented
        IO.println s!"    breaks={breaks} maxChain={maxChain}"
      IO.println ""

#eval! do
  IO.println ""
  IO.println "=== META-SYSTEM VIEW OF 1-UIP ==="
  IO.println ""
  -- Run the pipeline with 1-UIP CDCL and compare trajectories
  for seed in [42, 123] do
    let f := random3SAT 4 20 seed
    let (sat, _) := flatBruteForce f 4
    if sat.isNone then
      IO.println s!"--- rand-4-20-s{seed} ---"
      -- Naive CDCL
      let (_, costN, learnedN) := cdclSearch f (List.range 4) []
      let nWidths := learnedN.map List.length
      -- 1-UIP CDCL
      let (_, cost1, learned1) := satCDCL1UIP f 4
      let uWidths := learned1.map List.length
      IO.println s!"  naive: cost={costN} learned={List.length learnedN} \
        widths={nWidths}"
      IO.println s!"  1-UIP: cost={cost1} learned={List.length learned1} \
        widths={uWidths}"
      -- Width trajectory comparison
      let avgN := if nWidths.isEmpty then 0
        else nWidths.foldl (· + ·) 0 / List.length nWidths
      let avgU := if uWidths.isEmpty then 0
        else uWidths.foldl (· + ·) 0 / List.length uWidths
      IO.println s!"  width reduction: {avgN} → {avgU} \
        ({if avgN > 0 then avgN * 100 / max avgU 1 else 0}% of naive)"
      -- Pipeline trajectory with augmented formula
      let aug := f ++ learned1
      let msAug := buildTrajectory aug 4
      let mpAug := metaProfile msAug.trajectory
      IO.println s!"  meta(orig+1UIP): events={mpAug.totalEvents} \
        cascade={mpAug.nCascade}({mpAug.cascadeTotal}v) \
        search={mpAug.nSearch} cycles={mpAug.nConflictCycle}"
      IO.println ""

/-! ## Assessment

    1-UIP conflict analysis should produce SHORTER learned clauses:
    - Naive: width = n (full assignment negation)
    - 1-UIP: width = 1-2 for structured, ??? for random

    If 1-UIP produces unit clauses:
    - They create UP cascades in the augmented formula
    - The greedy resolver can then find single-chain proofs
    - The meta-system sees CASCADE events instead of SEARCH

    If 1-UIP produces short (width 2-3) clauses:
    - They create binary implications
    - UP cascades form when two short clauses share a variable
    - The chain structure should emerge

    The meta-system measures the EFFECT of 1-UIP:
    - Width reduction: how much shorter are learned clauses?
    - Cascade creation: do learned clauses enable UP?
    - Chain structure: does greedy find proofs after augmentation?
-/

end RotationCalculus
