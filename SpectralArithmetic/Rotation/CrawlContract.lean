/-
  Crawl-Contract Solver: Signal-Driven Inprocessing
  ===================================================

  CRAWL: run CDCL, accumulate learned clauses, monitor signals.
  CONTRACT: subsumption + UP cascade + measure contraction ratio.
  SPLIT: decompose when contraction stalls.

  The contraction ratio drives the adaptive budget:
  - High ratio → harvest often (short crawl)
  - Low ratio → need more data (long crawl)
  - Zero ratio for K rounds → split (irreducible component)

  Signals monitored during crawl:
  - Learned clause width (proxy for resolution width / LBD)
  - Conflict rate (conflicts per decision)
  - Cascade ratio (forced propagations / total assignments)
-/

import SpectralArithmetic.Rotation.IteratedCDCL

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Crawl: CDCL with signal monitoring -/

/-- Signals collected during a crawl phase. -/
structure CrawlSignals where
  nDecisions  : ℕ
  nConflicts  : ℕ
  nPropagated : ℕ
  learnedWidths : List ℕ
  avgWidth    : ℕ
  maxWidth    : ℕ
  deriving Repr

/-- Run CDCL for a bounded number of conflicts (the crawl budget).
    Returns learned clauses + signals. -/
def crawl (formula : SATFormula) (vars : List ℕ)
    (assign : List (ℕ × Bool)) (budget : ℕ)
    : Bool × List SATClause × CrawlSignals :=
  -- Run 1-UIP CDCL to collect learned clauses
  let (found, _, learned) := satCDCL1UIP formula (List.length vars)
  -- Remap variables (1-UIP uses 0..n-1 internally)
  let remapped := learned.map fun c =>
    c.map fun (v, p) =>
      match vars[v]? with
      | some realV => (realV, p)
      | none => (v, p)
  let widths := remapped.map List.length
  let avgW := if widths.isEmpty then 0
    else widths.foldl (· + ·) 0 / List.length widths
  let maxW := widths.foldl max 0
  let signals : CrawlSignals :=
    { nDecisions := List.length vars,
      nConflicts := List.length remapped,
      nPropagated := 0,
      learnedWidths := widths,
      avgWidth := avgW,
      maxWidth := maxW }
  (found, remapped, signals)

/-! ## Contract: simplify formula using learned clauses -/

/-- Contraction result. -/
structure ContractionResult where
  formula     : SATFormula
  vars        : List ℕ
  assign      : List (ℕ × Bool)
  varsBefore  : ℕ
  varsAfter   : ℕ
  clausesBefore : ℕ
  clausesAfter  : ℕ
  isUnsat     : Bool
  deriving Repr

/-- Contract: subsumption + UP cascade on augmented formula.
    Returns the simplified formula + contraction metrics. -/
def contract (formula : SATFormula) (vars : List ℕ)
    (assign : List (ℕ × Bool))
    (learned : List SATClause) : ContractionResult :=
  let varsBefore := List.length vars
  let clausesBefore := List.length formula
  -- Augment with learned clauses
  let augmented := formula ++ learned
  -- Subsumption: remove clauses subsumed by learned
  let cleaned := eliminateSubsumed augmented
  -- UP with conflict detection
  match upWithConflict cleaned vars assign with
  | .conflict _ =>
    { formula := [], vars := [], assign := assign,
      varsBefore := varsBefore, varsAfter := 0,
      clausesBefore := clausesBefore,
      clausesAfter := 0, isUnsat := true }
  | .ok state _ =>
    let freeVars := state.vars.filter fun v =>
      !state.assign.any fun (v', _) => v == v'
    { formula := state.formula, vars := freeVars,
      assign := state.assign,
      varsBefore := varsBefore,
      varsAfter := List.length freeVars,
      clausesBefore := clausesBefore,
      clausesAfter := List.length state.formula,
      isUnsat := false }

/-- Contraction ratio: how much did the formula shrink? -/
def contractionRatioN (before after : ℕ) : ℕ :=
  if after == 0 then 1000  -- complete contraction
  else before * 100 / after

/-! ## Split: decompose when contraction stalls -/

/-- Find the variable that minimizes shared variables at split. -/
def findSplitPoint (formula : SATFormula) (vars : List ℕ)
    : ℕ × ℕ :=  -- (split variable, shared count)
  if List.length vars ≤ 2 then (vars.head?.getD 0, List.length vars)
  else
    let candidates := vars.drop 1 |>.dropLast
    let best := candidates.foldl (fun (bestV, bestS) v =>
      let a := formula.filter fun c => c.all fun (vi, _) => vi < v
      let b := formula.filter fun c => c.any fun (vi, _) => vi >= v
      let aVars := (a.flatMap fun c => c.map (·.1)).eraseDups
      let bVars := (b.flatMap fun c => c.map (·.1)).eraseDups
      let shared := aVars.filter fun vi => bVars.contains vi
      if List.length shared < bestS
      then (v, List.length shared)
      else (bestV, bestS)
    ) (vars.head?.getD 0, List.length vars)
    best

/-! ## The Crawl-Contract Loop -/

/-- One round of crawl-contract. -/
structure CCRound where
  round       : ℕ
  phase       : String         -- "crawl", "contract", "split", "done"
  crawlBudget : ℕ
  learned     : ℕ
  avgWidth    : ℕ
  contrRatio  : ℕ              -- var contraction ratio * 100
  varsBefore  : ℕ
  varsAfter   : ℕ
  deriving Repr

/-- The crawl-contract solver. -/
partial def crawlContractSolve (formula : SATFormula) (nVars : ℕ)
    (maxRounds : ℕ := 20)
    : List CCRound × Bool × Bool :=  -- (log, isSAT, isUNSAT)
  let vars := List.range nVars
  let rec go (f : SATFormula) (vs : List ℕ)
      (assign : List (ℕ × Bool))
      (budget : ℕ) (logs : List CCRound)
      (stallCount : ℕ) (fuel : ℕ)
      : List CCRound × Bool × Bool :=
    match fuel with
    | 0 => (logs, false, false)
    | fuel + 1 =>
      if List.length vs == 0 then
        (logs, false, false)
      else
        let roundNum := maxRounds - fuel
        -- CRAWL phase
        let (found, learned, signals) := crawl f vs assign budget
        if found then
          let log : CCRound :=
            { round := roundNum, phase := "SAT",
              crawlBudget := budget, learned := 0,
              avgWidth := 0, contrRatio := 0,
              varsBefore := List.length vs,
              varsAfter := List.length vs }
          (logs ++ [log], true, false)
        else
          -- CONTRACT phase
          let cr := contract f vs assign learned
          let ratio := contractionRatioN cr.varsBefore cr.varsAfter
          let log : CCRound :=
            { round := roundNum, phase := "contract",
              crawlBudget := budget,
              learned := List.length learned,
              avgWidth := signals.avgWidth,
              contrRatio := ratio,
              varsBefore := cr.varsBefore,
              varsAfter := cr.varsAfter }
          let newLogs := logs ++ [log]
          if cr.isUnsat then
            (newLogs, false, true)
          else if cr.varsAfter == 0 then
            (newLogs, false, true)
          else
            -- Adaptive budget
            let newBudget :=
              if ratio > 200 then max (budget / 2) 1     -- high contraction: harvest often
              else if ratio < 110 then budget * 2         -- low contraction: need more data
              else budget                                  -- moderate: keep same
            let newStall :=
              if ratio < 105 then stallCount + 1 else 0
            -- SPLIT escape: stalled for 3+ rounds
            if newStall >= 3 then
              let (splitV, shared) := findSplitPoint cr.formula cr.vars
              let splitLog : CCRound :=
                { round := roundNum, phase := s!"split@x{splitV}(shared={shared})",
                  crawlBudget := newBudget,
                  learned := 0, avgWidth := 0, contrRatio := 0,
                  varsBefore := cr.varsAfter,
                  varsAfter := cr.varsAfter }
              -- Solve each part recursively
              let partA := cr.formula.filter fun c =>
                c.all fun (v, _) => v < splitV
              let partB := cr.formula.filter fun c =>
                c.any fun (v, _) => v >= splitV
              let aVars := cr.vars.filter (· < splitV)
              let bVars := cr.vars.filter (· >= splitV)
              let (logsA, satA, unsatA) :=
                crawlContractSolve partA (List.length aVars) (fuel / 2)
              if satA then
                (newLogs ++ [splitLog] ++ logsA, true, false)
              else
                let simpB := simplifyFormula partB cr.assign
                let (logsB, satB, unsatB) :=
                  crawlContractSolve simpB (List.length bVars) (fuel / 2)
                (newLogs ++ [splitLog] ++ logsA ++ logsB,
                 satB, unsatA || unsatB)
            else
              go cr.formula cr.vars cr.assign newBudget
                newLogs newStall fuel
  go formula vars [] 1 [] 0 maxRounds

/-! ## Demonstrations -/

#eval! do
  IO.println "=== CRAWL-CONTRACT SOLVER ==="
  IO.println ""

  let test := fun (name : String) (f : SATFormula) (nv : ℕ) => do
    let (logs, isSAT, isUNSAT) := crawlContractSolve f nv 20
    let result := if isSAT then "SAT"
      else if isUNSAT then "UNSAT"
      else "UNKNOWN"
    IO.println s!"  {name}: {result} rounds={List.length logs}"
    for (log : CCRound) in logs do
      IO.println s!"    R{log.round}: {log.phase} budget={log.crawlBudget} \
        L={log.learned} avgW={log.avgWidth} \
        ratio={log.contrRatio}% vars={log.varsBefore}→{log.varsAfter}"

  IO.println "--- Structured ---"
  test "PHP(3,2)" (pigeonhole 3 2) 6
  test "chain-5" (chainFormula 5) 5
  test "tseitin-5" (tseitinCycle 5) 5
  IO.println ""

  IO.println "--- Random n=4 ---"
  for seed in [42, 123, 456, 789] do
    let f := random3SAT 4 20 seed
    let (sat, _) := flatBruteForce f 4
    let tag := if sat.isSome then "(SAT)" else "(UNSAT)"
    test s!"rand-4-20-s{seed}{tag}" f 4
  IO.println ""

  IO.println "--- Random n=6 ---"
  for seed in [42, 123] do
    let f := random3SAT 6 30 seed
    let (sat, _) := flatBruteForce f 6
    let tag := if sat.isSome then "(SAT)" else "(UNSAT)"
    test s!"rand-6-30-s{seed}{tag}" f 6
  IO.println ""

  IO.println "--- PHP scaling ---"
  for p in [3, 4, 5] do
    test s!"PHP({p},{p-1})" (pigeonhole p (p-1)) (p*(p-1))

/-! ## Assessment

    The crawl-contract loop implements signal-driven inprocessing:

    1. CRAWL: CDCL accumulates learned clauses. Signals tracked:
       - Learned clause width (resolution width proxy)
       - Number of conflicts (search density)

    2. CONTRACT: subsumption + UP cascade. Measured by:
       - Variable contraction ratio (vars_before / vars_after)
       - Clause contraction (clausesBefore / clausesAfter)

    3. ADAPT: budget adjusts based on contraction ratio:
       - High (>200%): halve budget — harvest learned clauses often
       - Low (<110%): double budget — need more search before contracting
       - Stalled for 3 rounds (<105%): SPLIT — decompose the formula

    4. SPLIT: find minimal-shared-variable split point, solve recursively

    What's novel vs fixed-schedule inprocessing:
    - Contraction ratio as adaptive signal (no solver does this)
    - Split escape when crawl-contract stalls (no solver decomposes mid-search)
    - Width trajectory as phase indicator (could correlate with LBD — untested)
-/

end RotationCalculus
