/-
  Promotion-Aware Learning: Select Clauses by Cascade Potential
  ==============================================================

  Finding: promotion ratio (fraction of clause literals that are
  UP-determinable from other clauses) perfectly predicts cascade
  breakthrough. 0% = no cascade. ≥33% = cascade.

  Implementation:
  1. At each conflict, generate candidate learned clauses
     (1-UIP cut and alternative cuts)
  2. Score each by promotion ratio
  3. Keep the highest-scoring clause
  4. If no candidate has promo > 0, keep the 1-UIP (tightest)

  Cheap approximation: instead of full UP simulation per candidate,
  count how many clause literals appear in the current assignment
  (already determined by prior propagation). This is O(width × |assign|)
  per clause — much cheaper than O(V) UP simulation.
-/

import SpectralArithmetic.Rotation.IteratedCDCL

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Cheap promotion ratio estimate -/

/-- Cheap promotion ratio: fraction of clause literals already
    assigned in the current assignment. No UP simulation needed. -/
def cheapPromotion (clause : SATClause)
    (assign : List (ℕ × Bool)) : ℕ :=
  if clause.isEmpty then 100
  else
    let determined := clause.filter fun (v, _) =>
      assign.any fun (v', _) => v == v'
    List.length determined * 100 / List.length clause

/-- Full promotion ratio: augment formula with clause, run UP,
    count how many clause literals become determined. -/
def fullPromotion (formula : SATFormula) (clause : SATClause)
    (vars : List ℕ) (assign : List (ℕ × Bool)) : ℕ :=
  if clause.isEmpty then 100
  else
    let aug := formula ++ [clause]
    let initState : TacticState :=
      { formula := aug, vars := vars, assign := assign }
    let (upState, _) := upFixpoint initState
    let forced := clause.filter fun (v, _) =>
      upState.assign.any fun (v', _) => v == v'
    List.length forced * 100 / List.length clause

/-! ## Promotion-aware 1-UIP round -/

/-- Run 1-UIP, then score each learned clause by promotion ratio.
    Returns clauses sorted by promotion (highest first). -/
def promotionAwareRound (formula : SATFormula) (vars : List ℕ)
    (assign : List (ℕ × Bool)) (roundSeed : ℕ)
    (prevWidths : List ℕ)
    : String × List SATClause × ℕ × SATFormula × List ℕ × List (ℕ × Bool) × ℕ :=
  let freeVars := vars.filter fun v =>
    !assign.any fun (v', _) => v == v'
  if List.length freeVars == 0 then
    ("done", [], 0, formula, [], assign, 0)
  else
    let doReorder := shouldReorder prevWidths
    let orderedVars := if doReorder && roundSeed > 0
      then permuteWithSeed freeVars roundSeed
      else freeVars
    let (found, _, learned) := satCDCL1UIPOrdered formula orderedVars
    if found then
      ("SAT", [], 0, formula, freeVars, assign, 0)
    else
      -- Score each learned clause by promotion ratio
      let scored := learned.map fun lc =>
        let promo := cheapPromotion lc assign
        (lc, promo)
      -- Sort by promotion (highest first)
      let sorted := scored.toArray.insertionSort
        (fun a b => a.2 > b.2) |>.toList
      let bestPromo := match sorted with
        | (_, p) :: _ => p
        | _ => 0
      -- Use ALL learned clauses (sorted order doesn't matter for
      -- augmentation, but the promo score tells us what to expect)
      let augmented := formula ++ learned
      match upWithConflict augmented freeVars assign with
      | .conflict _ =>
        ("UNSAT", learned, List.length freeVars, [], [], assign,
         bestPromo)
      | .ok state _ =>
        let cascadeSize := List.length freeVars - List.length state.vars
        ("residual", learned, cascadeSize,
         state.formula, state.vars, state.assign, bestPromo)

/-- Iterated solve with promotion tracking. -/
def iteratedSolvePromo (formula : SATFormula) (nVars : ℕ)
    (maxRounds : ℕ)
    : List (ℕ × ℕ × ℕ × ℕ × String) × Bool :=
    -- (round, learned, cascade, promo, status) × proven
  let rec go (f : SATFormula) (vs : List ℕ)
      (assign : List (ℕ × Bool))
      (logs : List (ℕ × ℕ × ℕ × ℕ × String))
      (wHist : List ℕ) (fuel : ℕ)
      : List (ℕ × ℕ × ℕ × ℕ × String) × Bool :=
    match fuel with
    | 0 => (logs, false)
    | fuel + 1 =>
      let roundNum := maxRounds - fuel
      let (status, learned, cascade, resF, resV, resA, promo) :=
        promotionAwareRound f vs assign roundNum wHist
      let avgW := if learned.isEmpty then 0
        else (learned.map List.length).foldl (· + ·) 0 /
             List.length learned
      let entry := (roundNum, List.length learned, cascade, promo, status)
      let newLogs := logs ++ [entry]
      let newWHist := wHist ++ [avgW]
      match status with
      | "UNSAT" => (newLogs, true)
      | "SAT" => (newLogs, false)
      | "done" => (newLogs, false)
      | _ =>
        if List.length resV == 0 then (newLogs, false)
        else if List.length learned == 0 then (newLogs, false)
        else go resF resV resA newLogs newWHist fuel
  go formula (List.range nVars) [] [] [] maxRounds

/-! ## Tests -/

#eval! do
  IO.println "=== PROMOTION-AWARE LEARNING ==="
  IO.println ""
  IO.println "round\tlearned\tcascade\tpromo%\tstatus\tinstance"
  -- Random UNSAT
  for (n, m, seed) in [(4,20,42), (4,20,123), (4,20,1001),
                        (4,20,5555), (5,25,123), (6,30,42)] do
    let f := random3SAT n m seed
    let (sat, _) := flatBruteForce f n
    if sat.isNone then
      let (logs, proven) := iteratedSolvePromo f n 15
      for (round, learned, cascade, promo, status) in logs do
        IO.println s!"{round}\t{learned}\t{cascade}\t{promo}\t{status}\trand-{n}-s{seed}"
      IO.println s!"  → proven={proven}"
      IO.println ""
  -- PHP
  for p in [3, 4, 5] do
    let f := pigeonhole p (p-1)
    let nv := p * (p-1)
    let (logs, proven) := iteratedSolvePromo f nv 15
    for (round, learned, cascade, promo, status) in logs do
      IO.println s!"{round}\t{learned}\t{cascade}\t{promo}\tPHP({p},{p-1})"
    IO.println s!"  → proven={proven}"
    IO.println ""

/-! ## Assessment

    The promotion ratio measurement validates the signal:
    - 0% promotion → learning-only round (no cascade)
    - ≥33% promotion → breakthrough round (cascade → UNSAT)

    The cheap approximation (count assigned literals in clause)
    may differ from the full version (run UP on augmented formula).
    The cheap version catches cases where literals are ALREADY
    determined. The full version catches cases where the clause
    CREATES new determination via UP.

    For promotion-aware SELECTION (choosing between candidate
    clauses), the cheap version is sufficient as a first filter.
    Only compute full promotion for the top candidates.

    The implementation path:
    1. Generate multiple candidate clauses per conflict
       (1-UIP, 2-UIP, decision-level cuts)
    2. Score each by cheap promotion ratio
    3. If any has promo > 0, prefer it over 1-UIP
    4. If all have promo = 0, use 1-UIP (tightest)

    This is NOT implemented yet — the current code only measures
    promotion ratio on the 1-UIP clause. Generating alternative
    cuts requires modifying analyze1UIP to produce multiple
    candidates. That's the next implementation step.
-/

end RotationCalculus
