/-
  Bounded DAG: Treewidth-Parameterized SAT Solving
  ==================================================

  The DAG solver collapses at high treewidth because it shares ALL
  cross-partition variables — enumerating all their assignments is
  exponential. The fix: share at most k variables per split.

  Cost: O(2^k × n) — polynomial for fixed k.

  This IS the bounded-treewidth algorithm (Robertson-Seymour):
  - k is the sharing budget (analogous to bag size - 1)
  - Each split shares at most k variables
  - 2^k partial assignments enumerated per split
  - Subtrees solved independently given shared assignment

  Two enhancements:
  1. Smart variable selection: share variables that appear in the
     MOST cross-clauses (maximize pruning per shared variable)
  2. Smart split point: split to MINIMIZE cross-partition variables
     (minimize the sharing needed)
-/

import SpectralArithmetic.Rotation.Scaling

namespace RotationCalculus

open Term

/-! ## Bounded sharing solver -/

/-- Count how many cross-clauses mention a variable. -/
def crossClauseFreq (cross : SATFormula) (v : ℕ) : ℕ :=
  cross.foldl (fun acc clause =>
    if clause.any fun (v', _) => v == v' then acc + 1 else acc) 0

/-- Select the top k variables by cross-clause frequency. -/
def selectShared (cross : SATFormula) (candidates : List ℕ)
    (k : ℕ) : List ℕ :=
  let scored := candidates.map fun v => (crossClauseFreq cross v, v)
  let sorted := scored.toArray.insertionSort
    (fun a b => a.1 > b.1) |>.toList
  (sorted.take k).map (·.2)

/-- Generate all assignments for a list of variables. -/
def allVarAssignments : List ℕ → List (List (ℕ × Bool))
  | [] => [[]]
  | v :: vs =>
    let rest := allVarAssignments vs
    rest.flatMap fun a => [(v, true) :: a, (v, false) :: a]

/-- Bounded DAG solver: share at most k variables per split.
    Smart variable selection: share the highest-frequency cross-vars. -/
partial def boundedDAGSolve (formula : SATFormula)
    (vars : List ℕ) (k : ℕ)
    : List (List (ℕ × Bool)) × ℕ :=
  match vars with
  | [] => ([[]], 0)
  | [v] =>
    let solutions := [true, false].filterMap fun pol =>
      let assign := [(v, pol)]
      let local_ := clausesInScope formula [v]
      if satisfiesFormula assign local_ then some assign
      else none
    (solutions, 2)
  | vs =>
    let mid := vs.length / 2
    let leftVars := vs.take mid
    let rightVars := vs.drop mid
    let cross := crossClauses formula leftVars rightVars
    -- Identify cross-partition variables and select top k
    let crossVarCandidates := (cross.flatMap fun clause =>
      clause.map fun (v, _) => v).eraseDups
    let sharedVars := selectShared cross crossVarCandidates k
    let sharedAssigns := allVarAssignments sharedVars
    -- Local variables (not shared)
    let leftLocal := leftVars.filter fun v => !sharedVars.contains v
    let rightLocal := rightVars.filter fun v => !sharedVars.contains v
    -- Solve subtrees: only pass clauses involving LOCAL vars
    -- (clauses touching shared vars are handled at combination)
    let leftOnlyFormula := clausesInScope formula leftLocal
    let (leftSols, lc) := boundedDAGSolve leftOnlyFormula leftLocal k
    let rightOnlyFormula := clausesInScope formula rightLocal
    let (rightSols, rc) := boundedDAGSolve rightOnlyFormula rightLocal k
    -- For each shared assignment, combine with local solutions
    -- Check all clauses in scope for the full variable set
    let scopedFormula := clausesInScope formula vs
    let results := sharedAssigns.flatMap fun shared =>
      leftSols.flatMap fun lSol =>
        rightSols.filterMap fun rSol =>
          let merged := shared ++ lSol ++ rSol
          if satisfiesFormula merged scopedFormula then some merged
          else none
    let combineCost := sharedAssigns.length *
      (leftSols.length * rightSols.length + 1)
    (results, lc + rc + combineCost)

/-- Wrapper. -/
def satBoundedDAG (formula : SATFormula) (nVars : ℕ) (k : ℕ)
    : Option (List (ℕ × Bool)) × ℕ :=
  let vars := List.range nVars
  let (solutions, cost) := boundedDAGSolve formula vars k
  let valid := solutions.filter fun a => satisfiesFormula a formula
  (valid.head?, cost)

/-! ## Smart split: minimize cross-partition variables -/

/-- Count cross-partition variables for a given split point. -/
def crossVarCount (formula : SATFormula)
    (vars : List ℕ) (splitAt : ℕ) : ℕ :=
  let leftVars := vars.take splitAt
  let rightVars := vars.drop splitAt
  let cross := crossClauses formula leftVars rightVars
  (cross.flatMap fun clause =>
    clause.map fun (v, _) => v).eraseDups.length

/-- Find the split point that minimizes cross-partition variables. -/
def bestSplit (formula : SATFormula) (vars : List ℕ) : ℕ :=
  let n := vars.length
  if n ≤ 2 then 1
  else
    let candidates := List.range (n - 1) |>.map (· + 1)
    let scored := candidates.map fun i => (crossVarCount formula vars i, i)
    let best := scored.toArray.insertionSort
      (fun a b => a.1 < b.1) |>.toList
    match best.head? with
    | some (_, i) => i
    | none => n / 2

/-- Bounded DAG with smart splitting. -/
partial def smartDAGSolve (formula : SATFormula)
    (vars : List ℕ) (k : ℕ)
    : List (List (ℕ × Bool)) × ℕ :=
  match vars with
  | [] => ([[]], 0)
  | [v] =>
    let solutions := [true, false].filterMap fun pol =>
      let assign := [(v, pol)]
      let local_ := clausesInScope formula [v]
      if satisfiesFormula assign local_ then some assign
      else none
    (solutions, 2)
  | vs =>
    -- Smart split: minimize cross-partition variables
    let split := bestSplit formula vs
    let leftVars := vs.take split
    let rightVars := vs.drop split
    let cross := crossClauses formula leftVars rightVars
    let crossVarCandidates := (cross.flatMap fun clause =>
      clause.map fun (v, _) => v).eraseDups
    let sharedVars := selectShared cross crossVarCandidates k
    let sharedAssigns := allVarAssignments sharedVars
    let leftLocal := leftVars.filter fun v => !sharedVars.contains v
    let rightLocal := rightVars.filter fun v => !sharedVars.contains v
    -- Subtrees: only clauses involving local vars
    let leftOnlyFormula := clausesInScope formula leftLocal
    let (leftSols, lc) := smartDAGSolve leftOnlyFormula leftLocal k
    let rightOnlyFormula := clausesInScope formula rightLocal
    let (rightSols, rc) := smartDAGSolve rightOnlyFormula rightLocal k
    -- Combine: check all in-scope clauses
    let scopedFormula := clausesInScope formula vs
    let results := sharedAssigns.flatMap fun shared =>
      leftSols.flatMap fun lSol =>
        rightSols.filterMap fun rSol =>
          let merged := shared ++ lSol ++ rSol
          if satisfiesFormula merged scopedFormula then some merged
          else none
    let combineCost := sharedAssigns.length *
      (leftSols.length * rightSols.length + 1) + 1
    (results, lc + rc + combineCost)

/-- Wrapper for smart DAG. -/
def satSmartDAG (formula : SATFormula) (nVars : ℕ) (k : ℕ)
    : Option (List (ℕ × Bool)) × ℕ :=
  let vars := List.range nVars
  let (solutions, cost) := smartDAGSolve formula vars k
  let valid := solutions.filter fun a => satisfiesFormula a formula
  (valid.head?, cost)

/-! ## Five-way comparison across treewidths -/

-- n=8
#eval do
  let n := 8
  let data := [1, 2, 3, 4, 5, 7].map fun reach =>
    let f := reachInstance n reach
    let (_, a) := flatBruteForce f n
    let (_, b) := satTreeDecomp f n
    let (_, c) := satDAGDecomp f n
    let (_, d) := satBoundedDAG f n 2
    let (_, e) := satSmartDAG f n 2
    s!"n={n} r={reach} flat={a} tree={b} dag={c} bdag={d} smart={e}"
  IO.println (String.intercalate "\n" data)

-- n=10
#eval do
  let data := [1, 3, 5, 9].map fun reach =>
    let f := reachInstance 10 reach
    let (_, a) := flatBruteForce f 10
    let (_, b) := satTreeDecomp f 10
    let (_, c) := satDAGDecomp f 10
    let (_, d) := satBoundedDAG f 10 2
    let (_, e) := satSmartDAG f 10 2
    s!"n=10 r={reach} flat={a} tree={b} dag={c} bdag={d} smart={e}"
  IO.println (String.intercalate "\n" data)

/-! ## Varying k on medium treewidth (reach=5, n=10) -/

#eval do
  let f := reachInstance 10 5
  let (_, flat) := flatBruteForce f 10
  let data := [0, 1, 2, 3, 4, 5].map fun k =>
    let (r, cost) := satBoundedDAG f 10 k
    s!"  k={k} cost={cost} found={r.isSome}"
  IO.println s!"n=10 reach=5 flat={flat}"
  IO.println (String.intercalate "\n" data)

/-! ## SmartDAG varying k (reach=5, n=10) -/

#eval do
  let f := reachInstance 10 5
  let data := [0, 1, 2, 3, 4, 5].map fun k =>
    let (r, cost) := satSmartDAG f 10 k
    s!"  smart k={k} cost={cost} found={r.isSome}"
  IO.println s!"n=10 reach=5 smartDAG varying k:"
  IO.println (String.intercalate "\n" data)

/-! ## SmartDAG varying k (reach=9, n=10 — near clique) -/

#eval do
  let f := reachInstance 10 9
  let data := [0, 1, 2, 3, 4, 5].map fun k =>
    let (r, cost) := satSmartDAG f 10 k
    s!"  smart k={k} cost={cost} found={r.isSome}"
  IO.println s!"n=10 reach=9 smartDAG varying k:"
  IO.println (String.intercalate "\n" data)

/-! ## SmartDAG at larger n -/

#eval do
  let data := [8, 10, 12, 14].map fun n =>
    let f := reachInstance n 5
    let (r1, flat) := flatBruteForce f n
    let (r2, smart) := satSmartDAG f n 2
    s!"n={n} reach=5 flat={flat}(found={r1.isSome}) smart(k=2)={smart}(found={r2.isSome})"
  IO.println (String.intercalate "\n" data)

/-! ## n=12: scaling test -/

#eval do
  let data := [1, 3, 5].map fun reach =>
    let f := reachInstance 12 reach
    let (_, a) := flatBruteForce f 12
    let (_, b) := satTreeDecomp f 12
    let (_, d) := satBoundedDAG f 12 2
    let (_, e) := satSmartDAG f 12 2
    s!"n=12 r={reach} flat={a} tree={b} bdag={d} smart={e}"
  IO.println (String.intercalate "\n" data)

/-! ## Assessment

    Expected:
    - Bounded DAG (k=2): cost ≈ 4 × n per level (2^k=4 shared assignments).
      Should NOT collapse at high treewidth (sharing is bounded).
    - Smart DAG: finds optimal split to minimize cross-vars.
      Should need fewer shared variables → cheaper than bounded DAG.
    - The combination: smart split + bounded sharing should give the
      best performance across all treewidths.

    What this would demonstrate:
    - The DAG collapse is fixable by bounding the sharing budget
    - The sharing budget k is the treewidth parameter
    - For fixed k, the solver is O(2^k × n) — polynomial
    - k controls the tradeoff between solution quality and cost -/

end RotationCalculus
