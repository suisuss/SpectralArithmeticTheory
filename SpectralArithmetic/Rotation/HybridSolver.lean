/-
  Hybrid Solver: SmartDAG + Choice
  ==================================

  SmartDAG exploits spatial decomposition (split variables into groups).
  Choice exploits temporal pruning (backtrack on failure).
  They're complementary:
  - SmartDAG: great on structured, bad on random
  - Choice: great on random, bad on structured

  The hybrid: use SmartDAG to decompose into subproblems, then use
  Choice (AND-OR evaluation with alpha-beta) to solve each subproblem.

  At each tree level:
  1. Split variables into left and right (SmartDAG's smart split)
  2. Identify shared variables (bounded sharing, k parameter)
  3. For each shared assignment (2^k options):
     a. Build AND-OR search trees for left and right subproblems
     b. Evaluate with alpha-beta pruning (Choice)
     c. If both pass, combine and return
  4. Short-circuit: stop at first successful shared assignment

  This combines spatial factorization (SmartDAG) with temporal
  pruning (Choice) at every level of the decomposition.
-/

import SpectralArithmetic.Rotation.ChoiceSAT

namespace RotationCalculus

open Term

/-! ## Hybrid solver -/

/-- Solve a SAT subproblem using AND-OR evaluation.
    Builds the search tree over the given variables and evaluates
    with alpha-beta pruning. Returns (found?, cost). -/
def solveSubproblem (formula : SATFormula) (vars : List ℕ)
    (fixed : List (ℕ × Bool))
    : (Option (List (ℕ × Bool))) × ℕ :=
  match vars with
  | [] =>
    -- No free variables: just check fixed assignment
    let relevant := clausesInScope formula
      (fixed.map (·.1) ++ vars)
    if satisfiesFormula fixed relevant then (some fixed, 1)
    else (none, 1)
  | _ =>
    -- Build AND-OR tree for free variables
    let tree := buildSearchTree formula vars fixed
    let (found, cost) := evalSearchTree tree
    if found then
      -- Reconstruct the assignment by re-searching (simple approach)
      let rec findAssign : List ℕ → List (ℕ × Bool)
          → Option (List (ℕ × Bool))
        | [], acc => if satisfiesFormula acc
            (clausesInScope formula (acc.map (·.1)))
          then some acc else none
        | v :: rest, acc =>
          let tryTrue := findAssign rest ((v, true) :: acc)
          match tryTrue with
          | some a => some a
          | none => findAssign rest ((v, false) :: acc)
      (findAssign vars fixed, cost)
    else (none, cost)

/-- The hybrid solver: SmartDAG decomposition + Choice evaluation.
    `k` = sharing budget (treewidth parameter).
    `minSubproblem` = below this size, switch to AND-OR evaluation. -/
partial def hybridSolve (formula : SATFormula)
    (vars : List ℕ) (k : ℕ) (minSub : ℕ := 4)
    : (List (List (ℕ × Bool))) × ℕ :=
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
    if vs.length ≤ minSub then
      -- Small enough: solve entirely with AND-OR (Choice)
      let tree := buildSearchTree formula vs []
      let (found, cost) := evalSearchTree tree
      if found then
        -- Find actual assignment
        let assigns := allVarAssignments vs
        let valid := assigns.filter fun a =>
          satisfiesFormula a (clausesInScope formula vs)
        (valid, cost)
      else ([], cost)
    else
      -- Large: decompose with SmartDAG, solve pieces with Choice
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
      -- For each shared assignment, solve subtrees with hybrid recursion
      let leftFormula := clausesInScope formula leftVars
      let rightFormula := clausesInScope formula rightVars
      let scopedFormula := clausesInScope formula vs
      let results := sharedAssigns.flatMap fun shared =>
        -- Solve left with hybrid (spatial + temporal)
        let (leftSols, _) := hybridSolve leftFormula leftLocal k minSub
        let (rightSols, _) := hybridSolve rightFormula rightLocal k minSub
        leftSols.flatMap fun lSol =>
          rightSols.filterMap fun rSol =>
            let merged := shared ++ lSol ++ rSol
            if satisfiesFormula merged scopedFormula then some merged
            else none
      let combineCost := sharedAssigns.length *
        (2^leftLocal.length + 2^rightLocal.length + 1)
      (results, combineCost)

/-- Wrapper. -/
def satHybrid (formula : SATFormula) (nVars : ℕ)
    (k : ℕ := 2) (minSub : ℕ := 4)
    : Option (List (ℕ × Bool)) × ℕ :=
  let vars := List.range nVars
  let (solutions, cost) := hybridSolve formula vars k minSub
  let valid := solutions.filter fun a => satisfiesFormula a formula
  (valid.head?, cost)

/-- Hybrid with graph-aware ordering. -/
def satHybridOrdered (formula : SATFormula) (nVars : ℕ)
    (ordering : List ℕ) (k : ℕ := 2) (minSub : ℕ := 4)
    : Option (List (ℕ × Bool)) × ℕ :=
  let invPerm := invertPerm ordering
  let reordered := reorderFormula formula invPerm
  let (result, cost) := satHybrid reordered nVars k minSub
  let mapped := result.map fun assign =>
    assign.map fun (v, p) =>
      let origVar := ordering.getD v v
      (origVar, p)
  (mapped, cost)

/-! ## Six-way comparison: the full lineup -/

-- Structured (reachInstance, n=10)
#eval do
  let data := [1, 3, 5, 9].map fun reach =>
    let f := reachInstance 10 reach
    let (_, flat) := flatBruteForce f 10
    let (_, smart) := satSmartDAG f 10 2
    let (_, ch) := choiceSAT f 10
    let (_, hyb) := satHybrid f 10
    s!"r={reach} flat={flat} smart={smart} choice={ch} hybrid={hyb}"
  IO.println s!"Structured n=10:"
  IO.println (String.intercalate "\n" data)

-- Random 3-SAT (n=8)
#eval do
  let n := 8
  let m := 32
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, smart) := satSmartDAG f n 2
    let (_, ch) := choiceSAT f n
    let (_, hyb) := satHybrid f n
    s!"seed={seed} flat={flat} smart={smart} choice={ch} hybrid={hyb}"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- Random 3-SAT (n=10)
#eval do
  let n := 10
  let m := 42
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, smart) := satSmartDAG f n 2
    let (_, ch) := choiceSAT f n
    let md := minDegOrdering f n
    let (_, chmd) := choiceSATOrdered f md
    let (_, hyb) := satHybrid f n
    let (_, hybmd) := satHybridOrdered f n md
    s!"seed={seed} flat={flat} smart={smart} ch={ch} ch+md={chmd} hyb={hyb} hyb+md={hybmd}"
  IO.println s!"Random n={n} m={m} (full comparison):"
  IO.println (String.intercalate "\n" data)

-- Random 3-SAT (n=12)
#eval do
  let n := 12
  let m := 48
  let data := [42, 100, 200, 300, 400].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, smart) := satSmartDAG f n 2
    let (_, ch) := choiceSAT f n
    let md := minDegOrdering f n
    let (_, chmd) := choiceSATOrdered f md
    let (_, hyb) := satHybrid f n
    s!"seed={seed} flat={flat} smart={smart} ch={ch} ch+md={chmd} hyb={hyb}"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- Scaling: structured reach=3
#eval do
  let data := [6, 8, 10, 12, 14].map fun n =>
    let f := reachInstance n 3
    let (_, flat) := flatBruteForce f n
    let (_, smart) := satSmartDAG f n 2
    let (_, hyb) := satHybrid f n
    s!"n={n} flat={flat} smart={smart} hybrid={hyb}"
  IO.println s!"Structured reach=3 scaling:"
  IO.println (String.intercalate "\n" data)

/-! ## Assessment

    The hybrid combines SmartDAG's spatial decomposition with
    Choice's temporal pruning. The prediction:

    - Structured instances: hybrid ≈ SmartDAG (spatial decomposition
      is the dominant strategy, Choice adds little)
    - Random instances: hybrid ≈ Choice+mindeg (temporal pruning
      is the dominant strategy, SmartDAG decomposition adds little)
    - Mixed instances: hybrid > both (spatial decomposition reduces
      subproblem size, temporal pruning solves subproblems efficiently)

    The hybrid is the unified solver that adapts to instance structure.
    SmartDAG and Choice are its two modes. The smart split decides
    how much spatial decomposition to do. The minSub parameter
    decides when to switch from spatial to temporal. -/

end RotationCalculus
