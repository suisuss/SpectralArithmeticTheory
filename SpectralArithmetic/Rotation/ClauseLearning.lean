/-
  Clause Learning: From Tree-like to General Resolution
  ======================================================

  Choice+mindeg = DPLL = tree-like resolution.
  CDCL = DPLL + clause learning = general resolution.

  The key addition: when a branch fails, analyze WHY it failed
  and add a learned clause that prevents the same failure pattern
  in other branches. This is the exponential improvement from
  tree-like to general resolution.

  Implementation:
  - The evaluator maintains a list of learned clauses
  - On failure: extract the conflicting partial assignment
  - Derive a learned clause (negation of the conflict)
  - Add it to the formula for remaining branches
  - The constraint EVOLVES during search

  This is meta-rewriting: the constraint is no longer static.
  Each failure modifies the formula, which changes the pruning
  power of subsequent branches.
-/

import SpectralArithmetic.Rotation.AdaptiveSolver

namespace RotationCalculus

open Term

/-! ## Conflict analysis

    When a partial assignment fails, the conflict is the set of
    assignments that together caused the failure. The learned
    clause is the negation: "don't assign all of these simultaneously." -/

/-- A conflict: a partial assignment that violates some clause. -/
abbrev Conflict := List (ℕ × Bool)

/-- Find which clause is violated by a partial assignment.
    Returns the violated clause (if any). -/
def findConflict (formula : SATFormula) (assign : List (ℕ × Bool))
    : Option SATClause :=
  formula.find? fun clause =>
    -- Clause is violated if ALL its literals are falsified
    clause.all fun (v, p) =>
      assign.any fun (v', p') => v == v' && p != p'

/-- Derive a learned clause from a conflict.
    The learned clause is the negation of the conflicting assignment:
    "at least one of these variables must have a different value." -/
def learnClause (conflict : Conflict) : SATClause :=
  conflict.map fun (v, p) => (v, !p)

/-! ## CDCL-style evaluator

    Like the Choice evaluator but maintains a growing formula.
    Each failure adds a learned clause. Subsequent branches
    check the learned clauses too, enabling cross-branch pruning. -/

/-- CDCL search: backtracking with clause learning.
    `formula` is the CURRENT formula (original + learned clauses).
    `vars` is the remaining unassigned variables.
    `assign` is the current partial assignment.
    Returns (found, cost, learned_clauses). -/
partial def cdclSearch (formula : SATFormula) (vars : List ℕ)
    (assign : List (ℕ × Bool))
    : (Bool × ℕ × List SATClause) :=
  -- Check if current assignment violates any clause
  let conflict := findConflict formula assign
  match conflict with
  | some _ =>
    -- Conflict! Learn a clause from the current assignment.
    -- Simplification: learn the negation of the full current assignment.
    -- Real CDCL does 1-UIP analysis for shorter clauses.
    let learned := learnClause assign
    (false, 1, [learned])
  | none =>
    match vars with
    | [] =>
      -- All variables assigned, no conflict → solution found
      (true, 1, [])
    | v :: rest =>
      -- Try v = true
      let assignTrue := (v, true) :: assign
      let (foundT, costT, learnedT) := cdclSearch formula rest assignTrue
      if foundT then (true, costT + 1, learnedT)
      else
        -- Add learned clauses from the true branch
        let formula' := formula ++ learnedT
        -- Try v = false (with learned clauses!)
        let assignFalse := (v, false) :: assign
        let (foundF, costF, learnedF) := cdclSearch formula' rest assignFalse
        (foundF, costT + costF + 1, learnedT ++ learnedF)

/-- Wrapper: CDCL solver. -/
def satCDCL (formula : SATFormula) (nVars : ℕ)
    : (Bool × ℕ × ℕ) :=  -- (found, cost, clauses_learned)
  let vars := List.range nVars
  let (found, cost, learned) := cdclSearch formula vars []
  (found, cost, learned.length)

/-- CDCL with min-degree variable ordering. -/
def satCDCLOrdered (formula : SATFormula) (ordering : List ℕ)
    : (Bool × ℕ × ℕ) :=
  let (found, cost, learned) := cdclSearch formula ordering []
  (found, cost, learned.length)

/-! ## Head-to-head: DPLL vs CDCL

    DPLL = Choice evaluator (no learning).
    CDCL = Choice evaluator + clause learning.

    On satisfiable instances: both find solutions, CDCL may be
    faster due to learned clause pruning.

    On UNSATISFIABLE instances: CDCL should be dramatically faster.
    Tree-like resolution (DPLL) needs exponential proofs for some
    formulas. General resolution (CDCL) needs polynomial proofs. -/

-- === Random 3-SAT (satisfiable), n=8 ===

#eval do
  let n := 8
  let m := 32
  let data := [42, 123, 456].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, dpll) := choiceSAT f n
    let md := minDegOrdering f n
    let (_, dpllMd) := choiceSATOrdered f md
    let (found, cdclCost, learned) := satCDCL f n
    let (foundMd, cdclMdCost, learnedMd) := satCDCLOrdered f md
    s!"seed={seed} flat={flat} dpll={dpll} dpll+md={dpllMd} cdcl={cdclCost}(L={learned}) cdcl+md={cdclMdCost}(L={learnedMd})"
  IO.println s!"SAT n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- === Random 3-SAT, n=10 ===

#eval do
  let n := 10
  let m := 42
  let data := [42, 123, 456].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let md := minDegOrdering f n
    let (_, dpllMd) := choiceSATOrdered f md
    let (_, cdclCost, learned) := satCDCL f n
    let (_, cdclMdCost, learnedMd) := satCDCLOrdered f md
    s!"seed={seed} flat={flat} dpll+md={dpllMd} cdcl={cdclCost}(L={learned}) cdcl+md={cdclMdCost}(L={learnedMd})"
  IO.println s!"SAT n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- === UNSATISFIABLE instances ===
-- This is where CDCL should shine vs DPLL.

/-- Build an unsatisfiable formula: pigeonhole principle.
    n+1 pigeons, n holes. Each pigeon must be in some hole,
    no two pigeons in the same hole. Unsatisfiable. -/
def pigeonhole (pigeons holes : ℕ) : SATFormula :=
  -- Variable v(p, h) = pigeon p is in hole h
  -- Encoded as variable index: p * holes + h
  let var (p h : ℕ) := p * holes + h
  -- Each pigeon in at least one hole
  let atLeastOne := (List.range pigeons).map fun p =>
    (List.range holes).map fun h => (var p h, true)
  -- No two pigeons in same hole
  let atMostOne := (List.range holes).flatMap fun h =>
    (List.range pigeons).flatMap fun p1 =>
      (List.range pigeons).filterMap fun p2 =>
        if p1 < p2 then some [(var p1 h, false), (var p2 h, false)]
        else none
  atLeastOne ++ atMostOne

-- PHP(3,2): 3 pigeons, 2 holes. 6 variables. UNSAT.
#eval do
  let f := pigeonhole 3 2
  let n := 6
  let (_, flat) := flatBruteForce f n
  let (_, dpll) := choiceSAT f n
  let (found, cdclCost, learned) := satCDCL f n
  IO.println s!"PHP(3,2): flat={flat} dpll={dpll} cdcl={cdclCost}(L={learned}) found={found}"

-- PHP(4,3): 4 pigeons, 3 holes. 12 variables. UNSAT.
#eval do
  let f := pigeonhole 4 3
  let n := 12
  let (_, flat) := flatBruteForce f n
  let (_, dpll) := choiceSAT f n
  let (found, cdclCost, learned) := satCDCL f n
  IO.println s!"PHP(4,3): flat={flat} dpll={dpll} cdcl={cdclCost}(L={learned}) found={found}"

-- === Structured UNSAT ===

#eval do
  let f := unsatFormula  -- (x0) AND (NOT x0)
  let (_, dpll) := choiceSAT f 1
  let (found, cdclCost, learned) := satCDCL f 1
  IO.println s!"trivial-unsat: dpll={dpll} cdcl={cdclCost}(L={learned}) found={found}"

-- === Scaling: structured reach instances ===

#eval do
  let data := [8, 10, 12, 14].map fun n =>
    let f := reachInstance n 3
    let (_, smart) := satSmartDAG f n 2
    let (_, dpll) := choiceSAT f n
    let (_, cdclCost, learned) := satCDCL f n
    s!"n={n} smart={smart} dpll={dpll} cdcl={cdclCost}(L={learned})"
  IO.println s!"Structured reach=3:"
  IO.println (String.intercalate "\n" data)

/-! ## Assessment

    CDCL adds clause learning to the Choice evaluator.
    The learned clauses are the constraint evolving during search.
    This is meta-rewriting: the formula changes as you explore.

    Expected behavior:
    - SAT instances: CDCL ≈ DPLL (learning helps little when
      solutions are found quickly)
    - UNSAT instances: CDCL << DPLL (learned clauses prune
      exponentially many branches)
    - Pigeonhole: exponential gap (tree-like resolution needs
      2^Ω(n) for PHP, general resolution needs O(n^3))

    What this implements in proof complexity terms:
    - DPLL (Choice) = tree-like resolution proofs
    - CDCL (this file) = general resolution proofs
    - Learned clauses = resolution steps that combine inferences
      from different branches of the search tree

    Limitation: our "learning" is naive — it learns the full
    conflicting assignment. Real CDCL uses 1-UIP (first unique
    implication point) to derive shorter, more general clauses.
    Shorter learned clauses prune more branches. This is where
    the Ben-Sasson-Wigderson "short proofs are narrow" result
    connects: narrow clauses enable short proofs. -/

end RotationCalculus
