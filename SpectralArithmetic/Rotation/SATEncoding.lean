/-
  SAT as Tree Arrangement
  ========================

  Encode a SAT instance as a tree arrangement problem.

  Elements: one per literal. For n variables, 2n elements:
    (x1, true), (x1, false), (x2, true), (x2, false), ...

  Tree arrangement: group literals hierarchically. The tree shape
  is the decomposition strategy. The leaf placement determines
  which literals appear where.

  Constraint (two conditions checked simultaneously):
  1. CONSISTENCY: no variable appears with both values in the same
     branch path. The tree implicitly selects one value per variable
     by placing complementary literals in opposite subtrees.
  2. CLAUSE SATISFACTION: clauses are checked at the tree level
     where their variables first split apart.

  The key insight: in a tree, two literals are "resolved" at their
  lowest common ancestor. If x2=T is in the left subtree and x2=F
  is in the right subtree, they're resolved at the root. The
  constraint at the root sees both subtrees and can verify that
  exactly one value per variable crosses each split.

  For path-structured SAT (treewidth 1), the tree factorizes
  perfectly: each split resolves one variable, and the clause
  spanning that split involves only the resolved variable and its
  neighbor.
-/

import SpectralArithmetic.Rotation.Construction

namespace RotationCalculus

open Term

/-! ## Literal representation

    A literal is a (variable_index, polarity) pair.
    Encoded as a term: pair(pair(natToTerm var, polarity), ground)
    where polarity = pair(ground, ground) for true, ground for false.

    This gives each literal a unique term that treeSum and getLabel
    can distinguish. -/

/-- Encode a literal as a term.
    Variable index in [0, n). Polarity: true or false. -/
def literal (var : ℕ) (pol : Bool) : Term :=
  -- Encode as: label = 2*var + (if pol then 1 else 0)
  -- This gives each literal a unique natural number label.
  labeledElement (2 * var + if pol then 1 else 0)

/-- Extract variable index from a literal term. -/
def litVar (t : Term) : ℕ := getLabel t / 2

/-- Extract polarity from a literal term. -/
def litPol (t : Term) : Bool := getLabel t % 2 == 1

-- Verify encoding
#eval (litVar (literal 0 true), litPol (literal 0 true))    -- (0, true)
#eval (litVar (literal 0 false), litPol (literal 0 false))  -- (0, false)
#eval (litVar (literal 1 true), litPol (literal 1 true))    -- (1, true)
#eval (litVar (literal 2 false), litPol (literal 2 false))  -- (2, false)

/-- All literals for n variables. -/
def allLiterals (n : ℕ) : List Term :=
  (List.range n).flatMap fun v => [literal v true, literal v false]

#eval (allLiterals 3).map fun t => (litVar t, litPol t)
-- [(0,T), (0,F), (1,T), (1,F), (2,T), (2,F)]

/-! ## SAT instance representation -/

/-- A clause is a list of (variable, polarity) pairs (disjunction). -/
abbrev SATClause := List (ℕ × Bool)

/-- A SAT formula is a list of clauses (conjunction). -/
abbrev SATFormula := List SATClause

/-! ## Collecting assignments from a tree

    A tree arrangement of literals implicitly defines a partial
    assignment: the set of literals present in a subtree. For the
    arrangement to represent a valid assignment, each variable must
    appear exactly once (one polarity chosen). -/

/-- Collect all (variable, polarity) pairs from leaves of a tree. -/
def collectAssignment : Term → List (ℕ × Bool)
  | .ground => []
  | .pair a .ground => [(litVar (.pair a .ground), litPol (.pair a .ground))]
  | .pair a b => collectAssignment a ++ collectAssignment b
  | .observe t => collectAssignment t

/-- Check if an assignment is consistent: no variable has both values. -/
def isConsistent (assignment : List (ℕ × Bool)) : Bool :=
  assignment.all fun (v, p) =>
    !(assignment.any fun (v', p') => v == v' && p != p')

/-- Check if an assignment satisfies a clause.
    A clause is satisfied if at least one of its literals is in the assignment. -/
def satisfiesClause (assignment : List (ℕ × Bool)) (clause : SATClause) : Bool :=
  clause.any fun (v, p) =>
    assignment.any fun (v', p') => v == v' && p == p'

/-- Check if an assignment satisfies all clauses. -/
def satisfiesFormula (assignment : List (ℕ × Bool)) (formula : SATFormula) : Bool :=
  formula.all fun clause => satisfiesClause assignment clause

/-! ## The SAT tree constraint

    At each tree node, the constraint checks:
    1. The combined assignment from both subtrees is consistent
       (no variable appears with both polarities)
    2. All clauses whose variables are fully resolved at this level
       are satisfied

    For efficiency, we check a simpler condition:
    - The two subtrees have no variable in common with conflicting values
    - All clauses are satisfied by the combined assignment

    The full formula check at every node is redundant (it's checked
    at the root and inherited downward). But it's correct and simple.
    Optimization can come later. -/

/-- Check if all variables in a clause have been assigned. -/
def clauseResolved (assignment : List (ℕ × Bool)) (clause : SATClause) : Bool :=
  clause.all fun (v, _) =>
    assignment.any fun (v', _) => v == v'

/-- Build a SAT constraint from a formula.
    At each node, checks:
    1. Consistency: no variable has both polarities across subtrees
    2. Satisfaction: all RESOLVED clauses (where all variables are present)
       must be satisfied. Unresolved clauses are deferred to higher levels. -/
def satConstraint (formula : SATFormula) : Constraint where
  check := fun a b =>
    let leftAssign := collectAssignment a
    let rightAssign := collectAssignment b
    let combined := leftAssign ++ rightAssign
    -- Check consistency: no variable has both values
    let consistent := leftAssign.all fun (v, p) =>
      !(rightAssign.any fun (v', p') => v == v' && p != p')
    -- Check satisfaction: only check RESOLVED clauses
    let resolvedClauses := formula.filter fun clause =>
      clauseResolved combined clause
    let satisfied := resolvedClauses.all fun clause =>
      satisfiesClause combined clause
    consistent && satisfied

/-! ## Test instance 1: Path-structured SAT (treewidth 1)

    (x0 OR x1) AND (x1 OR x2) AND (x2 OR x3)

    This has treewidth 1 — the variable interaction graph is a path:
    x0 - x1 - x2 - x3

    Many satisfying assignments exist. The tree decomposition along
    the path should factorize perfectly. -/

def pathFormula : SATFormula :=
  [ [(0, true), (1, true)],     -- x0 OR x1
    [(1, true), (2, true)],     -- x1 OR x2
    [(2, true), (3, true)] ]    -- x2 OR x3

def pathLiterals := allLiterals 4  -- 8 elements

-- A manually constructed tree arrangement that should work:
-- Group by variable pairs: {x0, x1} and {x2, x3}
-- Within each pair, pick compatible values
-- x0=T, x1=T | x2=T, x3=T (all true satisfies everything)
def manualSAT : Term :=
  .pair (.pair (literal 0 true) (literal 1 true))
        (.pair (literal 2 true) (literal 3 true))

#eval
  let assign := collectAssignment manualSAT
  let consistent := isConsistent assign
  let satisfied := satisfiesFormula assign pathFormula
  (assign.map fun (v,p) => (v, p), consistent, satisfied)

-- Verify via the constraint
#eval verifyTree (satConstraint pathFormula) manualSAT

/-! ## Test instance 2: Triangle SAT (treewidth 2)

    (x0 OR x1) AND (x1 OR x2) AND (x0 OR x2)

    This has treewidth 2 — the interaction graph is a triangle (K3).
    No single variable split cleanly separates the clauses.
    Factorization should be harder. -/

def triangleFormula : SATFormula :=
  [ [(0, true), (1, true)],     -- x0 OR x1
    [(1, true), (2, true)],     -- x1 OR x2
    [(0, true), (2, true)] ]    -- x0 OR x2

def triangleLiterals := allLiterals 3  -- 6 elements

-- All-true satisfies this too
def manualTriangle : Term :=
  .pair (.pair (literal 0 true) (literal 1 true))
        (literal 2 true)

#eval verifyTree (satConstraint triangleFormula) manualTriangle

/-! ## Test instance 3: Unsatisfiable (pigeonhole-like)

    (x0) AND (NOT x0)
    Obviously unsatisfiable. No tree arrangement should work. -/

def unsatFormula : SATFormula :=
  [ [(0, true)],      -- x0
    [(0, false)] ]     -- NOT x0

def unsatLiterals := allLiterals 1  -- 2 elements

-- Try: pair(x0=T, x0=F) — inconsistent
#eval verifyTree (satConstraint unsatFormula)
  (.pair (literal 0 true) (literal 0 false))

-- Try: pair(x0=F, x0=T) — also inconsistent
#eval verifyTree (satConstraint unsatFormula)
  (.pair (literal 0 false) (literal 0 true))

/-! ## Flat brute-force SAT (baseline)

    Standard SAT solving: try all 2^n assignments, check each.
    No tree structure. This is the baseline to beat. -/

/-- Generate all truth assignments for n variables. -/
def allAssignments (n : ℕ) : List (List (ℕ × Bool)) :=
  match n with
  | 0 => [[]]
  | n + 1 =>
    let rest := allAssignments n
    rest.flatMap fun a => [(n, true) :: a, (n, false) :: a]

/-- Flat brute-force: try all 2^n assignments. Count checks. -/
def flatBruteForce (formula : SATFormula) (nVars : ℕ)
    : Option (List (ℕ × Bool)) × ℕ :=
  let assignments := allAssignments nVars
  let rec go : List (List (ℕ × Bool)) → ℕ
      → Option (List (ℕ × Bool)) × ℕ
    | [], cost => (none, cost)
    | a :: rest, cost =>
      if satisfiesFormula a formula then (some a, cost + 1)
      else go rest (cost + 1)
  go assignments 0

/-! ## Tree-decomposition SAT (the factorized approach)

    The key insight: don't enumerate complete assignments then check.
    Instead, SPLIT VARIABLES into groups using the tree structure,
    solve each group independently, and combine at the root.

    At each tree node:
    1. Split variables into left_vars and right_vars
    2. Find all valid partial assignments for left_vars
       (satisfying clauses involving ONLY left_vars)
    3. Find all valid partial assignments for right_vars
       (satisfying clauses involving ONLY right_vars)
    4. Combine: check cross-partition clauses

    For treewidth-k problems, each split has O(k) cross-partition
    clauses. The combination step is O(|left_solutions| × |right_solutions|).
    For low treewidth, the subtree solutions are few → fast combination.
    For high treewidth, many cross-clauses → less pruning. -/

/-- Get all variables mentioned in a formula. -/
def formulaVars (formula : SATFormula) : List ℕ :=
  (formula.flatMap fun clause =>
    clause.map fun (v, _) => v).eraseDups

/-- Filter clauses to those involving ONLY the given variables. -/
def clausesInScope (formula : SATFormula) (vars : List ℕ) : SATFormula :=
  formula.filter fun clause =>
    clause.all fun (v, _) => vars.contains v

/-- Filter clauses spanning two variable sets (involve vars from both). -/
def crossClauses (formula : SATFormula)
    (leftVars rightVars : List ℕ) : SATFormula :=
  formula.filter fun clause =>
    (clause.any fun (v, _) => leftVars.contains v) &&
    (clause.any fun (v, _) => rightVars.contains v)

/-- Tree-decomposition SAT solver.
    Splits variables, solves subtrees, combines.
    Returns (solution, operations_count). -/
partial def treeDecompSolve (formula : SATFormula)
    (vars : List ℕ)
    : List (List (ℕ × Bool)) × ℕ :=
  match vars with
  | [] => ([[]], 0)
  | [v] =>
    -- Base case: one variable. Try both values.
    let solutions := [true, false].filterMap fun pol =>
      let assign := [(v, pol)]
      let localClauses := clausesInScope formula [v]
      if satisfiesFormula assign localClauses then some assign
      else none
    (solutions, 2)  -- 2 operations (tried both values)
  | vs =>
    -- Split variables in half
    let mid := vs.length / 2
    let leftVars := vs.take mid
    let rightVars := vs.drop mid
    -- Solve left subtree (only left-local clauses)
    let (leftSolutions, leftCost) := treeDecompSolve formula leftVars
    -- Solve right subtree (only right-local clauses)
    let (rightSolutions, rightCost) := treeDecompSolve formula rightVars
    -- Combine: check cross-partition clauses
    let cross := crossClauses formula leftVars rightVars
    let pairs := leftSolutions.flatMap fun lSol =>
      rightSolutions.filterMap fun rSol =>
        let merged := lSol ++ rSol
        if satisfiesFormula merged cross then some merged
        else none
    let combineCost := leftSolutions.length * rightSolutions.length
    (pairs, leftCost + rightCost + combineCost)

/-- Wrapper: find first solution via tree decomposition. -/
def satTreeDecomp (formula : SATFormula) (nVars : ℕ)
    : Option (List (ℕ × Bool)) × ℕ :=
  let vars := List.range nVars
  let (solutions, cost) := treeDecompSolve formula vars
  -- Filter to only globally satisfying assignments
  let valid := solutions.filter fun a => satisfiesFormula a formula
  (valid.head?, cost)

/-! ## Test instances -/

/-! ### Instance A: Path formula (treewidth 1, 4 variables)

    (x0 OR x1) AND (NOT x1 OR x2) AND (NOT x2 OR NOT x3)

    Path structure: x0-x1-x2-x3. All-true FAILS (clause 3).
    Forces actual search. -/

def hardPath : SATFormula :=
  [ [(0, true), (1, true)],       -- x0 OR x1
    [(1, false), (2, true)],      -- NOT x1 OR x2
    [(2, false), (3, false)] ]    -- NOT x2 OR NOT x3

/-! ### Instance B: Dense formula (treewidth 3, 4 variables)

    (x0 OR x1) AND (x1 OR x2) AND (x2 OR x3) AND
    (x0 OR x3) AND (NOT x0 OR NOT x2)

    Nearly complete interaction graph. Every split has many
    cross-partition clauses. -/

def denseFormula : SATFormula :=
  [ [(0, true), (1, true)],       -- x0 OR x1
    [(1, true), (2, true)],       -- x1 OR x2
    [(2, true), (3, true)],       -- x2 OR x3
    [(0, true), (3, true)],       -- x0 OR x3
    [(0, false), (2, false)] ]    -- NOT x0 OR NOT x2

/-! ### Instance C: Longer path (treewidth 1, 6 variables)

    (x0 OR x1) AND (NOT x1 OR x2) AND (NOT x2 OR x3) AND
    (NOT x3 OR x4) AND (NOT x4 OR NOT x5)

    Path structure, 6 variables. Should show scaling. -/

def longPath : SATFormula :=
  [ [(0, true), (1, true)],       -- x0 OR x1
    [(1, false), (2, true)],      -- NOT x1 OR x2
    [(2, false), (3, true)],      -- NOT x2 OR x3
    [(3, false), (4, true)],      -- NOT x3 OR x4
    [(4, false), (5, false)] ]    -- NOT x4 OR NOT x5

/-! ## Head-to-head comparison -/

-- === Hard path (tw=1, 4 vars) ===
#eval
  let (r, c) := flatBruteForce hardPath 4
  (r, s!"flat-brute: {c} checks")

#eval
  let (r, c) := satTreeDecomp hardPath 4
  (r, s!"tree-decomp: {c} ops")

-- === Dense formula (tw=3, 4 vars) ===
#eval
  let (r, c) := flatBruteForce denseFormula 4
  (r, s!"flat-brute: {c} checks")

#eval
  let (r, c) := satTreeDecomp denseFormula 4
  (r, s!"tree-decomp: {c} ops")

-- === Long path (tw=1, 6 vars) ===
#eval
  let (r, c) := flatBruteForce longPath 6
  (r, s!"flat-brute: {c} checks")

#eval
  let (r, c) := satTreeDecomp longPath 6
  (r, s!"tree-decomp: {c} ops")

-- === Original path (easy, 4 vars) ===
#eval
  let (r, c) := flatBruteForce pathFormula 4
  (r, s!"flat-brute: {c} checks")

#eval
  let (r, c) := satTreeDecomp pathFormula 4
  (r, s!"tree-decomp: {c} ops")

-- === Unsatisfiable ===
#eval
  let (r, c) := flatBruteForce unsatFormula 1
  (r, s!"flat-brute: {c} checks")

#eval
  let (r, c) := satTreeDecomp unsatFormula 1
  (r, s!"tree-decomp: {c} ops")

/-! ## Hard instance: solution at the END of enumeration

    Force brute force to search most of the space.
    (NOT x0) AND (NOT x1) AND ... AND (NOT x_{n-1})
    Only solution: all false. Enumeration tries all-true first. -/

def allNegPath (n : ℕ) : SATFormula :=
  (List.range n).map fun v => [(v, false)]  -- each clause: NOT x_v

-- 6 variables: flat brute must try 2^6 = 64 assignments
-- (all-false is last in our enumeration order)
#eval
  let (r, c) := flatBruteForce (allNegPath 6) 6
  (r, s!"flat-brute-6: {c} checks")

#eval
  let (r, c) := satTreeDecomp (allNegPath 6) 6
  (r, s!"tree-decomp-6: {c} ops")

-- 8 variables: flat brute tries 2^8 = 256
#eval
  let (r, c) := flatBruteForce (allNegPath 8) 8
  (r, s!"flat-brute-8: {c} checks")

#eval
  let (r, c) := satTreeDecomp (allNegPath 8) 8
  (r, s!"tree-decomp-8: {c} ops")

-- 10 variables: flat brute tries 2^10 = 1024
#eval
  let (r, c) := flatBruteForce (allNegPath 10) 10
  (r, s!"flat-brute-10: {c} checks")

#eval
  let (r, c) := satTreeDecomp (allNegPath 10) 10
  (r, s!"tree-decomp-10: {c} ops")

/-! ## Assessment

    The comparison measures two things:

    1. DOES TREE DECOMPOSITION GIVE SPEEDUP?
       If tree-decomp cost << flat-brute cost for path instances,
       the tree structure provides genuine leverage.

    2. DOES TREEWIDTH PREDICT THE SPEEDUP?
       If the speedup is larger for path (tw=1) than dense (tw=3),
       treewidth correlates with factorizability.

    What this demonstrates (if speedup is observed):
    - The tree rotation framework naturally captures treewidth
    - The tree shape IS the decomposition
    - Splitting variables along the tree enables independent solving
    - The factorization speedup is real and measurable

    What this is:
    - Tree decomposition (Arnborg, Robertson-Seymour) implemented
      in the rotation calculus's term language
    - Not a new algorithm, but a new ENCODING of a known algorithm

    Why the encoding matters:
    - The same framework handles sorting, partition, AND SAT
    - The tree shape is always the strategy
    - The constraint always gates the rotation
    - Factorizability is always the complexity measure
    - P vs NP is always "does the constraint factorize?" -/

end RotationCalculus
