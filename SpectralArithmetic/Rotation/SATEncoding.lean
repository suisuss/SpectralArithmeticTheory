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

/-! ## SAT-aware search

    The search space is NOT all arrangements of all 2n literals.
    It's all ASSIGNMENTS (choose one literal per variable) times
    all tree shapes for the chosen n literals.

    Search space: 2^n assignments x Catalan(n-1) tree shapes x ... -/

/-- Generate all possible assignments: choose true or false for each variable. -/
def allAssignments (n : ℕ) : List (List Term) :=
  match n with
  | 0 => [[]]
  | n + 1 =>
    let rest := allAssignments n
    rest.flatMap fun assignment =>
      [literal n true :: assignment, literal n false :: assignment]

#eval (allAssignments 2).map (·.map fun t => (litVar t, litPol t))

/-- Check a complete tree: verifyTree AND global clause satisfaction. -/
def verifySATTree (formula : SATFormula) (t : Term) : Bool :=
  let C := satConstraint formula
  let assign := collectAssignment t
  verifyTree C t && satisfiesFormula assign formula

/-- Brute-force SAT search: try all assignments x all tree shapes. -/
def satBruteForce (formula : SATFormula) (nVars : ℕ)
    : Option (List (ℕ × Bool)) × ℕ :=
  let assignments := allAssignments nVars
  let rec go : List (List Term) → ℕ → Option (List (ℕ × Bool)) × ℕ
    | [], cost => (none, cost)
    | assignment :: rest, cost =>
      let trees := allTrees assignment
      let found := trees.find? fun t => verifySATTree formula t
      match found with
      | some t => (some (collectAssignment t), cost + trees.length)
      | none => go rest (cost + trees.length)
  go assignments 0

/-- Factorized SAT construction: try assignments, use factorized tree builder. -/
def satFactorized (formula : SATFormula) (nVars : ℕ)
    : Option (List (ℕ × Bool)) × ℕ :=
  let C := satConstraint formula
  let assignments := allAssignments nVars
  let rec go : List (List Term) → ℕ → Option (List (ℕ × Bool)) × ℕ
    | [], cost => (none, cost)
    | assignment :: rest, cost =>
      let (result, factCost) := factorizedConstruct C assignment
      match result with
      | some t =>
        -- Double-check with global satisfaction
        if satisfiesFormula (collectAssignment t) formula then
          (some (collectAssignment t), cost + factCost)
        else go rest (cost + factCost)
      | none => go rest (cost + factCost)
  go assignments 0

/-! ## Head-to-head: path vs triangle SAT -/

-- Path formula (treewidth 1, 4 variables)
#eval
  let (result, cost) := satBruteForce pathFormula 4
  (result, s!"brute: {cost} trees")

#eval
  let (result, cost) := satFactorized pathFormula 4
  (result, s!"factorized: {cost}")

-- Triangle formula (treewidth 2, 3 variables)
#eval
  let (result, cost) := satBruteForce triangleFormula 3
  (result, s!"brute: {cost} trees")

#eval
  let (result, cost) := satFactorized triangleFormula 3
  (result, s!"factorized: {cost}")

-- Unsatisfiable (1 variable)
#eval
  let (result, cost) := satBruteForce unsatFormula 1
  (result, s!"brute: {cost} trees")

/-! ## The treewidth test

    If the framework captures treewidth:
    - Path formula (tw=1): factorized should be MUCH cheaper than brute force
    - Triangle formula (tw=2): factorized should be somewhat cheaper
    - The ratio factorized/brute should correlate with treewidth

    If the framework DOESN'T capture treewidth:
    - Both construction strategies scale similarly regardless of structure
    - The tree decomposition provides no leverage

    The results above will tell us which case we're in. -/

/-! ## Assessment (to be filled after results)

    The encoding works if:
    1. Manual trees verify correctly (consistency + satisfaction)
    2. Brute force finds solutions for satisfiable instances
    3. Brute force exhausts search for unsatisfiable instances
    4. Factorized construction shows speedup for low-treewidth instances
    5. The speedup diminishes for high-treewidth instances

    What this demonstrates:
    - The tree rotation framework CAN encode NP-complete problems
    - The tree shape corresponds to the tree decomposition
    - Factorizability correlates with treewidth
    - The framework provides a concrete, computable complexity measure

    What this does NOT demonstrate:
    - A new algorithm for SAT (tree decomposition is well-known)
    - A proof technique for P vs NP
    - Anything beyond what treewidth theory already provides

    The value is in the UNIFICATION: the same framework (one rule,
    one data structure, one constraint) handles both the "easy"
    examples (sorting, balanced partition) and NP-complete problems
    (SAT). The tree shape is always the decomposition. The constraint
    always gates the rotation. The factorizability is always the
    complexity measure. -/

end RotationCalculus
