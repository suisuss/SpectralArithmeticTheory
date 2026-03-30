/-
  Tree Rotation: Complexity Hierarchy
  ====================================

  TreeArrangement.lean showed that tree arrangements escape the flat-list
  CSP equivalence. This file investigates whether the tree structure
  provides a genuine complexity characterization.

  Key idea: a tree arrangement decomposes the problem into LEVELS.
  At each level, the constraint restricts how elements can be split.
  If each level's constraint is independently solvable in polynomial
  time, the whole tree can be built top-down (greedy/D&C). If any
  level is NP-hard, the whole problem is NP-hard.

  Test cases:
  - Size-balanced constraint: easy at every level → polynomial
  - Sorted-leaves constraint: easy at every level → polynomial
  - Sum-balanced constraint: NP-hard at level 1 → NP-hard overall
-/

import SpectralArithmetic.Rotation.TreeArrangement

namespace RotationCalculus

open Term

/-! ## Constraint 1: Size-balanced (easy)

    At each tree level, the left and right subtrees must have
    roughly equal numbers of leaves (differ by at most 1).

    Solvable greedily: at each level, split elements in half.
    Any split of ⌊n/2⌋ and ⌈n/2⌉ works. O(n log n) total. -/

def sizeBalancedConstraint : Constraint where
  check := fun a b =>
    if isNode a && isNode b then
      let la := leafCount a
      let lb := leafCount b
      let diff := if la ≥ lb then la - lb else lb - la
      diff ≤ 1
    else
      true

-- Size-balanced: ((1,2),(3,4)) balanced, (1,(2,(3,4))) unbalanced
def sizebal_good : Term := .pair (.pair e1 e2) (.pair e3 e4)
def sizebal_bad : Term := .pair e1 (.pair e2 (.pair e3 e4))

#eval verifyTree sizeBalancedConstraint sizebal_good   -- true
#eval verifyTree sizeBalancedConstraint sizebal_bad    -- true (leaf vs compound → passes)

-- sizebal_bad passes because e1 is a leaf (not a node), so the
-- size check never fires. This highlights: the constraint only
-- engages when BOTH children are compound subtrees.

-- A tree where both sides are compound but unequal:
-- ((1,2,3),(4)) encoded as pair (pair e1 (pair e2 e3)) e4
-- But e4 is a leaf, so the check doesn't fire either.

-- For the check to fire AND fail, we need both sides compound with
-- unequal leaf counts. With 6 elements:
def sizebal_unequal : Term :=
  .pair (.pair e1 (.pair e2 (.pair e3 e4)))   -- 4 leaves
        (.pair e5 e6)                          -- 2 leaves

#eval verifyTree sizeBalancedConstraint sizebal_unequal  -- false (4 vs 2, diff=2)

/-! ## Constraint 2: Sorted leaves (easy)

    Left-to-right reading of leaves must be ascending.
    At each node: max(left) ≤ min(right).
    Solvable by sorting then recursively splitting. O(n log n). -/

def treeMax : Term → ℕ
  | .ground => 0
  | .pair a .ground => termToNat a
  | .pair a b => max (treeMax a) (treeMax b)
  | .observe t => treeMax t

def treeMin : Term → ℕ
  | .ground => 1000000
  | .pair a .ground => termToNat a
  | .pair a b => min (treeMin a) (treeMin b)
  | .observe t => treeMin t

def sortedLeavesConstraint : Constraint where
  check := fun a b =>
    if isNode a && isNode b then
      treeMax a ≤ treeMin b
    else if isNode a then
      treeMax a ≤ getLabel b
    else if isNode b then
      getLabel a ≤ treeMin b
    else
      getLabel a ≤ getLabel b

-- Sorted: ((1,2),(3,4))
#eval verifyTree sortedLeavesConstraint (.pair (.pair e1 e2) (.pair e3 e4))
-- true

-- Unsorted: ((3,1),(2,4))
#eval verifyTree sortedLeavesConstraint (.pair (.pair e3 e1) (.pair e2 e4))
-- false (max(left)=3 > min(right)=2 at top; also 3>1 within left)

/-! ## Constraint 3: Sum-balanced (NP-hard at level 1)

    Already defined as `balancedConstraint` in TreeArrangement.lean.
    At each level, left and right subtrees must have equal sums.
    Level 1 is the PARTITION problem (NP-complete). -/

/-! ## Density comparison: the structural complexity measure

    For each constraint, count (valid trees / total trees).
    Higher density → easier search. Lower density → harder search.

    The density directly reflects the constraint's difficulty:
    - Trivial constraint: density = 1 (everything passes)
    - Easy constraint: high density (many valid arrangements)
    - Hard constraint: low density (few valid arrangements) -/

-- 4-element trees: {1, 2, 3, 4}
#eval countValidTrees sizeBalancedConstraint [e1, e2, e3, e4]
#eval countValidTrees sortedLeavesConstraint [e1, e2, e3, e4]
#eval countValidTrees balancedConstraint [e1, e2, e3, e4]

-- Expected:
-- Size-balanced: high density (most shapes are OK when constraint rarely fires)
-- Sorted-leaves: very low density (only ascending leaf order works)
-- Sum-balanced: medium density (only sum-equal partitions work)

/-! ## Level-by-level analysis

    | Constraint     | Level 1 task          | Per-level complexity | Overall |
    |----------------|-----------------------|---------------------|---------|
    | Size-balanced  | Split ≈ equally       | O(1)                | P       |
    | Sorted-leaves  | Split sorted halves   | O(n log n)          | P       |
    | Sum-balanced   | Find equal-sum split  | NP-hard (PARTITION) | NP-hard |
    | No constraint  | Any split             | O(1)                | P       |

    The overall difficulty is the MAX difficulty across levels.
    This is the D&C principle in structural form. -/

/-! ## Three things the tree framework makes explicit

    1. THE DECOMPOSITION IS THE SEARCH OBJECT.
       In D&C, the programmer chooses the decomposition. In tree
       rotation, the decomposition IS the arrangement — the thing
       being searched for. "Designing an algorithm" and "finding a
       satisfying arrangement" become the same activity.

       This means: the question "is this problem decomposable?" has
       a LITERAL answer in the tree framework — "does a valid tree
       arrangement exist?" Decomposability is not a property we
       analyze from outside; it's a property we can search for.

    2. THE CONSTRAINT IS LEVEL-UNIFORM.
       The same constraint C fires at every tree level. It doesn't
       know what depth it's at. The difficulty at level k comes from
       the SIZE of the subproblem, not a different constraint.

       This creates a clean recursion:
         difficulty(n) = difficulty_of_split(n) + 2 × difficulty(n/2)

       If difficulty_of_split is polynomial in n, the master theorem
       gives polynomial overall. If NP-hard, the tree must be searched.

    3. THE ARRANGEMENT SPACE IS WELL-DEFINED.
       Catalan(n) × n! tree arrangements. The constraint carves a
       subset. The DENSITY of valid arrangements is a computable
       measure of difficulty. High density → easy random search.
       Low density → hard search.

       For flat lists, this is also true (n! arrangements), but
       for trees the density captures HIERARCHICAL structure that
       flat-list density misses. -/

/-! ## The honest verdict

    IS THIS JUST D&C RESTATED?

    Mostly yes. The level-by-level analysis reduces to the D&C master
    theorem. The tree framework provides notation, not new mathematics.

    BUT there is one structural feature that D&C analysis doesn't
    capture: the ROTATION RULE'S TRAVERSAL ORDER.

    When the rotation rule processes observe(pair(left, right)):
    1. It checks C(left, right) — the split constraint
    2. It carries `right` and descends into `left`
    3. Left is FULLY committed before right is examined
    4. At inner levels of left, the carried content includes right

    This means: the constraint at inner levels of the LEFT subtree
    can see the RIGHT subtree (as carried content). Information flows
    LEFT-TO-RIGHT across the tree, not simultaneously.

    In standard D&C, both subproblems are solved independently.
    In the rotation traversal, the left subproblem is solved WITH
    KNOWLEDGE of the right subproblem (via carried content).

    Whether this asymmetric information flow has complexity consequences
    is open. It's the one feature of the tree rotation framework that
    has no obvious D&C or tree-CSP equivalent. The constraint at an
    inner node of the left subtree sees a different "context" than
    the constraint at the same depth in the right subtree — because
    the right subtree is carried content during left's traversal,
    but the left subtree is NOT carried during right's traversal
    (it's already been consumed).

    This asymmetry is a consequence of the rotation rule's sequential
    nature and doesn't exist in symmetric tree decompositions. Whether
    it's useful or just an artifact remains to be determined. -/

end RotationCalculus
