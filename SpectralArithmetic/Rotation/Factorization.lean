/-
  Tree Rotation: Constraint Factorization
  =========================================

  The central thesis: the complexity of a constrained tree arrangement
  problem is determined by whether the constraint FACTORIZES over the
  tree structure.

  Factorization means: solving the left subtree and right subtree
  can be done independently. The partition of elements determines
  which subproblems exist, but within each subproblem, the solution
  doesn't depend on the sibling subtree.

  When the constraint factorizes: divide-and-conquer works.
  When it doesn't: brute force over Catalan(n) × n!.

  This file formalizes:
  1. Subtree independence (constraint is local to children)
  2. Search factorization (valid subtrees compose into valid trees)
  3. The gap: constraint independence ≠ search independence
  4. Examples showing factorizable vs non-factorizable constraints
  5. Connection to treewidth (informal)
-/

import SpectralArithmetic.Rotation.TreeFlow
import SpectralArithmetic.Rotation.TreeComplexity

namespace RotationCalculus

open Term

/-! ## Subtree independence

    A constraint is subtree-independent if the check at each node
    depends ONLY on the two children, not on any wider context.

    This is the symmetric verification model (verifyTree).
    It's the condition under which the constraint is "local." -/

/-- A constraint is subtree-independent: its verdict at a node
    depends only on the immediate children, not on context.
    Equivalently: verifyTree and verifyTreeCtx agree for all trees. -/
def Constraint.subtreeIndependent (C : Constraint) : Prop :=
  ∀ (t : Term) (ctx : Term),
    verifyTree C t = verifyTreeCtx C t ctx

/-! The balanced partition constraint IS subtree-independent:
    it checks treeSum(left) == treeSum(right) without using context.
    The budget constraint is NOT subtree-independent:
    it uses context to determine the "visible total." -/

-- balancedConstraint: verifyTree and verifyTreeCtx agree (no context used)
#eval
  let trees := allTrees [e1, e2, e3, e4]
  let agree := trees.filter fun t =>
    verifyTree balancedConstraint t == verifyTreeCtx balancedConstraint t .ground
  (agree.length, trees.length)
-- Should be (n, n) — all agree

-- budgetConstraint: they disagree (context matters)
#eval
  let ps := perms [e1, e2, e3, e4]
  let trees := ps.flatMap fun p => allTrees p
  let disagree := trees.filter fun t =>
    verifyTree budgetConstraint t != verifyTreeCtx budgetConstraint t .ground
  disagree.length
-- Should be > 0

/-! ## Search factorization

    Even when the constraint is subtree-independent, the SEARCH may
    not factorize. Factorization requires that the valid leaf
    placements for the left subtree don't depend on which elements
    are in the right subtree (beyond the initial partition).

    Two levels of independence:
    - Constraint independence: each check is local (verifyTree works)
    - Search independence: valid subtrees compose into valid trees

    Constraint independence is NECESSARY but not SUFFICIENT for
    search independence. -/

/-- A constraint factorizes on a given partition if: whenever both
    halves independently have valid tree arrangements, combining them
    at the root also produces a valid tree.

    This is the compositional property: local solutions compose
    into global solutions. -/
def factorizesOnPartition (C : Constraint)
    (left right : List Term) : Prop :=
  ∀ (lt rt : Term),
    verifyTree C lt = true →
    verifyTree C rt = true →
    C.check lt rt = true →
    verifyTree C (.pair lt rt) = true

/-- A constraint fully factorizes if for EVERY partition of the
    elements into two non-empty groups, valid subtrees compose. -/
def Constraint.factorizes (C : Constraint) (elements : List Term) : Prop :=
  ∀ (left right : List Term),
    left ++ right = elements →
    left ≠ [] → right ≠ [] →
    factorizesOnPartition C left right

/-! ## Test: does balancedConstraint factorize?

    Claim: YES for verification composability. If both subtrees are
    internally valid AND the root check passes (sums equal), then
    the whole tree is valid.

    This is because verifyTree checks root, then independently
    checks both children. So:
      verifyTree C (pair lt rt)
      = C.check lt rt && verifyTree C lt && verifyTree C rt

    If all three are true, the conjunction is true. -/

/-- verifyTree on a pair where b is not ground decomposes into
    root check AND both subtree checks. -/
theorem verifyTree_pair (C : Constraint) (a b1 b2 : Term) :
    verifyTree C (.pair a (.pair b1 b2)) =
    (if C.check a (.pair b1 b2) then
      verifyTree C a && verifyTree C (.pair b1 b2)
    else false) := by
  simp [verifyTree]

/-! ## The factorization gap: sorting vs partition

    SORTING factorizes:
    - Constraint: max(left) ≤ min(right) (sorted leaves)
    - Partition any way: sort left, sort right, check root
    - Left's valid arrangement doesn't depend on right's elements
    - You can merge independently sorted halves

    BALANCED PARTITION does NOT factorize as search:
    - Constraint: treeSum(left) == treeSum(right)
    - The ROOT CHECK depends on WHICH elements are in each half
    - You can't decide the partition without knowing all elements
    - The partition IS the hard part

    Both constraints are subtree-independent (local checks).
    But sorting allows independent subproblem solving while
    balanced partition couples the subproblems through the partition. -/

/-- Count how many partitions of elements into two halves allow
    BOTH halves to have at least one valid tree arrangement. -/
def countFactorizablePartitions (C : Constraint)
    (elements : List Term) : ℕ × ℕ :=
  let n := elements.length
  let partitions := List.range (n - 1) |>.map fun i =>
    (elements.take (i + 1), elements.drop (i + 1))
  let factorizable := partitions.filter fun (left, right) =>
    let leftValid := (allTrees left).any fun t => verifyTree C t
    let rightValid := (allTrees right).any fun t => verifyTree C t
    leftValid && rightValid
  (factorizable.length, partitions.length)

-- For sorted leaves: most partitions of a sorted list factorize
#eval countFactorizablePartitions sortedLeavesConstraint
  [e1, e2, e3, e4, e5, e6]

-- For balanced partition: fewer partitions factorize (need equal sums)
#eval countFactorizablePartitions balancedConstraint
  [e1, e2, e3, e4, e5, e6]

/-! ## The coupling measure

    Define the "coupling" of a constraint as: the fraction of
    partitions where the root check DEPENDS on the specific
    elements in each half (not just their count or local properties).

    High coupling → hard search (partition matters)
    Low coupling → easy search (any partition works)

    This is an empirical proxy for treewidth: high coupling means
    the constraint graph has high treewidth (many cross-partition
    edges), preventing independent subproblem solving. -/

/-- For each partition, check what fraction of leaf placements
    pass the root constraint. Low fraction = high coupling. -/
def rootPassRate (C : Constraint) (elements : List Term) : List (ℕ × ℕ) :=
  let n := elements.length
  List.range (n - 1) |>.map fun i =>
    let left := elements.take (i + 1)
    let right := elements.drop (i + 1)
    let leftTrees := allTrees left
    let rightTrees := allTrees right
    let pairs := leftTrees.flatMap fun lt =>
      rightTrees.map fun rt => (lt, rt)
    let passing := pairs.filter fun (lt, rt) => C.check lt rt
    (passing.length, pairs.length)

-- Sorted constraint: root pass rate for [1,2,3,4]
#eval rootPassRate sortedLeavesConstraint [e1, e2, e3, e4]

-- Balanced constraint: root pass rate for [1,2,3,4]
#eval rootPassRate balancedConstraint [e1, e2, e3, e4]

/-! ## Connection to treewidth (informal)

    The factorization analysis above is a computational version of
    treewidth for the specific constraint families we're studying.

    TREEWIDTH (standard definition):
    Given a constraint graph G, the treewidth tw(G) is the minimum
    width of a tree decomposition of G. Problems on graphs with
    tw(G) ≤ k can be solved in time O(n · d^(k+1)) where d is the
    domain size.

    FACTORIZATION (our definition):
    Given a constraint C and elements E, the "factorizability" is
    the degree to which valid subtree arrangements compose into
    valid whole-tree arrangements. High factorizability ≈ low treewidth.

    The correspondence is not exact:
    - Treewidth applies to FIXED constraint graphs
    - Factorizability applies to SEARCHABLE tree shapes
    - Treewidth is a property of the constraint structure
    - Factorizability is a property of (constraint × elements)

    But the underlying principle is the same: can the problem be
    decomposed into independent subproblems? Treewidth measures
    this for fixed decompositions. Factorizability measures it for
    the best possible decomposition.

    WHAT'S NEW IN THE ROTATION FRAMEWORK:
    The tree shape is part of the search space, not given in advance.
    You're searching for a decomposition that factorizes. This is
    closer to the algorithm-design problem ("find a good divide-and-
    conquer strategy") than to the constraint-satisfaction problem
    ("solve this CSP with a fixed constraint graph").

    And the asymmetric flow (TreeFlow.lean) adds a dimension that
    treewidth doesn't capture: the traversal order matters. The
    rotation rule's left-first descent means information flows
    differently through the tree depending on which subtree is
    processed first. This creates 18 disagreements on 4 elements
    between symmetric and asymmetric verification — a concrete
    structural difference from standard tree decomposition. -/

end RotationCalculus
