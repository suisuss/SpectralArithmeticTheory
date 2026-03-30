/-
  Rotation Calculus: Tree Arrangements
  =====================================

  Every example so far uses flat lists (permutation space = n!).
  But `pair` builds trees, and the rotation rule descends into nested
  structure. The constraint fires at EVERY nesting level — between
  grouped substructures, not just between atomic elements.

  Key finding: tree arrangements add a genuinely new dimension to the
  search space. The tree SHAPE determines which constraint checks fire.
  A constraint that is vacuous on flat lists becomes substantive on trees.
  This is structurally different from flat-list permutation CSP.

  Data representation:
  - Leaf (labeled element): pair (natToTerm n) ground  [via labeledElement]
  - Tree node: pair leftSubtree rightSubtree
  - NOT the list encoding (pair elem (pair elem ... ground))
-/

import SpectralArithmetic.Rotation.Examples

namespace RotationCalculus

open Term

/-! ## Tree structure utilities -/

/-- Sum all labels in a term tree.
    - Leaf = pair (natToTerm n) ground → value n
    - Node = pair subtree subtree → sum of both subtrees
    - ground → 0 -/
def treeSum : Term → ℕ
  | .ground => 0
  | .pair a .ground => termToNat a        -- leaf: extract label
  | .pair a b => treeSum a + treeSum b    -- node: sum both branches
  | .observe t => treeSum t

/-- Is a term a tree node (both children are subtrees, not a leaf)?
    Leaf = pair _ ground. Node = pair _ (pair _ _). -/
def isNode : Term → Bool
  | .pair _ (.pair _ _) => true
  | _ => false

/-- Count leaf elements in a tree. -/
def leafCount : Term → ℕ
  | .ground => 0
  | .pair _ .ground => 1                        -- leaf
  | .pair a b => leafCount a + leafCount b      -- node
  | .observe t => leafCount t

/-- Collect all leaf labels from a tree. -/
def leafLabels : Term → List ℕ
  | .ground => []
  | .pair a .ground => [termToNat a]            -- leaf
  | .pair a b => leafLabels a ++ leafLabels b   -- node
  | .observe t => leafLabels t

/-! ## Leaf elements -/

def e1 := labeledElement 1
def e2 := labeledElement 2
def e3 := labeledElement 3
def e4 := labeledElement 4
def e5 := labeledElement 5
def e6 := labeledElement 6
def e7 := labeledElement 7
def e8 := labeledElement 8

-- Verify: leaf sums
#eval treeSum e2   -- 2
#eval treeSum e8   -- 8

-- Verify: tree node sums
#eval treeSum (.pair e2 e8)   -- 10
#eval treeSum (.pair e3 e7)   -- 10
#eval treeSum (.pair (.pair e2 e8) (.pair e3 e7))   -- 20

-- Verify: isNode
#eval isNode e2                              -- false (leaf)
#eval isNode (.pair e2 e8)                   -- true (node)
#eval isNode (.pair (.pair e2 e8) (.pair e3 e7))  -- true (node)

/-! ## Balanced partition constraint

    At each tree level, the constraint fires on (leftChild, rightChild).

    - When BOTH children are nodes (compound subtrees): check that
      their sums are equal. This is the partition balance condition.
    - Otherwise (at least one child is a leaf): pass freely.

    This constraint is TREE-SENSITIVE: a flat list never has two
    compound children at the outermost level, so the balance check
    never fires. On trees, it fires at every level where both
    branches are themselves subtrees. -/

def balancedConstraint : Constraint where
  check := fun a b =>
    if isNode a && isNode b then
      treeSum a == treeSum b
    else
      true

/-! ## Example: Partition {2, 3, 7, 8}

    Total = 20. Target: two groups summing to 10 each.
    Valid: {2, 8} | {3, 7}  (10 vs 10)
    Invalid: {2, 3} | {7, 8}  (5 vs 15)
    Invalid: {2, 7} | {3, 8}  (9 vs 11) -/

/-! ### Tree arrangements (pair subtree subtree, leaves are labeledElement) -/

/-- {2, 8} | {3, 7}: sums 10 vs 10. Balanced. -/
def tree_bal := Term.pair (.pair e2 e8) (.pair e3 e7)

/-- {2, 3} | {7, 8}: sums 5 vs 15. Unbalanced. -/
def tree_unbal1 := Term.pair (.pair e2 e3) (.pair e7 e8)

/-- {2, 7} | {3, 8}: sums 9 vs 11. Unbalanced. -/
def tree_unbal2 := Term.pair (.pair e2 e7) (.pair e3 e8)

/-- {3, 8} | {2, 7}: sums 11 vs 9. Unbalanced. -/
def tree_unbal3 := Term.pair (.pair e3 e8) (.pair e2 e7)

-- Verify sums
#eval (treeSum (.pair e2 e8), treeSum (.pair e3 e7))  -- (10, 10)
#eval (treeSum (.pair e2 e3), treeSum (.pair e7 e8))  -- (5, 15)
#eval (treeSum (.pair e2 e7), treeSum (.pair e3 e8))  -- (9, 11)

-- Verify constraint checks at top level
#eval balancedConstraint.check (.pair e2 e8) (.pair e3 e7)  -- true  (10==10)
#eval balancedConstraint.check (.pair e2 e3) (.pair e7 e8)  -- false (5!=15)
#eval balancedConstraint.check (.pair e2 e7) (.pair e3 e8)  -- false (9!=11)

/-! ### Tree-level verifier

    The existing `verifyList`/`verifyArrangement` assumes flat lists.
    For trees, we need a verifier that descends into the hierarchical
    structure, checking the constraint at every internal node. -/

/-- Verify a tree arrangement: check constraint at each internal node,
    then recursively verify both subtrees. -/
def verifyTree (C : Constraint) : Term → Bool
  | .ground => true
  | .pair _ .ground => true                    -- leaf: nothing to check
  | .pair a b =>
    if C.check a b then
      verifyTree C a && verifyTree C b        -- pass: verify subtrees
    else
      false                                   -- fail: constraint violated
  | .observe t => verifyTree C t

-- Full tree verification
#eval verifyTree balancedConstraint tree_bal     -- true  (balanced)
#eval verifyTree balancedConstraint tree_unbal1  -- false (5 vs 15)
#eval verifyTree balancedConstraint tree_unbal2  -- false (9 vs 11)
#eval verifyTree balancedConstraint tree_unbal3  -- false (11 vs 9)

/-! ### Flat lists are vacuously balanced -/

-- A flat list: pair e2 (pair e3 (pair e7 (pair e8 ground)))
-- At each step: C(leaf, rest). The leaf isNode = false.
-- So the balance check never fires. Everything passes.

def flat1 := fromList [e2, e3, e7, e8]
def flat2 := fromList [e8, e7, e3, e2]
def flat3 := fromList [e2, e8, e3, e7]

#eval verifyTree balancedConstraint flat1  -- true (vacuous)
#eval verifyTree balancedConstraint flat2  -- true (vacuous)
#eval verifyTree balancedConstraint flat3  -- true (vacuous)

/-! STRUCTURAL DIFFERENCE DEMONSTRATED:

    Same elements {2, 3, 7, 8}. Same constraint.

    Flat lists: ALL arrangements pass (constraint is vacuous).
    Trees: ONLY balanced groupings pass (constraint is substantive).

    The tree SHAPE is where the computational content lives.
    Flat-list permutation CSP cannot express this problem. -/

/-! ## Brute-force tree search -/

/-- Generate all binary tree shapes over a list of leaves.
    Each leaf becomes a `labeledElement`. Internal nodes are pairs. -/
partial def allTrees : List Term → List Term
  | [] => [.ground]
  | [x] => [x]  -- single leaf
  | xs =>
    -- Split the list into every possible (non-empty left, non-empty right)
    let n := xs.length
    List.range (n - 1) |>.flatMap fun i =>
      let left := xs.take (i + 1)
      let right := xs.drop (i + 1)
      let leftTrees := allTrees left
      let rightTrees := allTrees right
      leftTrees.flatMap fun lt =>
        rightTrees.map fun rt => .pair lt rt

/-- Search all tree arrangements (all permutations × all tree shapes). -/
def treeSearch (C : Constraint) (elements : List Term)
    : Option (List ℕ × Term) :=
  let ps := perms elements
  let results := ps.flatMap fun perm =>
    (allTrees perm).filterMap fun tree =>
      if verifyTree C tree then
        some (leafLabels tree, tree)
      else
        none
  results.head?

/-- Count valid vs total tree arrangements. -/
def countValidTrees (C : Constraint) (elements : List Term) : ℕ × ℕ :=
  let ps := perms elements
  let all := ps.flatMap fun perm => allTrees perm
  let valid := all.filter fun tree => verifyTree C tree
  (valid.length, all.length)

-- Search for balanced partition of {2, 3, 7, 8}
#eval (treeSearch balancedConstraint [e2, e3, e7, e8]).map (·.1)
-- Should find [2, 8, 3, 7] or [3, 7, 2, 8] etc.

-- How many valid tree arrangements?
#eval countValidTrees balancedConstraint [e2, e3, e7, e8]
-- (valid, total) — valid should be small fraction

/-! ## Deeper trees: multi-level balance

    For 8 elements, the constraint can fire at MULTIPLE levels.
    A perfectly balanced tree has balance checks at every internal node.

    {1, 2, 3, 4, 5, 6, 7, 8}: total = 36.
    Top level: two subtrees of sum 18 each.
    Second level: four subtrees of sum 9 each.

    Finding a multi-level balanced tree is harder than a single split. -/

/-- A perfectly balanced tree: ((1,8),(5,4)) | ((2,7),(3,6))
    Level 1: left=18, right=18
    Level 2: (1+8)=9, (5+4)=9, (2+7)=9, (3+6)=9 -/
def deepBalanced : Term :=
  .pair (.pair (.pair e1 e8) (.pair e5 e4))
        (.pair (.pair e2 e7) (.pair e3 e6))

/-- An unbalanced deep tree: ((1,2),(3,4)) | ((5,6),(7,8))
    Level 1: left=10, right=26
    Already fails at top level. -/
def deepUnbalanced : Term :=
  .pair (.pair (.pair e1 e2) (.pair e3 e4))
        (.pair (.pair e5 e6) (.pair e7 e8))

#eval verifyTree balancedConstraint deepBalanced    -- true
#eval verifyTree balancedConstraint deepUnbalanced  -- false

-- Verify the sums at each level
#eval (treeSum (.pair (.pair e1 e8) (.pair e5 e4)),
       treeSum (.pair (.pair e2 e7) (.pair e3 e6)))  -- (18, 18)
#eval (treeSum (.pair e1 e8), treeSum (.pair e5 e4))  -- (9, 9)
#eval (treeSum (.pair e2 e7), treeSum (.pair e3 e6))  -- (9, 9)

/-! ## Assessment

    WHAT'S GENUINELY NEW:

    1. The arrangement space includes TREE SHAPE as a searchable
       dimension. Flat-list CSP searches over permutations (n!).
       Tree rotation searches over (tree shapes × leaf placements),
       which is Catalan(n) × n! — strictly larger.

    2. The SAME rewrite rule (observe(pair(a,b)) → pair(b,observe(a)))
       gains new power on trees. On flat lists, `a` is always atomic.
       On trees, `a` can be a compound subtree, and the constraint
       sees it as a structured object. The rule is unchanged; the
       expressiveness comes from the data.

    3. Constraints that are VACUOUS on flat lists become SUBSTANTIVE
       on trees. The balanced partition constraint demonstrates this:
       every flat arrangement passes, but only specific tree groupings
       pass. The tree structure IS the computational content.

    4. Multi-level constraints (like the deep balanced tree example)
       create HIERARCHICAL search problems where the constraint fires
       at every level of the tree. This is a search over hierarchical
       decompositions — not expressible in flat-list CSP at all.

    WHAT THIS MEANS:

    The CSP equivalence finding (CSPEquivalence.lean) showed that
    flat-list rotation = permutation CSP. Tree arrangements ESCAPE
    this equivalence. The search space is different (Catalan × n!
    vs n!), the constraint semantics are different (compound vs atomic
    elements), and the problems expressible are different (hierarchical
    decomposition vs sequential ordering).

    Whether this is "tree-CSP in costume" or something genuinely novel
    depends on whether the specific structure of the rotation rule —
    its descent into compound elements, its deterministic traversal
    order, its reversibility — gives proof-theoretic leverage that
    generic tree decomposition frameworks don't.

    The next test: can we prove a structural theorem about tree
    arrangement search that uses rotation-specific properties and
    has no tree-CSP equivalent? -/

end RotationCalculus
