/-
  Tree Rotation: Checking vs Constructing
  =========================================

  Checking is a catamorphism: fold the tree, check each node. O(n).
  Constructing is either:
  - Factorized: build top-down with local choices. O(n log n).
  - Brute-force: search all trees, verify each. Catalan(n) x n!.

  This file implements both construction strategies, measures their
  cost, and shows the factorization speedup directly.
-/

import SpectralArithmetic.Rotation.Factorization

namespace RotationCalculus

open Term

/-! ## Cost-instrumented verification

    Count the number of constraint checks during verification.
    This is the concrete cost of CHECKING. -/

/-- Verify a tree, counting constraint checks performed. -/
def verifyTreeCounting (C : Constraint) : Term → (Bool × ℕ)
  | .ground => (true, 0)
  | .pair _ .ground => (true, 0)
  | .pair a b =>
    let passed := C.check a b
    if passed then
      let (lOk, lCost) := verifyTreeCounting C a
      let (rOk, rCost) := verifyTreeCounting C b
      (lOk && rOk, 1 + lCost + rCost)
    else
      (false, 1)
  | .observe t => verifyTreeCounting C t

-- Checking cost: 4-element balanced tree
#eval verifyTreeCounting balancedConstraint
  (.pair (.pair e2 e8) (.pair e3 e7))
-- (true, 1) — one root check

-- Checking cost: 8-element deep tree
#eval verifyTreeCounting balancedConstraint deepBalanced
-- (true, N) — root + second-level checks

-- Failed check: stops early
#eval verifyTreeCounting balancedConstraint deepUnbalanced
-- (false, 1) — fails at root

/-! ## Brute-force construction (exponential)

    Try every tree arrangement. Count trees examined. -/

/-- Brute-force: try all permutations x all tree shapes.
    Returns (solution, trees_examined). -/
def bruteForceConstruct (C : Constraint) (elements : List Term)
    : Option Term × ℕ :=
  let ps := perms elements
  let allArrangements := ps.flatMap fun perm => allTrees perm
  let rec go : List Term → ℕ → Option Term × ℕ
    | [], n => (none, n)
    | t :: rest, n =>
      if verifyTree C t then (some t, n + 1)
      else go rest (n + 1)
  go allArrangements 0

/-! ## Factorized construction (polynomial when splits are easy)

    Build top-down: at each level, try splits until one works.
    Recurse into subtrees independently. -/

/-- Try all ways to split a list into two non-empty parts. -/
def allSplitsOf (xs : List α) : List (List α × List α) :=
  let n := xs.length
  if n ≤ 1 then []
  else List.range (n - 1) |>.map fun i =>
    (xs.take (i + 1), xs.drop (i + 1))

/-- Factorized construction: try splits, recurse independently.
    Returns (solution, operations_count). -/
partial def factorizedConstruct (C : Constraint) (elements : List Term)
    : Option Term × ℕ :=
  match elements with
  | [] => (some .ground, 0)
  | [x] => (some x, 0)
  | [x, y] =>
    let t1 := Term.pair x y
    if verifyTree C t1 then (some t1, 1)
    else
      let t2 := Term.pair y x
      if verifyTree C t2 then (some t2, 2)
      else (none, 2)
  | xs =>
    let splits := allSplitsOf xs
    let rec trySplits : List (List Term × List Term) → ℕ
        → Option Term × ℕ
      | [], cost => (none, cost)
      | (left, right) :: rest, cost =>
        let (leftTree, lc) := factorizedConstruct C left
        let (rightTree, rc) := factorizedConstruct C right
        let cost' := cost + lc + rc
        match leftTree, rightTree with
        | some lt, some rt =>
          -- Try both orientations
          if C.check lt rt && verifyTree C (.pair lt rt) then
            (some (.pair lt rt), cost' + 1)
          else if C.check rt lt && verifyTree C (.pair rt lt) then
            (some (.pair rt lt), cost' + 2)
          else trySplits rest (cost' + 2)
        | _, _ => trySplits rest cost'
    trySplits splits 0

/-! ## Heuristic construction for sorted constraint

    Sort then split recursively. Always succeeds. O(n log n).
    Uses fuel for termination proof. -/

def sortedBuild : List Term → ℕ → Term × ℕ
  | [], _ => (.ground, 0)
  | [x], _ => (x, 0)
  | _, 0 => (.ground, 0)
  | xs, fuel + 1 =>
    let mid := xs.length / 2
    let (lt, lc) := sortedBuild (xs.take mid) fuel
    let (rt, rc) := sortedBuild (xs.drop mid) fuel
    (.pair lt rt, 1 + lc + rc)

def sortedConstruct (elements : List Term) : Term × ℕ :=
  let sorted := elements.toArray.insertionSort
    (fun a b => getLabel a < getLabel b) |>.toList
  sortedBuild sorted sorted.length

/-! ## Head-to-head comparison -/

-- === SORTED CONSTRAINT: 4 elements ===

#eval
  let (result, cost) := bruteForceConstruct sortedLeavesConstraint
    [e4, e2, e1, e3]
  (result.map leafLabels, s!"brute: examined {cost} trees")

#eval
  let (result, cost) := factorizedConstruct sortedLeavesConstraint
    [e4, e2, e1, e3]
  (result.map leafLabels, s!"factorized: cost {cost}")

#eval
  let (result, cost) := sortedConstruct [e4, e2, e1, e3]
  (leafLabels result, s!"heuristic: cost {cost}")

-- === BALANCED CONSTRAINT: 4 elements ===

#eval
  let (result, cost) := bruteForceConstruct balancedConstraint
    [e2, e3, e7, e8]
  (result.map leafLabels, s!"brute: examined {cost} trees")

#eval
  let (result, cost) := factorizedConstruct balancedConstraint
    [e2, e3, e7, e8]
  (result.map leafLabels, s!"factorized: cost {cost}")

-- === SCALING: 6 elements, sorted ===

#eval
  let (result, cost) := bruteForceConstruct sortedLeavesConstraint
    [e3, e1, e5, e2, e6, e4]
  (result.map leafLabels, s!"brute-6: examined {cost} trees")

#eval
  let (result, cost) := factorizedConstruct sortedLeavesConstraint
    [e3, e1, e5, e2, e6, e4]
  (result.map leafLabels, s!"factorized-6: cost {cost}")

#eval
  let (result, cost) := sortedConstruct [e3, e1, e5, e2, e6, e4]
  (leafLabels result, s!"heuristic-6: cost {cost}")

-- === SCALING: 6 elements, balanced ===
-- Use even total: {1, 3, 4, 6, 7, 9} total = 30, target = 15 per side

def e9 := labeledElement 9

#eval
  let (result, cost) := bruteForceConstruct balancedConstraint
    [e1, e3, e4, e6, e7, e9]
  (result.map leafLabels, s!"brute-6-bal: examined {cost} trees")

#eval
  let (result, cost) := factorizedConstruct balancedConstraint
    [e1, e3, e4, e6, e7, e9]
  (result.map leafLabels, s!"factorized-6-bal: cost {cost}")

-- === HARD TEST: 8 elements, balanced ===
-- {1, 2, 3, 4, 5, 6, 7, 8} total = 36, target = 18 per side

#eval
  let (result, cost) := bruteForceConstruct balancedConstraint
    [e5, e3, e8, e1, e6, e2, e7, e4]
  (result.map leafLabels, s!"brute-8-bal: examined {cost} trees")

#eval
  let (result, cost) := factorizedConstruct balancedConstraint
    [e5, e3, e8, e1, e6, e2, e7, e4]
  (result.map leafLabels, s!"factorized-8-bal: cost {cost}")

-- === HARD TEST: 8 elements, sorted ===

#eval
  let (result, cost) := bruteForceConstruct sortedLeavesConstraint
    [e5, e3, e8, e1, e6, e2, e7, e4]
  (result.map leafLabels, s!"brute-8-sort: examined {cost} trees")

#eval
  let (result, cost) := factorizedConstruct sortedLeavesConstraint
    [e5, e3, e8, e1, e6, e2, e7, e4]
  (result.map leafLabels, s!"factorized-8-sort: cost {cost}")

#eval
  let (result, cost) := sortedConstruct [e5, e3, e8, e1, e6, e2, e7, e4]
  (leafLabels result, s!"heuristic-8-sort: cost {cost}")

/-! ## What the scaling reveals

    The factorized constructor has two regimes:

    WITH domain knowledge (heuristic split strategy):
    - Cost scales as O(n log n): 3 → 5 → 7 for 4 → 6 → 8 elements
    - This is genuine polynomial complexity reduction
    - The heuristic IS the algorithm (sort first, then split)

    WITHOUT domain knowledge (try all contiguous splits):
    - Cost scales roughly exponentially in the worst case
    - Each split requires recursive construction of both halves
    - Bad splits waste work that can't be recovered

    The HEURISTIC is what makes factorization polynomial. The tree
    structure enables factorization, but the split strategy exploits it.
    For NP-hard constraints (balanced partition), no polynomial split
    strategy is known — finding the right split IS the hard problem.

    This is the sharpest version of the finding:
    - The tree makes decomposition POSSIBLE (structural)
    - The heuristic makes decomposition EFFICIENT (algorithmic)
    - For P problems: efficient heuristics exist
    - For NP-hard problems: no efficient heuristic exists (assuming P != NP)
    - The gap between "possible" and "efficient" IS the P vs NP gap -/

/-! ## The structural summary

    CHECKING is a catamorphism:
      check(pair(l, r)) = C(l, r) && check(l) && check(r)
      check(leaf) = true

    One pass, no backtracking. The tree determines the computation.

    CONSTRUCTING (factorized) is an anamorphism:
      construct(elems) = pair(construct(left), construct(right))
        where (left, right) = split(elems)

    An unfold that builds the tree top-down. Each level makes one
    choice (the split). Choices compose independently.

    CONSTRUCTING (brute force) is a search:
      construct(elems) = find t in allTrees(elems) such that check(t)

    Enumeration of the arrangement space filtered by check.

    The speedup ratio between factorized and brute-force construction
    is the computable measure of how well the constraint factorizes.

    P  = checkable AND factorizable (anamorphism works)
    NP = checkable (catamorphism works)
    The gap = does checkability imply factorizability? -/

end RotationCalculus
