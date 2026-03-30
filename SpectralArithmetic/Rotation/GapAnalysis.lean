/-
  The Gap: Measuring P vs NP in Tree Rotation
  ==============================================

  P = NP asks: does checkability imply constructibility?

  In tree terms:
  - Checkable = verifyTree is O(n) (catamorphism)
  - Constructible = factorizedConstruct is polynomial (anamorphism)
  - P = NP iff every checkable constraint is constructible

  This file doesn't resolve the question. It MEASURES the gap:
  - How does root pass rate scale with n?
  - How does construction cost scale with n?
  - Do easy and hard constraints separate measurably?

  The measurements are computable and concrete. They give
  empirical fingerprints of the P vs NP gap.
-/

import SpectralArithmetic.Rotation.Construction

namespace RotationCalculus

open Term

/-! ## Scalable element generation -/

/-- Generate elements [1, 2, ..., n] -/
def elements (n : ℕ) : List Term :=
  (List.range n).map fun i => labeledElement (i + 1)

-- Sanity check
#eval (elements 4).map getLabel   -- [1, 2, 3, 4]
#eval (elements 6).map getLabel   -- [1, 2, 3, 4, 5, 6]

/-! ## Measure 1: Total arrangement space size

    How fast does the search space grow?
    For n elements: Catalan(n) tree shapes x n! leaf placements. -/

/-- Count total tree arrangements for n elements. -/
def totalArrangements (n : ℕ) : ℕ :=
  let elems := elements n
  let ps := perms elems
  ps.foldl (fun acc perm => acc + (allTrees perm).length) 0

#eval totalArrangements 2   -- small
#eval totalArrangements 3   -- medium
#eval totalArrangements 4   -- 120

/-! ## Measure 2: Valid arrangement density

    What fraction of arrangements pass the constraint?
    High density = easy (random search works).
    Low density = hard (must search carefully). -/

/-- Count valid arrangements for a constraint on n elements. -/
def validCount (C : Constraint) (n : ℕ) : ℕ × ℕ :=
  let elems := elements n
  countValidTrees C elems

-- Density scaling for sorted constraint
#eval validCount sortedLeavesConstraint 2
#eval validCount sortedLeavesConstraint 3
#eval validCount sortedLeavesConstraint 4

-- Density scaling for balanced constraint
#eval validCount balancedConstraint 2
#eval validCount balancedConstraint 3
#eval validCount balancedConstraint 4

/-! ## Measure 3: Construction cost scaling

    The critical measure: how does construction cost grow with n?
    Polynomial growth = P. Exponential growth = NP-hard. -/

/-- Measure construction costs for increasing n. -/
def scalingData (C : Constraint) (sizes : List ℕ)
    : List (ℕ × ℕ × ℕ) :=  -- (n, brute_cost, factorized_cost)
  sizes.map fun n =>
    let elems := elements n
    let (_, bruteCost) := bruteForceConstruct C elems
    let (_, factCost) := factorizedConstruct C elems
    (n, bruteCost, factCost)

-- Sorted constraint scaling
#eval scalingData sortedLeavesConstraint [2, 3, 4]

-- Balanced constraint scaling
#eval scalingData balancedConstraint [2, 3, 4]

/-! ## Measure 4: Root pass rate as a function of n

    For each partition of n elements, what fraction of subtree
    combinations pass the root check?

    For P problems: the pass rate should stay high (many valid splits).
    For NP-hard problems: the pass rate should decay (fewer valid splits).

    This is the FINGERPRINT of the gap. -/

/-- Root pass rate for equal-size splits of n elements.
    Only tests the (n/2, n/2) split for even n.
    Returns (passing_combinations, total_combinations). -/
def equalSplitPassRate (C : Constraint) (n : ℕ) : ℕ × ℕ :=
  let elems := elements n
  if n < 4 then (0, 0)
  else
    let mid := n / 2
    let left := elems.take mid
    let right := elems.drop mid
    let leftTrees := allTrees left
    let rightTrees := allTrees right
    let pairs := leftTrees.flatMap fun lt =>
      rightTrees.map fun rt => (lt, rt)
    let passing := pairs.filter fun (lt, rt) =>
      C.check lt rt
    (passing.length, pairs.length)

-- Root pass rate scaling: sorted
#eval equalSplitPassRate sortedLeavesConstraint 4
#eval equalSplitPassRate sortedLeavesConstraint 6

-- Root pass rate scaling: balanced
#eval equalSplitPassRate balancedConstraint 4
#eval equalSplitPassRate balancedConstraint 6

/-! ## Measure 5: The heuristic gap

    The ratio between heuristic cost and brute-force cost.
    This is the "factorization speedup."

    For P problems: speedup grows exponentially (heuristic is poly,
    brute force is exp). The ratio diverges.

    For NP-hard problems: no polynomial heuristic exists, so the
    speedup is bounded (both are exponential, just different constants). -/

/-- Heuristic cost for sorted constraint (sort then split). -/
def sortedHeuristicCost (n : ℕ) : ℕ :=
  let elems := elements n
  -- Reverse to make it unsorted
  let shuffled := elems.reverse
  (sortedConstruct shuffled).2

#eval (sortedHeuristicCost 2, sortedHeuristicCost 3,
       sortedHeuristicCost 4, sortedHeuristicCost 6,
       sortedHeuristicCost 8)
-- Should grow as O(n log n): roughly 1, 2, 3, 5, 7

/-! ## The composite picture

    Collect all measures for easy visual comparison. -/

/-- All measures for a given constraint and size. -/
structure GapMeasurement where
  n : ℕ
  totalSpace : ℕ
  validCount : ℕ
  density : String  -- valid/total as string
  bruteCost : ℕ
  factCost : ℕ
  deriving Repr

def measure (C : Constraint) (n : ℕ) : GapMeasurement :=
  let elems := elements n
  let total := totalArrangements n
  let (valid, _) := RotationCalculus.validCount C n
  let (_, brute) := bruteForceConstruct C elems
  let (_, fact) := factorizedConstruct C elems
  { n, totalSpace := total, validCount := valid,
    density := s!"{valid}/{total}",
    bruteCost := brute, factCost := fact }

-- Full measurement: sorted constraint
#eval measure sortedLeavesConstraint 3
#eval measure sortedLeavesConstraint 4

-- Full measurement: balanced constraint
#eval measure balancedConstraint 3
#eval measure balancedConstraint 4

/-! ## What the measurements tell us

    The gap between P and NP, in this framework, is the gap between:
    1. DENSITY of valid arrangements (how many solutions exist)
    2. FINDABILITY of valid arrangements (how cheaply can you find one)
    3. FACTORIZABILITY of the constraint (does the tree decompose?)

    For P problems (sorted):
    - Density is low (few valid arrangements out of n!)
    - But findability is high (sort-then-split finds one in O(n log n))
    - The constraint factorizes perfectly

    For NP-hard problems (balanced partition):
    - Density varies (depends on the specific numbers)
    - Findability is low (no known polynomial heuristic)
    - The constraint doesn't factorize (finding the split IS the problem)

    The key insight: DENSITY DOES NOT DETERMINE FINDABILITY.
    Sorted has very low density (1/n! for the unique sorted arrangement)
    but very high findability (sort and split). Balanced partition can
    have moderate density but low findability.

    What determines findability is STRUCTURE — whether the valid
    arrangements are connected to each other in the arrangement space
    in a way that a polynomial algorithm can navigate. The tree
    framework makes this structure visible as factorizability:
    can you decompose the search into independent subtree searches?

    P = NP would mean: checkability always implies factorizability.
    P != NP would mean: some checkable constraints resist factorization.

    The framework can't prove which is true. But it can MEASURE the
    factorizability of specific constraints on specific instances,
    giving empirical evidence about the structure of the gap. The
    root pass rate, construction cost ratio, and factorization
    density are the computable fingerprints. -/

end RotationCalculus
