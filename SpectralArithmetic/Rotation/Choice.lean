/-
  Choice Constructor: AND-OR Trees and Alternating Computation
  ==============================================================

  `pair` is AND: both children are present, both must pass.
  `choice` is OR: one branch is selected, at least one must pass.

  Together they give AND-OR trees — the game tree / proof tree
  structure underlying alternating computation and the polynomial
  hierarchy.

  Key complexity-theoretic significance:
  - pair only (current): NP (existential search over arrangements)
  - pair + existential choice: still NP (choice picks the best branch)
  - pair + universal choice: coNP (all branches must work)
  - alternating pair + choice: PH (polynomial hierarchy levels)
  - unbounded alternation: PSPACE

  The choice constructor doesn't change the rotation rule.
  It changes what VERIFICATION means: instead of "all checks pass"
  (conjunction), some nodes require "at least one branch passes"
  (disjunction).
-/

import SpectralArithmetic.Rotation.SATEncoding

namespace RotationCalculus

open Term

/-! ## AND-OR Term representation

    Extend the term type conceptually with an OR node.
    Implementation: use a special label to mark OR-nodes within
    the existing Term type, avoiding modification of the inductive.

    OR-node: pair(marker, pair(branch_a, branch_b))
    where marker = labeledElement 9999 (sentinel) -/

/-- The OR-node marker. -/
def orMarker : Term := labeledElement 9999

/-- Build an OR node: the verifier succeeds if EITHER branch succeeds. -/
def choice (a b : Term) : Term := .pair orMarker (.pair a b)

/-- Check if a term is an OR node. -/
def isChoice (t : Term) : Bool :=
  match t with
  | .pair marker _ => getLabel marker == 9999
  | _ => false

/-- Extract the two branches of an OR node. -/
def choiceBranches (t : Term) : Option (Term × Term) :=
  match t with
  | .pair _ (.pair a b) => if isChoice t then some (a, b) else none
  | _ => none

/-! ## AND-OR verification

    The standard verifyTree treats every node as AND:
    both subtrees must pass. The AND-OR verifier distinguishes:

    - AND nodes (pair): both children must pass
    - OR nodes (choice): at least one child must pass

    This is alpha-beta style evaluation. -/

/-- Verify an AND-OR tree.
    AND nodes: both children must pass.
    OR nodes: at least one child must pass. -/
def verifyAO (C : Constraint) : Term → Bool
  | .ground => true
  | .pair _ .ground => true    -- leaf
  | t =>
    if isChoice t then
      -- OR node: at least one branch must pass
      match t with
      | .pair _ (.pair a b) => verifyAO C a || verifyAO C b
      | _ => false
    else
      -- AND node: constraint check + both subtrees
      match t with
      | .pair a b =>
        if C.check a b then verifyAO C a && verifyAO C b
        else false
      | _ => true

/-! ## Example: SAT with OR-branching

    A SAT formula with a choice node represents: "try this assignment
    OR that assignment." The verifier succeeds if ANY branch leads to
    satisfaction.

    This encodes existential quantification directly in the tree.

    Instance: (x0 OR x1) AND (NOT x0 OR x1)
    Solution: x0=anything, x1=true. Or specifically: x1 must be true.

    AND-OR tree:
      choice(
        pair(x0=T, x1=T),    -- branch 1: both true
        pair(x0=F, x1=T)     -- branch 2: x0 false, x1 true
      )

    Both branches satisfy the formula. The choice says "pick either." -/

def choiceFormula : SATFormula :=
  [ [(0, true), (1, true)],      -- x0 OR x1
    [(0, false), (1, true)] ]    -- NOT x0 OR x1

-- Manual AND-OR tree: choose between two satisfying assignments
def aoTree1 : Term :=
  choice
    (.pair (literal 0 true) (literal 1 true))
    (.pair (literal 0 false) (literal 1 true))

-- Verify: should succeed (both branches work for this formula)
#eval verifyAO (satConstraint choiceFormula) aoTree1

-- A choice where only ONE branch works:
-- branch 1: x0=T, x1=F → clause 2 fails (NOT x0 OR x1 = F OR F = F)
-- branch 2: x0=F, x1=T → both clauses pass
def aoTree2 : Term :=
  choice
    (.pair (literal 0 true) (literal 1 false))   -- fails clause 2
    (.pair (literal 0 false) (literal 1 true))    -- passes both

#eval verifyAO (satConstraint choiceFormula) aoTree2
-- Should be true: branch 2 passes

-- A choice where NO branch works:
def aoTree3 : Term :=
  choice
    (.pair (literal 0 false) (literal 1 false))   -- fails clause 1
    (.pair (literal 0 true) (literal 1 false))    -- fails clause 2

#eval verifyAO (satConstraint choiceFormula) aoTree3
-- Should be false: neither branch passes

/-! ## Nested AND-OR: the polynomial hierarchy

    One level of OR = existential = NP.
    AND under OR = universal check of existential witness = coNP check.
    OR under AND under OR = Sigma_2.

    The DEPTH of OR/AND alternation characterizes PH levels.

    Example: a Sigma_2 statement:
    "there exists an assignment such that for all perturbations,
    the formula still holds"

    AND-OR tree:
      OR(                         -- exists an assignment
        AND(                      -- for all perturbations
          branch_1_holds,
          branch_2_holds
        )
      )

    The outer OR searches over assignments.
    The inner AND checks all perturbations. -/

-- Sigma_2 tree: exists x0 such that forall x1, formula holds
-- choice(                                  -- exists x0
--   pair(x0=T,                             -- try x0=T
--     pair(check_x1=T, check_x1=F)),       -- forall x1
--   pair(x0=F,
--     pair(check_x1=T, check_x1=F))
-- )

def sigma2Formula : SATFormula :=
  [ [(0, true), (1, true)],      -- x0 OR x1
    [(0, true), (1, false)] ]    -- x0 OR NOT x1
  -- Satisfied iff x0 = true (regardless of x1)

-- Sigma_2 tree: outer choice over x0, inner AND over x1
def sigma2Tree : Term :=
  choice
    -- Branch 1: x0=T, check both x1 values
    (.pair (literal 0 true)
      (.pair (literal 1 true) (literal 1 false)))
    -- Branch 2: x0=F, check both x1 values
    (.pair (literal 0 false)
      (.pair (literal 1 true) (literal 1 false)))

-- The OR verifier picks the branch where x0=T
-- Within that branch, the AND checks both x1 values
-- But wait — the inner pair has x1=T and x1=F which is inconsistent!
-- The constraint would flag this.

-- Better encoding: separate the quantifiers
def sigma2Tree2 : Term :=
  choice
    -- Branch: x0=T (existential choice)
    (.pair
      -- Sub-branch: x1=T (universal check 1)
      (.pair (literal 0 true) (literal 1 true))
      -- Sub-branch: x1=F (universal check 2)
      (.pair (literal 0 true) (literal 1 false)))
    -- Branch: x0=F (existential choice)
    (.pair
      (.pair (literal 0 false) (literal 1 true))
      (.pair (literal 0 false) (literal 1 false)))

-- With x0=T: both sub-branches should satisfy the formula
-- clause 1 (x0 OR x1): T OR T = T, T OR F = T ✓
-- clause 2 (x0 OR NOT x1): T OR F = T, T OR T = T ✓
-- With x0=F: x1=T → clause 1: F OR T = T, clause 2: F OR F = F ✗

#eval verifyAO (satConstraint sigma2Formula) sigma2Tree2
-- Should be true: x0=T branch works (both sub-branches pass)

/-! ## AND-OR counting: verification vs construction cost

    For AND-OR trees, verification has TWO modes:
    - AND-node: check BOTH children (must verify both)
    - OR-node: check children until one PASSES (can short-circuit)

    The cost of verification:
    - AND tree (no choice): check all n leaves. O(n).
    - OR at root: check at most 2 subtrees. Best case O(n/2).
    - Deeply alternating: depends on the game tree structure.

    Alpha-beta pruning exploits this: in an AND-OR tree,
    once you find a passing branch at an OR node, skip the rest.
    Once you find a failing branch at an AND node, skip the rest.

    The CONSTRUCTION cost depends on the quantifier structure:
    - Existential only (NP): find ONE passing branch
    - Universal only (coNP): verify ALL branches
    - Alternating: game-tree search -/

/-- Count AND-OR verification operations. -/
def verifyAOCounting (C : Constraint) : Term → (Bool × ℕ)
  | .ground => (true, 0)
  | .pair _ .ground => (true, 0)
  | t =>
    if isChoice t then
      match t with
      | .pair _ (.pair a b) =>
        let (aOk, aCost) := verifyAOCounting C a
        if aOk then (true, aCost + 1)  -- short-circuit: first branch passed
        else
          let (bOk, bCost) := verifyAOCounting C b
          (bOk, aCost + bCost + 1)
      | _ => (false, 1)
    else
      match t with
      | .pair a b =>
        let passed := C.check a b
        if passed then
          let (aOk, aCost) := verifyAOCounting C a
          if !aOk then (false, aCost + 1)  -- short-circuit AND
          else
            let (bOk, bCost) := verifyAOCounting C b
            (bOk, aCost + bCost + 1)
        else (false, 1)
      | _ => (true, 0)

-- Verification costs
#eval verifyAOCounting (satConstraint choiceFormula) aoTree1
#eval verifyAOCounting (satConstraint choiceFormula) aoTree2
#eval verifyAOCounting (satConstraint sigma2Formula) sigma2Tree2

/-! ## Assessment

    The Choice constructor adds OR-branching to the rotation calculus.
    Combined with pair (AND), this gives AND-OR trees.

    WHAT'S NEW:
    1. Verification now has TWO modes (AND and OR) at each node.
       This is alternation — the structure underlying PH.
    2. Short-circuit evaluation reduces verification cost for OR
       nodes (skip remaining branches once one passes).
    3. The DEPTH of AND-OR alternation is a natural complexity
       measure: 0 = P, 1-existential = NP, 1-universal = coNP,
       k-alternating = Sigma_k.

    WHAT THIS ENABLES:
    - Express PH problems natively (not just NP)
    - Study the alternation hierarchy through tree structure
    - Connect to game-tree evaluation (alpha-beta pruning)
    - AND-OR tree evaluation is in P (polynomial verification)
    - AND-OR tree CONSTRUCTION under constraints = PH search

    LIMITATIONS:
    - The encoding is hacky (OR-marker via label sentinel)
    - A proper implementation would add `choice` to the Term inductive
    - The constraint interface doesn't know about OR nodes
    - Alpha-beta pruning in construction (not just verification)
      is where the real algorithmic content would live -/

end RotationCalculus
