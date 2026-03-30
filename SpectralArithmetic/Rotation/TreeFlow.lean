/-
  Tree Rotation: Asymmetric Information Flow
  ============================================

  TreeComplexity.lean identified one genuinely novel structural feature:
  the rotation rule's sequential traversal creates asymmetric information
  flow. Left is processed before right. Left's constraints can see right
  (as carried content). Right's constraints cannot see left (consumed).

  But verifyTree processes both children INDEPENDENTLY — no flow at all.
  This file implements the asymmetric traversal properly and tests whether
  the asymmetry changes which arrangements are valid.

  The key construction: verifyTreeCtx passes a CONTEXT through the tree.
  - At each node: check C(left, right, context)
  - Descend left with context = (right, outer_context)
  - Descend right with context = outer_context only (left consumed)
  - LEFT sees RIGHT as context. RIGHT does not see LEFT.
-/

import SpectralArithmetic.Rotation.TreeArrangement

namespace RotationCalculus

open Term

/-! ## Context-aware tree verification

    The symmetric verifyTree checks C(left, right) independently at each
    node, then verifies both subtrees with no shared state.

    The asymmetric verifyTreeCtx threads context through the traversal:
    - Left subtree gets (right sibling ++ outer context) as its context
    - Right subtree gets (outer context only) — left is already consumed

    The constraint receives the current node AND the accumulated context.
    This models the rotation rule's behavior: when observe descends left,
    the right sibling becomes carried content visible to inner checks. -/

/-- Verify a tree with accumulated context.
    The context represents "what's visible as carried content." -/
def verifyTreeCtx (C : Constraint) : Term → Term → Bool
  | .ground, _ => true
  | .pair _ .ground, _ => true     -- leaf: no internal structure to check
  | .pair a b, ctx =>
    -- Check: constraint sees left child against (right child, context)
    let rightWithCtx := .pair b ctx
    if C.check a rightWithCtx then
      -- Left subtree sees right+context
      verifyTreeCtx C a rightWithCtx &&
      -- Right subtree sees ONLY outer context (left consumed)
      verifyTreeCtx C b ctx
    else false
  | .observe t, ctx => verifyTreeCtx C t ctx

/-! ## Context-sensitive constraint

    To demonstrate that the asymmetry matters, we need a constraint that
    behaves differently depending on context. A constraint that only
    checks the immediate children (like balancedConstraint) is insensitive
    to context — it gives the same result regardless of what's carried.

    Context-sensitive constraint: "my sum must be ≤ half the visible total."
    - Left sees: its own subtree + right + context → visible total is everything
    - Right sees: its own subtree + context (no left) → visible total is smaller
    - This means LEFT faces a tighter proportionality check than RIGHT. -/

/-- Sum of ALL visible content: the term itself plus context. -/
def visibleSum (t : Term) (ctx : Term) : ℕ :=
  treeSum t + treeSum ctx

/-- "Proportional" constraint: left child's sum must be ≤ half the
    total visible content (left + right + context).
    This is context-sensitive: the "total" changes depending on
    what's in the context. -/
def proportionalConstraint : Constraint where
  check := fun a b =>
    if isNode a && isNode b then
      -- a's sum ≤ half of (a + b) where b includes context
      2 * treeSum a ≤ treeSum a + treeSum b
    else
      true

/-! ## Demonstration: symmetric vs asymmetric verification -/

-- Elements: {1, 2, 3, 6}
-- Total sum = 12

-- Tree: ((1,2),(3,6))
-- Left = {1,2} sum=3, Right = {3,6} sum=9
def demo1 : Term := .pair (.pair e1 e2) (.pair e3 e6)

-- Tree: ((3,6),(1,2))
-- Left = {3,6} sum=9, Right = {1,2} sum=3
def demo2 : Term := .pair (.pair e3 e6) (.pair e1 e2)

/-! ### Symmetric verification (both children independent)

    proportionalConstraint checks: 2 * sum(left) ≤ sum(left) + sum(right)
    Which simplifies to: sum(left) ≤ sum(right)

    demo1: sum(left)=3 ≤ sum(right)=9 → true
    demo2: sum(left)=9 ≤ sum(right)=3 → false -/

#eval verifyTree proportionalConstraint demo1  -- true
#eval verifyTree proportionalConstraint demo2  -- false

/-! ### Asymmetric verification (context accumulates)

    Same constraint, but now with context passing.
    Starting context = ground (empty).

    demo1: pair(pair(1,2), pair(3,6))
    - Top: C(pair(1,2), pair(pair(3,6), ground))
      a=pair(1,2) sum=3, b=pair(pair(3,6),ground) sum=9
      2*3=6 ≤ 3+9=12 → true
    - Left (pair(1,2)) with ctx=pair(pair(3,6),ground):
      C(1, pair(2, pair(pair(3,6),ground)))? Both not nodes → true
    - Right (pair(3,6)) with ctx=ground:
      C(3, pair(6, ground))? Both not nodes → true

    demo2: pair(pair(3,6), pair(1,2))
    - Top: C(pair(3,6), pair(pair(1,2), ground))
      a=pair(3,6) sum=9, b=pair(pair(1,2),ground) sum=3
      2*9=18 ≤ 9+3=12? NO → false -/

#eval verifyTreeCtx proportionalConstraint demo1 .ground  -- true
#eval verifyTreeCtx proportionalConstraint demo2 .ground  -- false

/-! For this constraint (sum(left) ≤ sum(right)), symmetric and asymmetric
    give the same result. The constraint doesn't actually USE the context
    beyond the immediate sibling — it only sees a and b.

    To get different results, we need a constraint that inspects the
    context SEPARATELY from the sibling. -/

/-! ## A truly context-sensitive constraint

    "Budget constraint": the sum of this subtree must be ≤ half the
    total budget, where the budget is (this subtree + all context).

    Key: the CONTEXT term is inspected separately from the sibling.
    When left is processed, context includes the right sibling → bigger budget.
    When right is processed, context excludes the left sibling → smaller budget.

    This means the same subtree might pass as "left" but fail as "right"
    (or vice versa) depending on what context is accumulated. -/

def budgetConstraint : Constraint where
  check := fun a b =>
    -- "a's sum must be ≤ half the visible total"
    -- visible total = sum(a) + sum(b) where b = pair(sibling, context)
    let mySum := treeSum a
    let totalVisible := mySum + treeSum b
    if isNode a then
      2 * mySum ≤ totalVisible
    else
      true  -- leaves always pass

-- demo1 under budget with context:
-- Top: pair(pair(1,2), pair(3,6)), ctx=ground
-- C(pair(1,2), pair(pair(3,6), ground)):
--   mySum=3, totalVisible=3+9=12, 2*3=6 ≤ 12 → true
-- Left pair(1,2), ctx=pair(pair(3,6), ground):
--   Both leaves → true
-- Right pair(3,6), ctx=ground:
--   C(3, pair(6, ground)): leaf → true

#eval verifyTreeCtx budgetConstraint demo1 .ground  -- true

-- demo2 under budget with context:
-- Top: pair(pair(3,6), pair(1,2)), ctx=ground
-- C(pair(3,6), pair(pair(1,2), ground)):
--   mySum=9, totalVisible=9+3=12, 2*9=18 ≤ 12? NO → false

#eval verifyTreeCtx budgetConstraint demo2 .ground  -- false

/-! ## The deeper test: 3-level tree with asymmetric flow

    With deeper trees, the asymmetry compounds. Context accumulates
    differently on the left spine vs the right spine.

    8 elements: {1, 2, 3, 4, 5, 6, 7, 8}, total = 36.

    Tree A: ((1,8),(5,4)) | ((2,7),(3,6))
    - Top context: ground
    - Left ((1,8),(5,4)) sees right ((2,7),(3,6)) as context → budget = 36
    - Right ((2,7),(3,6)) sees NO left → budget = 18

    Tree B: ((2,7),(3,6)) | ((1,8),(5,4))
    - Top context: ground
    - Left ((2,7),(3,6)) sees right ((1,8),(5,4)) as context → budget = 36
    - Right ((1,8),(5,4)) sees NO left → budget = 18

    The budget constraint is symmetric in the immediate check
    (sum(left) ≤ half total), but the CONTEXT makes the inner
    checks different. -/

-- Tree A: left-heavy (sums: (9,9) | (9,9))
def treeA : Term :=
  .pair (.pair (.pair e1 e8) (.pair e5 e4))
        (.pair (.pair e2 e7) (.pair e3 e6))

-- Tree B: swapped top-level children
def treeB : Term :=
  .pair (.pair (.pair e2 e7) (.pair e3 e6))
        (.pair (.pair e1 e8) (.pair e5 e4))

-- Symmetric: both should give same result (children are independent)
#eval verifyTree budgetConstraint treeA   -- ?
#eval verifyTree budgetConstraint treeB   -- ?

-- Asymmetric: may differ (context flow is different)
#eval verifyTreeCtx budgetConstraint treeA .ground  -- ?
#eval verifyTreeCtx budgetConstraint treeB .ground  -- ?

/-! ## Finding the asymmetry gap

    To find arrangements where symmetric and asymmetric verification
    DISAGREE, we need the budget to be tight enough that the context
    makes or breaks it.

    Constraint: "my sum must be STRICTLY LESS than 2/3 of visible total"
    This is tighter than half, making the budget sensitivity stronger. -/

def tightBudgetConstraint : Constraint where
  check := fun a b =>
    let mySum := treeSum a
    let totalVisible := mySum + treeSum b
    if isNode a then
      3 * mySum < 2 * totalVisible  -- sum < 2/3 of total
    else
      true

-- Build several 6-element trees {1, 2, 3, 4, 5, 6}, total = 21

-- ((1,2),(3,(4,(5,6))))
def asym1 : Term := .pair (.pair e1 e2) (.pair e3 (.pair e4 (.pair e5 e6)))
-- ((5,6),(1,(2,(3,4))))
def asym2 : Term := .pair (.pair e5 e6) (.pair e1 (.pair e2 (.pair e3 e4)))
-- ((3,4),(1,(2,(5,6))))
def asym3 : Term := .pair (.pair e3 e4) (.pair e1 (.pair e2 (.pair e5 e6)))

-- Symmetric
#eval verifyTree tightBudgetConstraint asym1
#eval verifyTree tightBudgetConstraint asym2
#eval verifyTree tightBudgetConstraint asym3

-- Asymmetric
#eval verifyTreeCtx tightBudgetConstraint asym1 .ground
#eval verifyTreeCtx tightBudgetConstraint asym2 .ground
#eval verifyTreeCtx tightBudgetConstraint asym3 .ground

/-! ## Brute-force gap search

    Systematically find tree arrangements where symmetric and
    asymmetric verification disagree. -/

/-- Find arrangements where symmetric and asymmetric verification differ. -/
def findAsymmetryGap (C : Constraint) (elements : List Term)
    : List (List ℕ × Bool × Bool) :=
  let ps := perms elements
  let allArrangements := ps.flatMap fun perm => allTrees perm
  allArrangements.filterMap fun tree =>
    let sym := verifyTree C tree
    let asym := verifyTreeCtx C tree .ground
    if sym != asym then
      some (leafLabels tree, sym, asym)
    else
      none

-- Search for asymmetry gaps with budget constraint on {1, 2, 3, 4}
#eval findAsymmetryGap budgetConstraint [e1, e2, e3, e4]
#eval findAsymmetryGap tightBudgetConstraint [e1, e2, e3, e4]

-- Count the gaps
#eval (findAsymmetryGap budgetConstraint [e1, e2, e3, e4]).length
#eval (findAsymmetryGap tightBudgetConstraint [e1, e2, e3, e4]).length

-- Break down: symmetric-only vs asymmetric-only
#eval
  let gaps := findAsymmetryGap budgetConstraint [e1, e2, e3, e4]
  let symOnly := gaps.filter (fun | (_, true, false) => true | _ => false)
  let asymOnly := gaps.filter (fun | (_, false, true) => true | _ => false)
  s!"sym-only: {symOnly.length}, asym-only: {asymOnly.length}"

/-! ## Assessment

    If findAsymmetryGap returns non-empty results, the asymmetric
    traversal (rotation-style) creates genuinely different acceptance
    sets than symmetric verification. This would mean:

    1. The TRAVERSAL ORDER is computationally significant — not just
       a presentation choice but a structural feature that changes
       which arrangements are valid.

    2. The rotation rule's left-first descent is not equivalent to
       "check all nodes independently" — it creates information flow
       that affects the constraint's power.

    3. Tree rotation with context-aware constraints is a DIFFERENT
       computational model from symmetric tree-CSP.

    If findAsymmetryGap returns empty, the asymmetry doesn't affect
    satisfiability for these constraints on small inputs. The traversal
    order would be presentational, not structural.

    Either result is informative. -/

end RotationCalculus
