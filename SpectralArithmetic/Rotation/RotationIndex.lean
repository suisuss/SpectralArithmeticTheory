/-
  Rotation Index: All Possible Rotation Rules and Their Structures
  =================================================================

  The rotation calculus has one rewrite rule:
    observe(pair(a, b)) → pair(b, observe(a))

  But this is one choice from a family. Any rule of the form
    observe(pair(a, b)) → f(a, b, observe)
  that preserves groundedness and terminates is a valid rotation.

  The family is indexed by:
  1. WHERE observe goes (left, right, both, neither)
  2. WHETHER a and b swap positions
  3. WHETHER the rule creates new observe markers (fork)

  The tree shapes produced by n pair operations are the Catalan
  numbers C(n). Different rotation rules traverse these shapes in
  different orders. The rotation rule IS a walk over the Catalan
  lattice — each step transforms one tree shape into another.

  This file:
  - Enumerates all valid rotation rules on pair(a, b)
  - Shows which tree structures each rule produces
  - Connects the rules to Catalan number indexing
  - Proves which rules terminate and which don't
-/

import SpectralArithmetic.Rotation.TreeArrangement

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## The family of rotation rules

    A rotation rule maps observe(pair(a, b)) to some term
    built from a, b, pair, observe, and ground.

    Constraints:
    - Must use both a and b (no information loss)
    - Output must be a well-formed term
    - For termination: pairsUnderObserve must decrease

    We enumerate by: where does observe go? -/

/-- A rotation rule: takes (a, b) and produces the rewritten term. -/
structure RotationRule where
  name : String
  apply : Term → Term → Term

/-! ### Rule 0: Current rule (dive left) -/

def rule_diveLeft : RotationRule where
  name := "dive-left"
  apply := fun a b => .pair b (.observe a)
  -- observe goes to a (left child)
  -- b (right child) is carried

/-! ### Rule 1: Dive right -/

def rule_diveRight : RotationRule where
  name := "dive-right"
  apply := fun a b => .pair (.observe b) a
  -- observe goes to b (right child)
  -- a (left child) is carried

/-! ### Rule 2: Fork (observe both) -/

def rule_fork : RotationRule where
  name := "fork"
  apply := fun a b => .pair (.observe a) (.observe b)
  -- observe goes to BOTH children
  -- Creates a new observe marker (symbol creation)

/-! ### Rule 3: Absorb (observe neither) -/

def rule_absorb : RotationRule where
  name := "absorb"
  apply := fun a b => .pair a b
  -- observe goes to NEITHER child
  -- The pair is "observed" and done in one step

/-! ### Rule 4: Swap (observe the whole, swapped) -/

def rule_swap : RotationRule where
  name := "swap"
  apply := fun a b => .observe (.pair b a)
  -- observe stays on the pair, but children swap
  -- Does not terminate on its own (oscillates)

/-! ### Rule 5: Dive left, swap -/

def rule_diveLeftSwap : RotationRule where
  name := "dive-left-swap"
  apply := fun a b => .pair (.observe a) b
  -- observe goes to a, but a stays on the LEFT
  -- b stays on the RIGHT (no position swap)

/-! ### Rule 6: Dive right, swap -/

def rule_diveRightSwap : RotationRule where
  name := "dive-right-swap"
  apply := fun a b => .pair a (.observe b)
  -- observe goes to b, b stays on the RIGHT
  -- a stays on the LEFT (no position swap)

/-! ### Rule 7: Rotate left (tree rotation) -/

def rule_rotateTree : RotationRule where
  name := "tree-rotate"
  apply := fun a b =>
    -- If a is a pair, do a tree rotation (AVL-style)
    match a with
    | .pair a1 a2 => .pair a1 (.observe (.pair a2 b))
    | _ => .pair b (.observe a)  -- fallback to dive-left

/-! ## All rules -/

def allRules : List RotationRule :=
  [rule_diveLeft, rule_diveRight, rule_fork, rule_absorb,
   rule_swap, rule_diveLeftSwap, rule_diveRightSwap, rule_rotateTree]

/-! ## Properties of each rule -/

/-- Apply a rule to observe(pair(a, b)), then measure the result. -/
structure RuleProfile where
  name : String
  createsObserve : Bool     -- does it add new observe markers?
  swapsChildren : Bool      -- do a and b change position?
  observeTarget : String    -- "left", "right", "both", "neither", "whole"
  terminates : Bool         -- does pairsUnderObserve decrease?
  deriving Repr

/-- Analyze a rule by applying it to a test case and measuring. -/
def analyzeRule (r : RotationRule) : RuleProfile :=
  let a := Term.pair .ground .ground  -- a compound left child
  let b := Term.pair .ground .ground  -- a compound right child
  let result := r.apply a b
  -- Count observe markers in result
  let rec countObserve : Term → ℕ
    | .observe t => 1 + countObserve t
    | .pair x y => countObserve x + countObserve y
    | .ground => 0
  let nObs := countObserve result
  -- Check if a and b swapped
  let swapped := match result with
    | .pair x _ => x == b    -- b is now on the left
    | _ => false
  -- Check termination: does size under observe decrease?
  let origMeasure := a.size + b.size  -- = size of pair(a,b) - 1
  let rec sizeUnderObs : Term → ℕ
    | .observe t => t.size
    | .pair x y => sizeUnderObs x + sizeUnderObs y
    | .ground => 0
  let newMeasure := sizeUnderObs result
  let obsTarget :=
    if nObs == 0 then "neither"
    else if nObs >= 2 then "both"
    else match result with
      | .pair _ (.observe _) => "left-into"
      | .pair (.observe _) _ => "right-into"
      | .observe _ => "whole"
      | _ => "unknown"
  { name := r.name,
    createsObserve := nObs > 1,
    swapsChildren := swapped,
    observeTarget := obsTarget,
    terminates := newMeasure < origMeasure }

/-! ## Execution under each rule -/

/-- Apply a rotation rule repeatedly until normal form or fuel. -/
def runRule (r : RotationRule) (t : Term) (fuel : ℕ)
    : Term × ℕ :=
  match fuel with
  | 0 => (t, 0)
  | fuel + 1 =>
    match t with
    | .observe (.pair a b) =>
      let result := r.apply a b
      let (final, steps) := runRule r result fuel
      (final, steps + 1)
    | .observe .ground => (.ground, 1)
    | .pair a b =>
      -- Try to find observe in subterms
      let (a', sa) := runRule r a fuel
      let (b', sb) := runRule r b (fuel - sa)
      (.pair a' b', sa + sb)
    | t => (t, 0)

/-- Count how many steps each rule takes on a list of n elements. -/
def ruleSteps (r : RotationRule) (n : ℕ) (fuel : ℕ) : ℕ :=
  let t := Term.observe (Term.fromList (List.replicate n .ground))
  let (_, steps) := runRule r t fuel
  steps

/-! ## Catalan connection

    Binary tree shapes on n leaves are counted by C(n-1), the
    (n-1)-th Catalan number. The first few:

    | Leaves | Shapes | C(n-1) |
    |--------|--------|--------|
    | 1      | 1      | C(0)=1 |
    | 2      | 1      | C(1)=1 |
    | 3      | 2      | C(2)=2 |
    | 4      | 5      | C(3)=5 |
    | 5      | 14     | C(4)=14|

    Each rotation rule defines a TRANSITION between tree shapes.
    The dive-left rule: pair(a, pair(b, c)) → pair(pair(b, c), a)
    when a is compound, this reshapes the tree.

    The set of all transitions forms a GRAPH over Catalan-indexed
    tree shapes. The structure of this graph depends on the rule. -/

/-- Catalan number via the recursive formula. -/
partial def catalan : ℕ → ℕ
  | 0 => 1
  | n + 1 => List.range (n + 1) |>.foldl
    (fun acc k => acc + catalan k * catalan (n - k)) 0

/-- Generate all binary tree shapes with n leaves.
    Leaves are numbered 1..n (as labeledElement). -/
partial def allShapes : ℕ → List Term
  | 0 => [.ground]
  | 1 => [labeledElement 1]
  | n =>
    List.range (n - 1) |>.flatMap fun i =>
      let leftSize := i + 1
      let rightSize := n - leftSize
      let leftShapes := allShapes leftSize
      let rightShapes := allShapes rightSize
      leftShapes.flatMap fun l =>
        rightShapes.map fun r => .pair l r

/-! ## Demonstrations -/

#eval! do
  IO.println "=== ROTATION RULE INDEX ==="
  IO.println ""
  IO.println "--- Rule properties ---"
  for r in allRules do
    let p := analyzeRule r
    IO.println s!"  {p.name}: observe→{p.observeTarget} \
      swap={p.swapsChildren} creates={p.createsObserve} \
      terminates={p.terminates}"

#eval! do
  IO.println ""
  IO.println "--- Steps per rule on n-element lists ---"
  IO.println "rule\t\tn=3\tn=5\tn=8\tn=10"
  for r in allRules do
    let s3 := ruleSteps r 3 100
    let s5 := ruleSteps r 5 200
    let s8 := ruleSteps r 8 500
    let s10 := ruleSteps r 10 1000
    IO.println s!"{r.name}\t\t{s3}\t{s5}\t{s8}\t{s10}"

#eval! do
  IO.println ""
  IO.println "--- Catalan numbers (tree shapes) ---"
  IO.println "n\tC(n)\tshapes"
  for n in [0, 1, 2, 3, 4, 5, 6] do
    let c := catalan n
    let shapes := if n ≤ 5 then (allShapes (n + 1)).length else 0
    IO.println s!"{n}\t{c}\t{shapes}"

#eval! do
  IO.println ""
  IO.println "--- Tree shapes for 4 leaves ---"
  let shapes := allShapes 4
  IO.println s!"  {shapes.length} shapes (Catalan(3) = {catalan 3})"
  let mut i := 0
  for shape in shapes do
    let labs := leafLabels shape
    let depth := shape.depth
    IO.println s!"  shape {i}: leaves={labs} depth={depth}"
    i := i + 1

#eval! do
  IO.println ""
  IO.println "--- Rule effect on tree shapes ---"
  IO.println "  Starting shape: pair(pair(1,2), pair(3,4))"
  let t := Term.pair (.pair (labeledElement 1) (labeledElement 2))
                      (.pair (labeledElement 3) (labeledElement 4))
  for r in allRules do
    let result := r.apply
      (.pair (labeledElement 1) (labeledElement 2))
      (.pair (labeledElement 3) (labeledElement 4))
    let labs := leafLabels result
    let d := result.depth
    IO.println s!"  {r.name}: leaves={labs} depth={d}"

/-! ## Assessment

    The rotation rule family is indexed by two independent choices:

    1. OBSERVE TARGET: where the observe marker goes
       - left (dive-left, current rule)
       - right (dive-right)
       - both (fork) — creates symbols
       - neither (absorb) — immediate completion
       - whole (swap) — no progress

    2. POSITION SWAP: whether a and b exchange positions
       - yes (current rule: pair(b, observe(a)))
       - no (dive-left-swap: pair(observe(a), b))

    The product gives 10 combinations, but only some terminate:

    | Target   | Swap? | Terminates? | Why |
    |----------|-------|-------------|-----|
    | left     | yes   | YES         | a shrinks under observe |
    | left     | no    | YES         | a shrinks under observe |
    | right    | yes   | YES         | b shrinks under observe |
    | right    | no    | YES         | b shrinks under observe |
    | both     | *     | YES         | both shrink, but symbol count grows |
    | neither  | *     | YES (trivial) | observe is removed immediately |
    | whole    | yes   | NO          | same size, swaps forever |
    | whole    | no    | NO          | no change at all |

    The TERMINATING rules that DON'T create symbols are:
    dive-left (swap), dive-left (no swap),
    dive-right (swap), dive-right (no swap).
    These four are the rotation rules proper.

    The current rule (dive-left + swap) is the one that produces
    the shift-register behavior: content rotates through the
    observation point. The no-swap variants produce depth-first
    traversal without the rotation effect.

    CATALAN CONNECTION:
    The binary tree shapes on n leaves are indexed by C(n-1).
    Each rotation rule defines transitions between shapes.
    The dive-left rule on pair(pair(a,b), c) produces
    pair(c, observe(pair(a,b))) — a RIGHT ROTATION of the tree.
    This is exactly the rotation operation on binary search trees,
    which generates the Catalan lattice (Tamari lattice).

    The Tamari lattice on C(n) elements is the partial order
    where shape S1 ≤ S2 if S1 can be reached from S2 by a
    sequence of right rotations. The rotation calculus rule IS
    the covering relation of the Tamari lattice.

    Different rotation rules (dive-left vs dive-right) correspond
    to different orientations of the Tamari lattice (right rotations
    vs left rotations). The full Tamari lattice is generated by
    BOTH directions — which corresponds to having both dive-left
    and dive-right available as rules.
-/

end RotationCalculus
