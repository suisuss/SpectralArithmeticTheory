/-
  Choice-Based SAT: Embedding Search in AND-OR Trees
  =====================================================

  Instead of searching externally over assignments, embed the
  existential search INSIDE the tree structure using Choice nodes.

  Each variable becomes a Choice (OR) node:
    choice(x_i=true branch, x_i=false branch)

  The evaluator explores branches with short-circuit:
  - OR node: try first branch. If it passes, done (skip second).
  - AND node (pair): both children must pass.

  This is alpha-beta evaluation on a game tree.
  The tree structure IS the search strategy.
  The evaluation order IS the variable ordering.

  Key question: does this beat flat brute force on random 3-SAT?
  Alpha-beta prunes provably-failed branches. On structured instances,
  pruning could be massive. On random instances, it depends on the
  branching order.
-/

import SpectralArithmetic.Rotation.GraphOrder
import SpectralArithmetic.Rotation.Choice

namespace RotationCalculus

open Term

/-! ## AND-OR SAT tree construction

    Build an AND-OR tree that represents ALL possible assignments.
    The tree has depth n (one Choice per variable).
    Leaves are complete assignments checked against the formula.

    Structure for 3 variables:
      choice(                         -- x0
        choice(                       -- x1 (when x0=T)
          choice(leaf_TTT, leaf_TTF), -- x2 (when x0=T, x1=T)
          choice(leaf_TFT, leaf_TFF)  -- x2 (when x0=T, x1=F)
        ),
        choice(                       -- x1 (when x0=F)
          choice(leaf_FTT, leaf_FTF),
          choice(leaf_FFT, leaf_FFF)
        )
      )

    Total leaves: 2^n. But alpha-beta evaluation prunes branches
    that are provably unsatisfiable. -/

/-- Build a leaf term that encodes a complete assignment. -/
def assignmentLeaf (assignment : List (ℕ × Bool)) : Term :=
  fromList (assignment.map fun (v, p) => literal v p)

/-- Build the AND-OR search tree for SAT.
    Each level is a Choice over the next variable's values.
    `partialAssign` accumulates the assignment so far. -/
def buildSearchTree (formula : SATFormula) (vars : List ℕ)
    (partialAssign : List (ℕ × Bool)) : Term :=
  match vars with
  | [] =>
    -- Leaf: check if the complete assignment satisfies the formula
    -- Encode as a term that verifyAO can check
    if satisfiesFormula partialAssign formula then
      .pair .ground .ground  -- "true" leaf (non-ground pair = passes)
    else
      .ground  -- "false" leaf (ground = fails in our encoding below)
  | v :: rest =>
    -- Choice node: try v=true OR v=false
    let trueBranch := buildSearchTree formula rest ((v, true) :: partialAssign)
    let falseBranch := buildSearchTree formula rest ((v, false) :: partialAssign)
    choice trueBranch falseBranch

/-! ## AND-OR evaluator with cost counting

    Evaluates the search tree with short-circuit semantics:
    - Choice (OR): try first branch. If true, skip second.
    - Pair (AND): try first. If false, skip second.
    - Leaf pair(ground, ground): true.
    - Leaf ground: false. -/

/-- Evaluate an AND-OR search tree. Returns (result, nodes_visited). -/
def evalSearchTree : Term → (Bool × ℕ)
  | .ground => (false, 1)  -- false leaf
  | .pair .ground .ground => (true, 1)  -- true leaf
  | t =>
    if isChoice t then
      -- OR: try first branch, short-circuit on success
      match t with
      | .pair _ (.pair a b) =>
        let (aResult, aCost) := evalSearchTree a
        if aResult then (true, aCost + 1)
        else
          let (bResult, bCost) := evalSearchTree b
          (bResult, aCost + bCost + 1)
      | _ => (false, 1)
    else
      -- AND or other structure: check both
      match t with
      | .pair a b =>
        let (aResult, aCost) := evalSearchTree a
        if !aResult then (false, aCost + 1)
        else
          let (bResult, bCost) := evalSearchTree b
          (bResult, aCost + bCost + 1)
      | _ => (true, 1)

/-! ## SAT via AND-OR evaluation -/

/-- Solve SAT by building and evaluating an AND-OR search tree. -/
def choiceSAT (formula : SATFormula) (nVars : ℕ)
    : (Bool × ℕ) :=
  let vars := List.range nVars
  let tree := buildSearchTree formula vars []
  evalSearchTree tree

/-- Solve with a specific variable ordering. -/
def choiceSATOrdered (formula : SATFormula) (ordering : List ℕ)
    : (Bool × ℕ) :=
  let tree := buildSearchTree formula ordering []
  evalSearchTree tree

/-! ## Head-to-head: flat brute force vs AND-OR search tree

    On structured instances (reachInstance): does alpha-beta pruning help?
    On random instances (random3SAT): how much pruning occurs? -/

-- === Structured instances ===

#eval do
  let data := [1, 3, 5, 7].map fun reach =>
    let f := reachInstance 8 reach
    let (_, flat) := flatBruteForce f 8
    let (found, aoCost) := choiceSAT f 8
    s!"reach={reach} flat={flat} choice={aoCost} found={found}"
  IO.println s!"Structured n=8:"
  IO.println (String.intercalate "\n" data)

-- === Structured scaling ===

#eval do
  let data := [6, 8, 10, 12, 14].map fun n =>
    let f := reachInstance n 3
    let (_, flat) := flatBruteForce f n
    let (found, aoCost) := choiceSAT f n
    s!"n={n} flat={flat} choice={aoCost} found={found}"
  IO.println s!"Structured reach=3, scaling:"
  IO.println (String.intercalate "\n" data)

-- === Random 3-SAT n=8 ===

#eval do
  let n := 8
  let m := 32
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (found, aoCost) := choiceSAT f n
    s!"seed={seed} flat={flat} choice={aoCost} found={found}"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- === Random 3-SAT n=10 ===

#eval do
  let n := 10
  let m := 42
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (found, aoCost) := choiceSAT f n
    s!"seed={seed} flat={flat} choice={aoCost} found={found}"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- === Random 3-SAT n=12 ===

#eval do
  let n := 12
  let m := 48
  let data := [42, 100, 200, 300, 400].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (found, aoCost) := choiceSAT f n
    s!"seed={seed} flat={flat} choice={aoCost} found={found}"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- === Graph-ordered AND-OR ===

#eval do
  let n := 10
  let m := 42
  let data := [42, 456, 789].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, defaultCost) := choiceSAT f n
    let bfs := bfsOrdering f n
    let (_, bfsCost) := choiceSATOrdered f bfs
    let md := minDegOrdering f n
    let (_, mdCost) := choiceSATOrdered f md
    s!"seed={seed} flat={flat} default={defaultCost} bfs={bfsCost} mindeg={mdCost}"
  IO.println s!"Random n={n} m={m} with graph ordering:"
  IO.println (String.intercalate "\n" data)

/-! ## The pruning ratio

    The AND-OR tree has 2^n leaves. Alpha-beta prunes some.
    The pruning ratio = nodes_visited / 2^n.
    Low ratio = heavy pruning = structured instance.
    High ratio = little pruning = random/hard instance.

    This ratio is another complexity fingerprint — it measures
    how much the search tree can be trimmed by constraint propagation. -/

#eval do
  let data := [6, 8, 10, 12].map fun n =>
    let f := reachInstance n 3
    let (_, cost) := choiceSAT f n
    let total := 2^n
    s!"structured n={n}: visited={cost}/{total} ratio={cost*100/total}%"
  IO.println s!"Pruning ratio (structured reach=3):"
  IO.println (String.intercalate "\n" data)

#eval do
  let data := [6, 8, 10, 12].map fun n =>
    let f := random3SAT n (4*n) 42
    let (_, cost) := choiceSAT f n
    let total := 2^n
    s!"random n={n}: visited={cost}/{total} ratio={cost*100/total}%"
  IO.println s!"Pruning ratio (random ratio=4):"
  IO.println (String.intercalate "\n" data)

/-! ## Assessment

    The AND-OR search tree embeds the entire search process in the
    tree structure. There is no external search loop — the evaluator
    walks the tree with short-circuit pruning.

    This is fundamentally different from SmartDAG:
    - SmartDAG: spatial decomposition (split variables into groups)
    - Choice SAT: temporal decomposition (try one variable at a time)

    SmartDAG is tree decomposition. Choice SAT is backtracking search
    with pruning. They're dual strategies operating on the same problem.

    The pruning ratio measures how much of the 2^n search space is
    actually explored. For structured instances with constraint
    propagation, pruning can be massive. For random instances at
    the phase transition, pruning is minimal.

    Connection to the polynomial hierarchy:
    - One level of Choice (existential): NP search
    - Choice nested in pair nested in Choice: Sigma_2
    - Alternating levels: the full polynomial hierarchy
    - The DEPTH of Choice nesting characterizes PH level -/

end RotationCalculus
