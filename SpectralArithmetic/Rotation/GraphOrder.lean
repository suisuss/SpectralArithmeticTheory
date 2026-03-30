/-
  Graph-Aware Variable Ordering for SAT
  =======================================

  SmartDAG fails on random 3-SAT because the variable order (0,1,2,...)
  is arbitrary — splitting at the midpoint doesn't align with the
  formula's interaction structure. Variables that share many clauses
  may be split into different subtrees, creating expensive cross-partition
  checks.

  Fix: build the variable interaction graph, reorder variables so that
  tightly coupled variables are adjacent, THEN apply SmartDAG. The
  contiguous splits will align with graph communities.

  This is the standard preprocessing step for tree decomposition:
  find a good elimination ordering. We implement two strategies:
  1. BFS ordering from the most-connected variable
  2. Min-degree ordering (eliminate least-connected first)
-/

import SpectralArithmetic.Rotation.Random3SAT

namespace RotationCalculus

open Term

/-! ## Variable interaction graph -/

/-- Build the interaction graph: for each pair of variables that
    share a clause, record the edge with weight = number of shared clauses. -/
def interactionGraph (formula : SATFormula) (n : ℕ)
    : List (ℕ × ℕ × ℕ) :=  -- (var1, var2, weight)
  let pairs := (List.range n).flatMap fun i =>
    (List.range n).filterMap fun j =>
      if i < j then
        let weight := formula.foldl (fun acc clause =>
          let hasI := clause.any fun (v, _) => v == i
          let hasJ := clause.any fun (v, _) => v == j
          if hasI && hasJ then acc + 1 else acc) 0
        if weight > 0 then some (i, j, weight) else none
      else none
  pairs

/-- Get the degree (number of neighbors) of a variable. -/
def degree (graph : List (ℕ × ℕ × ℕ)) (v : ℕ) : ℕ :=
  graph.foldl (fun acc (a, b, _) =>
    if a == v || b == v then acc + 1 else acc) 0

/-- Get neighbors of a variable. -/
def neighbors (graph : List (ℕ × ℕ × ℕ)) (v : ℕ) : List ℕ :=
  graph.filterMap fun (a, b, _) =>
    if a == v then some b
    else if b == v then some a
    else none

-- Inspect the interaction graph of a random formula
#eval
  let f := random3SAT 8 32 42
  let g := interactionGraph f 8
  (g.length, g.take 10)

/-! ## BFS ordering: start from highest-degree variable

    BFS groups tightly connected variables together. Contiguous
    splits of BFS order tend to cut fewer edges. -/

/-- BFS ordering from a start variable. -/
partial def bfsOrder (graph : List (ℕ × ℕ × ℕ)) (n : ℕ)
    (start : ℕ) : List ℕ :=
  let rec go (queue : List ℕ) (visited : List ℕ) : List ℕ :=
    match queue with
    | [] =>
      -- Add any unvisited variables (disconnected components)
      let remaining := (List.range n).filter fun v => !visited.contains v
      if remaining.isEmpty then visited
      else go remaining visited
    | v :: rest =>
      if visited.contains v then go rest visited
      else
        let nbrs := (neighbors graph v).filter fun u => !visited.contains u
        go (rest ++ nbrs) (visited ++ [v])
  go [start] []

/-- Find the highest-degree variable. -/
def highestDegree (graph : List (ℕ × ℕ × ℕ)) (n : ℕ) : ℕ :=
  let scored := (List.range n).map fun v => (degree graph v, v)
  let sorted := scored.toArray.insertionSort (fun a b => a.1 > b.1)
  match sorted.toList.head? with
  | some (_, v) => v
  | none => 0

/-- BFS ordering starting from the highest-degree variable. -/
def bfsOrdering (formula : SATFormula) (n : ℕ) : List ℕ :=
  let graph := interactionGraph formula n
  let start := highestDegree graph n
  bfsOrder graph n start

-- Check BFS ordering
#eval bfsOrdering (random3SAT 8 32 42) 8

/-! ## Min-degree ordering: eliminate least-connected first

    This is the standard heuristic for tree decomposition.
    Variables with few connections are placed at the leaves of
    the decomposition tree. Highly connected variables end up
    at the root where they can be shared. -/

/-- Min-degree ordering: repeatedly pick the least-connected variable. -/
partial def minDegreeOrder (graph : List (ℕ × ℕ × ℕ)) (n : ℕ)
    : List ℕ :=
  let rec go (remaining : List ℕ) (acc : List ℕ) : List ℕ :=
    match remaining with
    | [] => acc
    | _ =>
      -- Find the variable with minimum degree among remaining
      let degrees := remaining.map fun v =>
        let d := remaining.foldl (fun count u =>
          if graph.any fun (a, b, _) =>
            (a == v && b == u) || (a == u && b == v)
          then count + 1 else count) 0
        (d, v)
      let sorted := degrees.toArray.insertionSort (fun a b => a.1 < b.1)
      match sorted.toList.head? with
      | some (_, v) =>
        go (remaining.filter (· != v)) (acc ++ [v])
      | none => acc
  go (List.range n) []

def minDegOrdering (formula : SATFormula) (n : ℕ) : List ℕ :=
  let graph := interactionGraph formula n
  minDegreeOrder graph n

#eval minDegOrdering (random3SAT 8 32 42) 8

/-! ## Graph-ordered SmartDAG

    Apply SmartDAG with variables reordered according to the graph. -/

/-- Reorder a formula's variable indices according to a permutation.
    perm[i] = new index for old variable i. -/
def reorderFormula (formula : SATFormula) (perm : List ℕ) : SATFormula :=
  formula.map fun clause =>
    clause.map fun (v, p) =>
      let newIdx := perm.findIdx (· == v)
      (newIdx, p)

/-- Inverse permutation. -/
def invertPerm (perm : List ℕ) : List ℕ :=
  let n := perm.length
  (List.range n).map fun i =>
    perm.findIdx (· == i)

/-- Run SmartDAG with graph-aware variable ordering.
    Returns (solution in ORIGINAL variable order, cost). -/
def graphSmartDAG (formula : SATFormula) (n : ℕ) (k : ℕ)
    (ordering : List ℕ)
    : Option (List (ℕ × Bool)) × ℕ :=
  -- Reorder formula so ordered vars become 0,1,2,...
  let invPerm := invertPerm ordering
  let reordered := reorderFormula formula invPerm
  let (result, cost) := satSmartDAG reordered n k
  -- Map solution back to original variable indices
  let mapped := result.map fun assign =>
    assign.map fun (v, p) =>
      let origVar := ordering.getD v v
      (origVar, p)
  (mapped, cost)

/-! ## Head-to-head: default vs BFS vs min-degree ordering -/

-- n=8, ratio=4, multiple seeds
#eval do
  let n := 8
  let m := 32
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, def_) := satSmartDAG f n 2
    let bfs := bfsOrdering f n
    let (_, bfsCost) := graphSmartDAG f n 2 bfs
    let md := minDegOrdering f n
    let (_, mdCost) := graphSmartDAG f n 2 md
    s!"seed={seed} flat={flat} default={def_} bfs={bfsCost} mindeg={mdCost}"
  IO.println s!"n={n} m={m} ratio=4:"
  IO.println (String.intercalate "\n" data)

-- n=10, ratio=4.2, multiple seeds
#eval do
  let n := 10
  let m := 42
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, def_) := satSmartDAG f n 2
    let bfs := bfsOrdering f n
    let (_, bfsCost) := graphSmartDAG f n 2 bfs
    let md := minDegOrdering f n
    let (_, mdCost) := graphSmartDAG f n 2 md
    s!"seed={seed} flat={flat} default={def_} bfs={bfsCost} mindeg={mdCost}"
  IO.println s!"n={n} m={m} ratio=4.2:"
  IO.println (String.intercalate "\n" data)

-- n=12, ratio=4
#eval do
  let n := 12
  let m := 48
  let data := [42, 100, 200, 300, 400].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, def_) := satSmartDAG f n 2
    let bfs := bfsOrdering f n
    let (_, bfsCost) := graphSmartDAG f n 2 bfs
    let md := minDegOrdering f n
    let (_, mdCost) := graphSmartDAG f n 2 md
    s!"seed={seed} flat={flat} default={def_} bfs={bfsCost} mindeg={mdCost}"
  IO.println s!"n={n} m={m} ratio=4:"
  IO.println (String.intercalate "\n" data)

/-! ## Assessment

    If graph-aware ordering helps:
    - BFS/min-degree costs < default SmartDAG cost on random instances
    - The improvement comes from aligning splits with graph communities
    - This demonstrates that SmartDAG's failure on random SAT was due
      to poor ordering, not fundamental tree-decomposition limits

    If graph-aware ordering doesn't help:
    - Random 3-SAT genuinely resists tree decomposition regardless
      of variable ordering
    - The interaction graph is too dense for any tree-based approach
    - A fundamentally different strategy (not tree-based) is needed

    The comparison directly tests whether the complexity lens provided
    by tree decomposition can be improved with graph preprocessing,
    or whether it hits a fundamental wall on dense instances. -/

end RotationCalculus
