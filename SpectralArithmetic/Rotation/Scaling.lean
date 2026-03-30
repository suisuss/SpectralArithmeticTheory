/-
  Scaling: Flat vs Tree vs DAG across Treewidths
  ================================================

  Systematic comparison of three SAT solving strategies across
  instances with controlled treewidth and varying size.

  Treewidth is controlled by "clause reach" — each clause connects
  variables at most k positions apart. k=1 gives path (tw≈1),
  k=n gives clique (tw≈n).
-/

import SpectralArithmetic.Rotation.DAG

namespace RotationCalculus

open Term

/-! ## Parameterized instance generator

    Build SAT instances with controlled structure:
    - n variables
    - "reach" k: clauses connect x_i with x_j where |i-j| ≤ k
    - Forced solution: x_0 = false (to prevent all-true shortcut)
    - Implication chains: NOT x_i OR x_j for linked pairs
      These propagate: if x_i is true, x_j must be true.
      Combined with x_0 = false, this constrains the solution space. -/

/-- Build a SAT instance with n variables and clause reach k.
    - Clause 1: NOT x_0 (forces x_0 = false)
    - For each i, for each j in [i+1, min(i+k, n-1)]:
      clause (NOT x_i OR x_j): if x_i then x_j
    - Final: NOT x_{n-1} (forces last variable false too)
    This creates a constraint propagation network with reach k.
    Solution: all false (the only assignment satisfying both endpoints). -/
def reachInstance (n : ℕ) (reach : ℕ) : SATFormula :=
  let forcing := [[(0, false)], [(n - 1, false)]]
  let implications := (List.range n).flatMap fun i =>
    (List.range (min reach (n - 1 - i))).map fun j =>
      [(i, false), (i + j + 1, true)]  -- NOT x_i OR x_{i+j+1}
  forcing ++ implications

/-- Count the number of clauses (proxy for treewidth). -/
def clauseCount (formula : SATFormula) : ℕ := formula.length

-- Verify instance structure
#eval clauseCount (reachInstance 8 1)   -- 2 forcing + 7 implications
#eval clauseCount (reachInstance 8 2)   -- 2 + 13
#eval clauseCount (reachInstance 8 4)   -- 2 + 22
#eval clauseCount (reachInstance 8 7)   -- 2 + 28

-- Verify solution exists (all false should work)
#eval satisfiesFormula
  ((List.range 8).map fun v => (v, false))
  (reachInstance 8 1)

#eval satisfiesFormula
  ((List.range 8).map fun v => (v, false))
  (reachInstance 8 7)

/-! ## Fixed size (n=8), varying treewidth

    Each row: (reach, clauses, flat_cost, tree_cost, dag_cost) -/

#eval do  -- reach=1
  let f := reachInstance 8 1
  let (_, a) := flatBruteForce f 8
  let (_, b) := satTreeDecomp f 8
  let (_, c) := satDAGDecomp f 8
  IO.println s!"n=8 reach=1 cls={clauseCount f} flat={a} tree={b} dag={c}"

#eval do  -- reach=2
  let f := reachInstance 8 2
  let (_, a) := flatBruteForce f 8
  let (_, b) := satTreeDecomp f 8
  let (_, c) := satDAGDecomp f 8
  IO.println s!"n=8 reach=2 cls={clauseCount f} flat={a} tree={b} dag={c}"

#eval do  -- reach=3
  let f := reachInstance 8 3
  let (_, a) := flatBruteForce f 8
  let (_, b) := satTreeDecomp f 8
  let (_, c) := satDAGDecomp f 8
  IO.println s!"n=8 reach=3 cls={clauseCount f} flat={a} tree={b} dag={c}"

#eval do  -- reach=4
  let f := reachInstance 8 4
  let (_, a) := flatBruteForce f 8
  let (_, b) := satTreeDecomp f 8
  let (_, c) := satDAGDecomp f 8
  IO.println s!"n=8 reach=4 cls={clauseCount f} flat={a} tree={b} dag={c}"

#eval do  -- reach=5
  let f := reachInstance 8 5
  let (_, a) := flatBruteForce f 8
  let (_, b) := satTreeDecomp f 8
  let (_, c) := satDAGDecomp f 8
  IO.println s!"n=8 reach=5 cls={clauseCount f} flat={a} tree={b} dag={c}"

#eval do  -- reach=7 (full)
  let f := reachInstance 8 7
  let (_, a) := flatBruteForce f 8
  let (_, b) := satTreeDecomp f 8
  let (_, c) := satDAGDecomp f 8
  IO.println s!"n=8 reach=7 cls={clauseCount f} flat={a} tree={b} dag={c}"

/-! ## Fixed size (n=10), varying treewidth -/

#eval do
  let f := reachInstance 10 1
  let (_, a) := flatBruteForce f 10
  let (_, b) := satTreeDecomp f 10
  let (_, c) := satDAGDecomp f 10
  IO.println s!"n=10 reach=1 cls={clauseCount f} flat={a} tree={b} dag={c}"

#eval do
  let f := reachInstance 10 3
  let (_, a) := flatBruteForce f 10
  let (_, b) := satTreeDecomp f 10
  let (_, c) := satDAGDecomp f 10
  IO.println s!"n=10 reach=3 cls={clauseCount f} flat={a} tree={b} dag={c}"

#eval do
  let f := reachInstance 10 5
  let (_, a) := flatBruteForce f 10
  let (_, b) := satTreeDecomp f 10
  let (_, c) := satDAGDecomp f 10
  IO.println s!"n=10 reach=5 cls={clauseCount f} flat={a} tree={b} dag={c}"

#eval do
  let f := reachInstance 10 9
  let (_, a) := flatBruteForce f 10
  let (_, b) := satTreeDecomp f 10
  let (_, c) := satDAGDecomp f 10
  IO.println s!"n=10 reach=9 cls={clauseCount f} flat={a} tree={b} dag={c}"

/-! ## Fixed reach=1, varying size -/

#eval do
  let data := [4, 6, 8, 10, 12].map fun n =>
    let f := reachInstance n 1
    let (_, a) := flatBruteForce f n
    let (_, b) := satTreeDecomp f n
    let (_, c) := satDAGDecomp f n
    s!"reach=1 n={n} flat={a} tree={b} dag={c}"
  IO.println (String.intercalate "\n" data)

/-! ## Fixed reach=3, varying size -/

#eval do
  let data := [4, 6, 8, 10].map fun n =>
    let f := reachInstance n 3
    let (_, a) := flatBruteForce f n
    let (_, b) := satTreeDecomp f n
    let (_, c) := satDAGDecomp f n
    s!"reach=3 n={n} flat={a} tree={b} dag={c}"
  IO.println (String.intercalate "\n" data)

/-! ## Summary table

    Expected pattern:
    - Low reach (tw≈1): tree and DAG much cheaper than flat.
      DAG slightly cheaper than tree (shared boundary vars).
    - Medium reach (tw≈n/2): tree and DAG help less. Combination
      step grows with cross-partition clauses.
    - High reach (tw≈n): all three converge to similar cost.
      No factorization possible.

    The CROSSOVER POINT — where tree/DAG stop beating flat — is
    the empirical treewidth threshold for this instance family. -/

end RotationCalculus
