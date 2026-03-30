/-
  Random 3-SAT: Testing SmartDAG on Hard Instances
  ==================================================

  The reachInstance formula has specific structure (implication chains)
  that the smart split exploits. To test generality, we need instances
  with less predictable structure.

  Random 3-SAT: m clauses, each with 3 random literals over n variables.
  Phase transition at m/n ≈ 4.27 — where instances are hardest.

  The test: does SmartDAG(k=2) maintain its linear scaling advantage
  on structurally random instances, or does it degrade?
-/

import SpectralArithmetic.Rotation.DAGBounded

namespace RotationCalculus

open Term

/-! ## Deterministic pseudo-random generator

    Simple LCG for reproducible "random" instances. -/

/-- Linear congruential generator. Returns (value, next_seed). -/
def lcg (seed : ℕ) : ℕ × ℕ :=
  let next := (seed * 1103515245 + 12345) % (2^31)
  (next, next)

/-- Generate a random number in [0, bound) from seed. -/
def randMod (seed : ℕ) (bound : ℕ) : ℕ × ℕ :=
  let (val, next) := lcg seed
  (val % bound, next)

/-! ## Random 3-SAT generator -/

/-- Generate a random 3-SAT clause over n variables. -/
def randomClause (n : ℕ) (seed : ℕ) : SATClause × ℕ :=
  let (v1, s1) := randMod seed n
  let (p1, s2) := randMod s1 2
  let (v2, s3) := randMod s2 n
  let (p2, s4) := randMod s3 2
  let (v3, s5) := randMod s4 n
  let (p3, s6) := randMod s5 2
  ([(v1, p1 == 1), (v2, p2 == 1), (v3, p3 == 1)], s6)

/-- Generate a random 3-SAT formula with m clauses over n variables. -/
def random3SAT (n : ℕ) (m : ℕ) (seed : ℕ) : SATFormula :=
  let rec go : ℕ → ℕ → SATFormula
    | 0, _ => []
    | remaining + 1, s =>
      let (clause, nextSeed) := randomClause n s
      clause :: go remaining nextSeed
  go m seed

-- Check a sample formula
#eval random3SAT 6 10 42

/-! ## Test suite: multiple random instances

    For each (n, m/n ratio), generate several instances with
    different seeds and measure flat vs SmartDAG costs. -/

/-- Run flat and SmartDAG on a formula, return costs and whether found. -/
def benchmark (formula : SATFormula) (n : ℕ)
    : (ℕ × Bool) × (ℕ × Bool) :=
  let (r1, c1) := flatBruteForce formula n
  let (r2, c2) := satSmartDAG formula n 2
  ((c1, r1.isSome), (c2, r2.isSome))

/-! ## Under-constrained (m/n = 2, easy, almost always SAT) -/

#eval do
  let n := 8
  let m := 16  -- ratio 2
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let ((fc, ff), (sc, sf)) := benchmark f n
    s!"seed={seed} flat={fc}(found={ff}) smart={sc}(found={sf})"
  IO.println s!"n={n} m={m} ratio={m/n} (under-constrained)"
  IO.println (String.intercalate "\n" data)

/-! ## Near phase transition (m/n ≈ 4, hard) -/

#eval do
  let n := 8
  let m := 32  -- ratio 4
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let ((fc, ff), (sc, sf)) := benchmark f n
    s!"seed={seed} flat={fc}(found={ff}) smart={sc}(found={sf})"
  IO.println s!"n={n} m={m} ratio={m/n} (near phase transition)"
  IO.println (String.intercalate "\n" data)

/-! ## Over-constrained (m/n = 6, likely UNSAT) -/

#eval do
  let n := 8
  let m := 48  -- ratio 6
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let ((fc, ff), (sc, sf)) := benchmark f n
    s!"seed={seed} flat={fc}(found={ff}) smart={sc}(found={sf})"
  IO.println s!"n={n} m={m} ratio={m/n} (over-constrained)"
  IO.println (String.intercalate "\n" data)

/-! ## Scaling: n=10 near phase transition -/

#eval do
  let n := 10
  let m := 42  -- ratio ~4.2
  let data := [42, 123, 456, 789, 1001].map fun seed =>
    let f := random3SAT n m seed
    let ((fc, ff), (sc, sf)) := benchmark f n
    s!"seed={seed} flat={fc}(found={ff}) smart={sc}(found={sf})"
  IO.println s!"n={n} m={m} ratio=4.2 (phase transition)"
  IO.println (String.intercalate "\n" data)

/-! ## Scaling comparison: fixed ratio=4, varying n -/

#eval do
  let data := [6, 8, 10, 12].map fun n =>
    let m := 4 * n
    let f := random3SAT n m 42
    let ((fc, ff), (sc, sf)) := benchmark f n
    s!"n={n} m={m} flat={fc}(found={ff}) smart={sc}(found={sf})"
  IO.println s!"ratio=4, seed=42, varying n:"
  IO.println (String.intercalate "\n" data)

/-! ## Multiple seeds at n=12 ratio=4 -/

#eval do
  let n := 12
  let m := 48
  let data := [42, 100, 200, 300, 400].map fun seed =>
    let f := random3SAT n m seed
    let ((fc, ff), (sc, sf)) := benchmark f n
    s!"seed={seed} flat={fc}(found={ff}) smart={sc}(found={sf})"
  IO.println s!"n={n} m={m} ratio=4:"
  IO.println (String.intercalate "\n" data)

/-! ## Assessment

    If SmartDAG generalizes:
    - Linear cost growth with n regardless of instance structure
    - Consistent speedup over flat across different seeds
    - Works on both SAT and UNSAT instances

    If SmartDAG does NOT generalize:
    - Cost degrades on random instances (approaches flat)
    - The smart split can't find good decompositions for random structure
    - The reachInstance results were an artifact of structured formulas

    Either result is informative. If SmartDAG fails on random instances,
    it tells us that the smart split exploits SPECIFIC structure
    (implication chains) rather than GENERAL structure. The question
    then becomes: what structural properties must an instance have
    for the smart split to work? -/

end RotationCalculus
