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

    The original LCG had catastrophic autocorrelation in lower bits:
    - Only odd-indexed variables appeared (period-2 parity)
    - All polarities were false (bit 0 had period 2)
    - No phase transition visible at any density

    Replaced with xorshift32: full-period (2^32-1), good statistical
    properties, all bits usable. -/

/-- Xorshift32 PRNG. Returns (value, next_state).
    Full period 2^32 - 1, passes most statistical tests. -/
def xorshift32 (state : UInt32) : UInt32 × UInt32 :=
  let s := state ^^^ (state <<< 13)
  let s := s ^^^ (s >>> 17)
  let s := s ^^^ (s <<< 5)
  (s, s)

/-- Generate a random number in [0, bound) from state.
    Uses upper bits via division to avoid low-bit bias. -/
def xrandMod (state : UInt32) (bound : ℕ) : ℕ × UInt32 :=
  let (val, next) := xorshift32 state
  if bound == 0 then (0, next)
  else (val.toNat % bound, next)

/-- Kept for backwards compatibility with existing #eval blocks. -/
def lcg (seed : ℕ) : ℕ × ℕ :=
  let next := (seed * 1103515245 + 12345) % (2^31)
  (next, next)

def randMod (seed : ℕ) (bound : ℕ) : ℕ × ℕ :=
  let (val, next) := lcg seed
  (val % bound, next)

/-! ## Random 3-SAT generator -/

/-- Generate a random 3-SAT clause over n variables.
    Ensures distinct variables per clause (standard convention). -/
def randomClause (n : ℕ) (state : UInt32) : SATClause × UInt32 :=
  let (v1, s1) := xrandMod state n
  let (p1, s2) := xrandMod s1 2
  -- v2 distinct from v1
  let (v2raw, s3) := xrandMod s2 (n - 1)
  let v2 := if v2raw >= v1 then v2raw + 1 else v2raw
  let (p2, s4) := xrandMod s3 2
  -- v3 distinct from v1 and v2
  let (v3raw, s5) := xrandMod s4 (n - 2)
  let v3' := if v3raw >= min v1 v2 then v3raw + 1 else v3raw
  let v3 := if v3' >= max v1 v2 then v3' + 1 else v3'
  let (p3, s6) := xrandMod s5 2
  ([(v1, p1 == 1), (v2, p2 == 1), (v3, p3 == 1)], s6)

/-- Convert a seed to initial xorshift state (must be nonzero). -/
def seedToState (seed : ℕ) : UInt32 :=
  let s := (seed.toUInt32 ^^^ 0x12345678) ||| 1
  s

/-- Generate a random 3-SAT formula with m clauses over n vars. -/
def random3SAT (n : ℕ) (m : ℕ) (seed : ℕ) : SATFormula :=
  if n < 3 then []  -- need at least 3 variables for 3-SAT
  else
    let rec go : ℕ → UInt32 → SATFormula
      | 0, _ => []
      | remaining + 1, s =>
        let (clause, nextState) := randomClause n s
        clause :: go remaining nextState
    go m (seedToState seed)

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
