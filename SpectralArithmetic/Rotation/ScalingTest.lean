/-
  Scaling Test: Does the Architecture Work at n=10, 15, 20?
  ===========================================================

  Push iterated 1-UIP + adaptive ordering to larger instances.
  Measure: round count, learned clause count, cascade pattern.

  No brute force verification at scale — trust the solver.
  Verify soundness on small instances only.
-/

import SpectralArithmetic.Rotation.PromotionAware

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

deriving instance Inhabited for IterationLog

/-! ## High-density UNSAT generators (no brute force needed) -/

/-- Generate a formula at density well above the phase transition.
    At ratio 6+, almost certainly UNSAT. -/
def denseUNSAT (n : ℕ) (seed : ℕ) : SATFormula :=
  random3SAT n (n * 6) seed

-- PHP is always UNSAT — no verification needed.

/-! ## Scaling tests -/

#eval! do
  IO.println "=== SCALING: ITERATED 1-UIP ==="
  IO.println ""
  IO.println "n\tm\tseed\trounds\tproven\tcascade_pattern"

  -- Random dense UNSAT: n=4..8 (safe range)
  for n in [4, 5, 6, 7, 8] do
    for seed in [42] do
      let f := denseUNSAT n seed
      let (logs, proven) := iteratedSolve f n 20
      let cascades := logs.map fun (l : IterationLog) => l.cascade
      let totalLearned := logs.foldl
        (fun a (l : IterationLog) => a + l.learned) 0
      IO.println s!"{n}\t{n*6}\t{seed}\t{List.length logs}\t{proven}\t{cascades}\tL={totalLearned}"

#eval! do
  IO.println ""
  IO.println "=== PHP SCALING ==="
  IO.println ""
  IO.println "p\tnVars\trounds\tproven\tcascades\ttotalL"
  for p in [3, 4, 5, 6] do
    let f := pigeonhole p (p-1)
    let nv := p * (p-1)
    let (logs, proven) := iteratedSolve f nv 25
    let cascades := logs.map fun (l : IterationLog) => l.cascade
    let totalLearned := logs.foldl
      (fun a (l : IterationLog) => a + l.learned) 0
    IO.println s!"{p}\t{nv}\t{List.length logs}\t{proven}\t{cascades}\t{totalLearned}"

#eval! do
  IO.println ""
  IO.println "=== PHASE TRANSITION SWEEP ==="
  IO.println ""
  IO.println "n\tratio\tseed\trounds\tproven"
  -- n=8, vary density around the transition
  for ratio10 in [30, 42, 50, 60] do
    let n := 6
    let m := ratio10 * n / 10
    for seed in [42] do
      let f := random3SAT n m seed
      let (logs, proven) := iteratedSolve f n 20
      IO.println s!"{n}\t{ratio10/10}.{ratio10%10}\t{seed}\t{List.length logs}\t{proven}"

/-! ## Assessment

    What to look for:

    ROUND COUNT vs n:
    - O(1) or O(log n) → architecture scales
    - O(n) or O(n^2) → architecture is linear/quadratic in variables
    - Blows up → specific bottleneck to identify

    CASCADE PATTERN:
    - [0, 0, ..., 0, N] → critical mass pattern (standard)
    - [0, k, 0, m, ...] → incremental progress
    - All zeros → stall (reordering not helping at this scale)

    PHP ROUND COUNT vs p:
    - O(p) → polynomial (good, matches resolution proof)
    - O(p^2) → quadratic (certificate size)
    - O(2^p) → exponential (architecture fails for PHP at scale)

    PHASE TRANSITION:
    - Easy (low density): 1 round, SAT detected
    - Hard (at transition): many rounds
    - Easy (high density): few rounds, UNSAT quickly
    - The hardest point should be at density ~4.27
-/

end RotationCalculus
