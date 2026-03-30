/-
  Phase Transition Study (#23)
  ==============================

  Sweep clause density through the SAT/UNSAT transition for
  random 3-SAT. Measure complexity fingerprints at each density.

  The phase transition for 3-SAT occurs at α ≈ 4.267 (clause/variable
  ratio). Below: almost certainly SAT. Above: almost certainly UNSAT.
  At the transition: hardest instances.

  Fingerprints measured:
  1. Satisfiability (SAT or UNSAT)
  2. Flat brute force cost
  3. CDCL cost + learned clauses
  4. BP success (found or not)
  5. ExtRes+UP cost + abstractions
  6. Free inference cascade depth (how many vars eliminated by UP)
-/

import SpectralArithmetic.Rotation.CompositionTheory

namespace RotationCalculus

open Term

/-! ## Phase transition sweep

    For n=8 variables, sweep clause count from 8 (ratio 1) to 56 (ratio 7).
    At each density, run all solvers and measure costs. -/

/-- Run all solvers on a formula, return a summary string. -/
def benchmarkAll (formula : SATFormula) (n : ℕ)
    : String :=
  let (rFlat, cFlat) := flatBruteForce formula n
  let (_, cCDCL, nLearned) := satCDCL formula n
  let (rBP, cBP, _) := runBP formula n 2
  let (rExt, cExt, nAbs) := satExtRes formula n 3
  -- Count free inference: how many vars does UP alone eliminate?
  let (_, forcedAssign, remainingVars, _) :=
    freeInference formula (List.range n) []
  let upEliminated := n - remainingVars.length
  let sat := if rFlat.isSome then "SAT" else "UNSAT"
  s!"{sat} flat={cFlat} cdcl={cCDCL}(L={nLearned}) bp={cBP}(f={rBP.isSome}) ext={cExt}(a={nAbs},f={rExt.isSome}) up_elim={upEliminated}/{n}"

/-! ## Sweep at n=8, single seed -/

#eval do
  let n := 8
  let seed := 42
  let data := [8, 12, 16, 20, 24, 28, 32, 36, 40, 48, 56].map fun m =>
    let f := random3SAT n m seed
    let ratio := m * 10 / n  -- 10x to show decimal
    let result := benchmarkAll f n
    s!"m={m} r={ratio/10}.{ratio%10} {result}"
  IO.println s!"Phase transition sweep n={n} seed={seed}:"
  IO.println (String.intercalate "\n" data)

/-! ## Sweep at n=8, multiple seeds (for statistics) -/

#eval do
  let n := 8
  let data := [16, 24, 32, 40, 48].map fun m =>
    let results := [42, 123, 456, 789, 1001].map fun seed =>
      let f := random3SAT n m seed
      let (rFlat, cFlat) := flatBruteForce f n
      let (_, cCDCL, _) := satCDCL f n
      let (rExt, cExt, _) := satExtRes f n 3
      (cFlat, cCDCL, cExt, rFlat.isSome, rExt.isSome)
    -- Average costs
    let avgFlat := results.foldl (fun a (f, _, _, _, _) => a + f) 0 / results.length
    let avgCDCL := results.foldl (fun a (_, c, _, _, _) => a + c) 0 / results.length
    let avgExt := results.foldl (fun a (_, _, e, _, _) => a + e) 0 / results.length
    let satCount := results.foldl (fun a (_, _, _, s, _) => if s then a + 1 else a) 0
    let extFound := results.foldl (fun a (_, _, _, _, e) => if e then a + 1 else a) 0
    s!"m={m} r={m/n} sat={satCount}/5 avgFlat={avgFlat} avgCDCL={avgCDCL} avgExt={avgExt} extFound={extFound}/5"
  IO.println s!"Phase transition statistics n=8 (5 seeds):"
  IO.println (String.intercalate "\n" data)

/-! ## Sweep at n=10, single seed -/

#eval do
  let n := 10
  let seed := 42
  let data := [10, 20, 30, 40, 50, 60].map fun m =>
    let f := random3SAT n m seed
    let result := benchmarkAll f n
    s!"m={m} r={m/n} {result}"
  IO.println s!"Phase transition sweep n={n} seed={seed}:"
  IO.println (String.intercalate "\n" data)

/-! ## UP cascade depth across the transition

    How many variables does unit propagation eliminate at each density?
    High elimination = structured (easy). Low = random (hard). -/

#eval do
  let n := 8
  let data := [8, 16, 24, 32, 40, 48, 56].map fun m =>
    let results := [42, 123, 456].map fun seed =>
      let f := random3SAT n m seed
      let (_, _, remainingVars, _) :=
        freeInference f (List.range n) []
      n - remainingVars.length
    let avgElim := results.foldl (· + ·) 0 / results.length
    s!"m={m} r={m/n} avg_UP_eliminated={avgElim}/{n}"
  IO.println s!"UP cascade depth n={n} (3 seeds):"
  IO.println (String.intercalate "\n" data)

/-! ## Assessment

    The phase transition sweep reveals:

    1. WHERE each solver fails. BP should fail above the transition
       (UNSAT instances). CDCL should work everywhere but get
       expensive at the transition. ExtRes+UP should show the cascade
       effect disappearing as density increases.

    2. The COST LANDSCAPE across densities. If the framework's
       fingerprints (flat cost, CDCL cost, UP elimination, ExtRes
       abstractions) show a clear peak at the transition, the
       framework empirically locates the phase transition.

    3. The UP ELIMINATION PROFILE. At low density, UP should
       eliminate many variables (under-constrained, many pure
       literals). At high density, UP should eliminate fewer
       (over-constrained, few pure literals). At the transition,
       the elimination drops sharply — variables become entangled.

    Caveat: our LCG-based "random" instances may not exhibit
    true phase transition behavior due to correlation in the
    pseudo-random number generator. A proper PRNG would be
    needed for rigorous empirical results. -/

end RotationCalculus
