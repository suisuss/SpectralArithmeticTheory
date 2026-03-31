/-
  Chain Analysis: Do Random UNSAT Instances Have Single-Chain Proofs?
  ====================================================================

  Finding: all tested structured formulas (PHP, chain, Tseitin, forced)
  have optimal greedy proofs that are SINGLE CHAINS — one break (start),
  then every step uses the previous resolvent as clause1.

  Question: do RANDOM UNSAT instances also have single-chain proofs?
  If yes, chain finding is a general contraction strategy.
  If no, what's the minimum number of breaks (branches)?
-/

import SpectralArithmetic.Rotation.WidthGuidedSolver

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-- Analyze chain structure of a resolution derivation. -/
def analyzeChain (steps : List ResolutionStep)
    (original : SATFormula)
    : ℕ × ℕ × ℕ × List ℕ :=  -- (breaks, maxChain, origUsed, visitOrder)
  let rec go (remaining : List ResolutionStep)
      (prev : Option SATClause)
      (breaks chainLen maxChain origUsed : ℕ)
      (order : List ℕ)
      : ℕ × ℕ × ℕ × List ℕ :=
    match remaining with
    | [] => (breaks, maxChain, origUsed, order)
    | step :: rest =>
      let usedPrev := match prev with
        | some pr => step.clause1 == pr || step.clause2 == pr
        | none => false
      let newBreaks := if usedPrev then breaks else breaks + 1
      let newChainLen := if usedPrev then chainLen + 1 else 0
      let newMaxChain := max maxChain newChainLen
      let partner := match prev with
        | some pr =>
          if step.clause1 == pr then step.clause2 else step.clause1
        | none => step.clause2
      let idx := match original.findIdx? (· == partner) with
        | some i => i | none => List.length original
      let newOrigUsed := if idx < List.length original
        then origUsed + 1 else origUsed
      go rest (some step.result) newBreaks newChainLen
        newMaxChain newOrigUsed (order ++ [idx])
  go steps none 0 0 0 0 []

/-! ## Tests on small random UNSAT -/

-- n=4 is small enough that greedy resolution should always terminate
#eval! do
  IO.println "=== RANDOM UNSAT CHAIN STRUCTURE ==="
  IO.println ""
  IO.println "--- n=4, m=20 (high density, likely UNSAT) ---"
  IO.println "seed\tsteps\tbreaks\tchain%\torig\tclauses"
  let mut unsatCount := 0
  let mut totalBreaks := 0
  let mut totalSteps := 0
  for seed in [42, 123, 456, 789, 1001, 2024, 3141, 4242, 5555, 6789] do
    let f := random3SAT 4 20 seed
    let (sat, _) := flatBruteForce f 4
    if sat.isNone then
      let (gd, _) := greedyResolution f 2000
      if gd.conclusion.isEmpty then
        let (breaks, maxChain, origUsed, _) :=
          analyzeChain gd.steps f
        let n := List.length gd.steps
        let pct := if n > 0 then (n - breaks) * 100 / n else 0
        IO.println s!"{seed}\t{n}\t{breaks}\t{pct}%\t{origUsed}/{List.length f}"
        unsatCount := unsatCount + 1
        totalBreaks := totalBreaks + breaks
        totalSteps := totalSteps + n
      else
        IO.println s!"{seed}\t{List.length gd.steps}\tfail\t-\t-"
    else
      IO.println s!"{seed}\tSAT\t-\t-\t-"
  if unsatCount > 0 then
    IO.println s!"\navg: {totalSteps/unsatCount} steps, \
      {totalBreaks/unsatCount} breaks"

#eval! do
  IO.println ""
  IO.println "--- n=5, m=25 ---"
  IO.println "seed\tsteps\tbreaks\tchain%\torig\tclauses"
  for seed in [42, 123, 456, 789, 1001] do
    let f := random3SAT 5 25 seed
    let (sat, _) := flatBruteForce f 5
    if sat.isNone then
      let (gd, _) := greedyResolution f 5000
      if gd.conclusion.isEmpty then
        let (breaks, _, origUsed, _) := analyzeChain gd.steps f
        let n := List.length gd.steps
        let pct := if n > 0 then (n - breaks) * 100 / n else 0
        IO.println s!"{seed}\t{n}\t{breaks}\t{pct}%\t{origUsed}/{List.length f}"
      else
        IO.println s!"{seed}\t>{List.length gd.steps}\t-\t-\t-"
    else
      IO.println s!"{seed}\tSAT\t-\t-\t-"

-- Comparison: structured families always have 1 break
#eval! do
  IO.println ""
  IO.println "--- Structured: always 1 break ---"
  IO.println "formula\t\tsteps\tbreaks\tchain%\torig"
  for p in [3, 4, 5, 6, 7] do
    let f := pigeonhole p (p-1)
    let (gd, _) := greedyResolution f 5000
    if gd.conclusion.isEmpty then
      let (breaks, _, origUsed, _) := analyzeChain gd.steps f
      let n := List.length gd.steps
      IO.println s!"PHP({p},{p-1})\t\t{n}\t{breaks}\t{(n-breaks)*100/n}%\t{origUsed}/{List.length f}"
  for n in [5, 8, 10] do
    let f := chainFormula n
    let (gd, _) := greedyResolution f 500
    if gd.conclusion.isEmpty then
      let (breaks, _, origUsed, _) := analyzeChain gd.steps f
      let s := List.length gd.steps
      IO.println s!"chain-{n}\t\t{s}\t{breaks}\t{(s-breaks)*100/s}%\t{origUsed}/{List.length f}"

/-! ## Assessment

    If random UNSAT has multi-break chains:
    The proof BRANCHES — it derives intermediate lemmas from
    different parts of the formula, then combines them. This
    is NOT a single rotation pass. It requires the resolver to
    RESTART the chain at new entry points.

    Each break is a point where the resolver abandons the current
    chain and starts a new one from original clauses. The number
    of breaks = the number of independent sub-derivations that
    must be composed.

    Connection to the composition story:
    - 1 break = pure single chain (rotation pass)
    - k breaks = k sub-chains composed via shared resolvents
    - The breaks correspond to the INTERPOLATION points —
      each sub-chain produces a lemma that the next chain needs

    For general NP contraction:
    - If breaks are O(1) or O(log n): the proof nearly a chain,
      composition overhead is small
    - If breaks are O(n) or O(m): the proof is heavily branched,
      no single-chain structure, composition is the bottleneck
-/

end RotationCalculus
