/-
  Transition Predictor: Can We Detect the Phase Jump Before It Happens?
  ======================================================================

  The crawl-contract trajectory shows a phase transition:
  contraction ratio jumps from ~100% to 1000% at a specific round.

  Question: is there a SIGNAL in rounds 1..k-1 that predicts
  the jump will happen at round k?

  Candidate signals:
  1. Width narrowing: avgWidth decreasing across rounds
  2. Learned clause count decreasing: fewer clauses needed
  3. Width slope: rate of change of avgWidth
  4. Cascade appearance: first round with ratio > 100%
-/

import SpectralArithmetic.Rotation.CrawlContract

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

deriving instance Inhabited for CCRound

/-- Extract per-round signals from crawl-contract logs. -/
structure RoundSignal where
  round     : ℕ
  learned   : ℕ
  avgWidth  : ℕ
  ratio     : ℕ
  isFinal   : Bool  -- did this round achieve complete contraction?
  deriving Repr

def extractSignals (logs : List CCRound) : List RoundSignal :=
  logs.map fun log =>
    { round := log.round,
      learned := log.learned,
      avgWidth := log.avgWidth,
      ratio := log.contrRatio,
      isFinal := log.contrRatio > 500 }

/-! ## Data collection -/

#eval! do
  IO.println "=== TRANSITION PREDICTION DATA ==="
  IO.println ""
  IO.println "round\tlearned\tavgW\tratio\tfinal?\tformula"

  -- PHP family
  for p in [3, 4, 5] do
    let f := pigeonhole p (p-1)
    let nv := p * (p-1)
    let (logs, _, _) := crawlContractSolve f nv 20
    let signals := extractSignals logs
    for s in signals do
      IO.println s!"{s.round}\t{s.learned}\t{s.avgWidth}\t{s.ratio}%\t{s.isFinal}\tPHP({p},{p-1})"

  -- Chain family
  for n in [3, 5, 8, 10] do
    let f := chainFormula n
    let (logs, _, _) := crawlContractSolve f n 20
    let signals := extractSignals logs
    for s in signals do
      IO.println s!"{s.round}\t{s.learned}\t{s.avgWidth}\t{s.ratio}%\t{s.isFinal}\tchain-{n}"

  -- Tseitin
  for n in [3, 5, 7] do
    let f := tseitinCycle n
    let (logs, _, _) := crawlContractSolve f n 20
    let signals := extractSignals logs
    for s in signals do
      IO.println s!"{s.round}\t{s.learned}\t{s.avgWidth}\t{s.ratio}%\t{s.isFinal}\ttseitin-{n}"

  -- Forced
  for n in [3, 5, 8] do
    let f := forcedContradiction n
    let (logs, _, _) := crawlContractSolve f n 20
    let signals := extractSignals logs
    for s in signals do
      IO.println s!"{s.round}\t{s.learned}\t{s.avgWidth}\t{s.ratio}%\t{s.isFinal}\tforced-{n}"

#eval! do
  IO.println ""
  IO.println "=== WIDTH NARROWING HYPOTHESIS ==="
  IO.println ""
  IO.println "Does avgWidth decrease monotonically before the transition?"
  IO.println "And does the transition always happen when avgWidth first ≤ 2?"
  IO.println ""

  -- For each multi-round proof, check the width trajectory
  IO.println "formula\t\twidth_trajectory\ttrans_at_width"
  for p in [3, 4, 5] do
    let f := pigeonhole p (p-1)
    let nv := p * (p-1)
    let (logs, _, _) := crawlContractSolve f nv 20
    let signals := extractSignals logs
    let widths := signals.map fun (s : RoundSignal) => s.avgWidth
    let transWidth := match signals.find? fun (s : RoundSignal) => s.isFinal with
      | some s => s.avgWidth
      | none => 0
    IO.println s!"PHP({p},{p-1})\t\t{widths}\t\t{transWidth}"

  for n in [3, 5, 7] do
    let f := tseitinCycle n
    let (logs, _, _) := crawlContractSolve f n 20
    let signals := extractSignals logs
    let widths := signals.map fun (s : RoundSignal) => s.avgWidth
    let transWidth := match signals.find? fun (s : RoundSignal) => s.isFinal with
      | some s => s.avgWidth
      | none => 0
    IO.println s!"tseitin-{n}\t{widths}\t\t{transWidth}"

#eval! do
  IO.println ""
  IO.println "=== LEARNED COUNT AS PREDICTOR ==="
  IO.println ""
  IO.println "Does the learned clause count decrease before transition?"
  IO.println ""
  IO.println "formula\t\tlearned_trajectory"
  for p in [3, 4, 5] do
    let f := pigeonhole p (p-1)
    let nv := p * (p-1)
    let (logs, _, _) := crawlContractSolve f nv 20
    let signals := extractSignals logs
    let counts := signals.map fun (s : RoundSignal) => s.learned
    IO.println s!"PHP({p},{p-1})\t\t{counts}"

#eval! do
  IO.println ""
  IO.println "=== RATIO TRAJECTORY ==="
  IO.println ""
  IO.println "Is there a partial contraction (ratio > 100%) before full (1000%)?"
  IO.println ""
  IO.println "formula\t\tratio_trajectory"
  for p in [3, 4, 5] do
    let f := pigeonhole p (p-1)
    let nv := p * (p-1)
    let (logs, _, _) := crawlContractSolve f nv 20
    let signals := extractSignals logs
    let ratios := signals.map fun (s : RoundSignal) => s.ratio
    IO.println s!"PHP({p},{p-1})\t\t{ratios}"
  for n in [3, 5, 7] do
    let f := tseitinCycle n
    let (logs, _, _) := crawlContractSolve f n 20
    let signals := extractSignals logs
    let ratios := signals.map fun (s : RoundSignal) => s.ratio
    IO.println s!"tseitin-{n}\t{ratios}"

/-! ## Assessment

    Prediction hypotheses:

    H1 (width narrowing): avgWidth decreases monotonically,
    and the transition happens when avgWidth first drops to ≤ 2.
    If true: monitor avgWidth, predict "1-2 more rounds" when
    width reaches 3.

    H2 (learned count peak): the number of learned clauses per
    round peaks early then decreases. The transition happens when
    learned count drops below a threshold.
    If true: the formula "saturates" — fewer new things to learn.

    H3 (partial contraction): a small contraction (ratio 105-120%)
    appears 1 round before the full contraction (1000%).
    If true: the partial cascade is the early warning signal.

    H4 (width × learned): the product avgWidth × learned
    decreases, and transition happens when it drops below
    a threshold.

    Which hypothesis works determines whether the transition
    is predictable, and therefore whether the crawl budget
    can be set optimally rather than adaptively.
-/

end RotationCalculus
