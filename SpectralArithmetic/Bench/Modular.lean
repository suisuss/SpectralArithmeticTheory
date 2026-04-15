/-
  Modular Formula Resolution-Proof Benchmark (issue #45)
  =======================================================

  Two sweeps:
    (1) modularFormula — dense clusters + bridges + forcing units.
        Known to be trivialised by UP; kept as a baseline /
        regression check.
    (2) modularTseitinFormula — Tseitin on a chain of K_n cliques.
        Structurally UNSAT by parity; no trivial UP escape.
        This is where we actually test the 2^Ω(k) hypothesis.

  Both write TSV to results/.

  Run:  lake exe modular-bench
-/

import SpectralArithmetic.Rotation.IndustrialInstances
import SpectralArithmetic.Rotation.WidthTrajectory
import SpectralArithmetic.Rotation.CrawlContract
import SpectralArithmetic.Rotation.TseitinModular

set_option linter.style.longLine false

open RotationCalculus

namespace SpectralArithmetic.Bench.Modular

/-- One row of bench output. -/
structure BenchRow where
  k          : Nat
  n          : Nat
  seed       : Nat
  vars       : Nat
  clauses    : Nat
  proofLen   : Nat
  proofDone  : Bool
  peakW      : Nat
  widthTraj  : List Nat
  ccRounds   : Nat
  ccProven   : Bool
  ccWidths   : List Nat
  ccLearned  : List Nat
  deriving Repr

private def listToString (xs : List Nat) : String :=
  String.intercalate "," (xs.map toString)

def header : String :=
  String.intercalate "\t"
    ["k", "n", "seed", "vars", "clauses",
     "proofLen", "proofDone", "peakW", "widthTraj",
     "ccRounds", "ccProven", "ccWidths", "ccLearned"]

def rowToTSV (r : BenchRow) : String :=
  String.intercalate "\t"
    [toString r.k, toString r.n, toString r.seed,
     toString r.vars, toString r.clauses,
     toString r.proofLen, toString r.proofDone, toString r.peakW,
     listToString r.widthTraj,
     toString r.ccRounds, toString r.ccProven,
     listToString r.ccWidths, listToString r.ccLearned]

def resolutionBudget : Nat := 5000
def ccBudget : Nat := 30

/-- Run the bench on one (k, n, seed) cell with a given generator. -/
def runWith (gen : Nat → Nat → Nat → SATFormula × Nat)
    (k n seed : Nat) : BenchRow :=
  let (formula, vars) := gen k n seed
  let clauses := formula.length
  let (deriv, _) := greedyResolution formula resolutionBudget
  let widths := widthTrajectory deriv
  let peak := peakWidth deriv
  let proofLen := deriv.steps.length
  let proofDone := deriv.conclusion.isEmpty
  let (logs, _, ccProven) := crawlContractSolve formula vars ccBudget
  let ccWidths := logs.map (·.avgWidth)
  let ccLearned := logs.map (·.learned)
  { k, n, seed, vars, clauses,
    proofLen, proofDone, peakW := peak, widthTraj := widths,
    ccRounds := logs.length, ccProven, ccWidths, ccLearned }

/-- Baseline generator wrapper: modularFormula with density 2n clauses
    per cluster and 2 bridges per adjacent-cluster pair. -/
def genModular (k n seed : Nat) : SATFormula × Nat :=
  modularFormula k n (n * 2) 2 seed

/-- Tseitin generator wrapper. -/
def genTseitin (k n seed : Nat) : SATFormula × Nat :=
  modularTseitinFormula k n seed

end SpectralArithmetic.Bench.Modular

open SpectralArithmetic.Bench.Modular in
def runSweep (label : String) (outFile : String)
    (gen : Nat → Nat → Nat → SATFormula × Nat)
    (ks ns seeds : List Nat) : IO Unit := do
  let total := ks.length * ns.length * seeds.length
  IO.println ""
  IO.println s!"=== {label} ==="
  IO.println s!"  sweep: k∈{ks}  n∈{ns}  seeds∈{seeds}  ({total} cells)"
  IO.println s!"  budgets: greedy={resolutionBudget}  cc={ccBudget}"
  let outDir : System.FilePath := "results"
  IO.FS.createDirAll outDir
  let outPath := outDir / outFile
  let mut lines : Array String := #[header]
  let mut idx := 0
  for k in ks do
    for n in ns do
      for s in seeds do
        idx := idx + 1
        IO.print s!"  [{idx}/{total}] k={k} n={n} seed={s} ... "
        (← IO.getStdout).flush
        let row := runWith gen k n s
        IO.println s!"vars={row.vars} cl={row.clauses} len={row.proofLen} peak={row.peakW} done={row.proofDone} cc={row.ccRounds}/{row.ccProven}"
        lines := lines.push (rowToTSV row)
  IO.FS.writeFile outPath (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"  wrote {outPath} ({lines.size - 1} rows)"

open SpectralArithmetic.Bench.Modular in
def main : IO Unit := do
  runSweep "BASELINE: modularFormula (forcing-clause UNSAT, expected trivialised)"
           "modular_bench.tsv"
           genModular
           [2, 3, 4, 5] [3, 4, 5] [42, 137, 314]
  runSweep "TSEITIN: modularTseitinFormula (structural UNSAT via parity)"
           "modular_tseitin_bench.tsv"
           genTseitin
           [2, 3, 4, 5, 6] [3, 4, 5] [42, 137, 314]
