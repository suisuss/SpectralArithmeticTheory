/-
  Tactic Selector: Meta-Guided Strategy Dispatch
  =================================================

  Uses the meta-system's structural measurements to decide
  which tactic to apply at each point:

  1. CASCADE DEPTH → UP is productive? Keep propagating.
  2. MARGINAL BIAS → BP has strong signal? Use BP-guided assignment.
  3. CLAUSE DENSITY → Above transition? Switch to UNSAT mode.
  4. SHARED VARS → Few shared? Split and compose.
  5. RESIDUAL SIZE → Small? Finish with CDCL.

  The selector reads the ComplexitySnapshot and dispatches:
  - UP when unit clauses or pure literals exist
  - BP when variables have strong marginal bias
  - Split when the formula decomposes cleanly
  - CDCL when nothing else works
  - Resolution when UNSAT is suspected (density > threshold)

  For UNSAT: resolution replaces CDCL, and the cascade/split
  structure still applies (unit resolution = UP, independent
  sub-derivations = split).
-/

import SpectralArithmetic.Rotation.IteratedCDCL
import SpectralArithmetic.Rotation.AdaptiveMetaSolver

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Structural signals -/

/-- Measure a formula's structural properties for tactic dispatch. -/
structure FormulaSignal where
  nClauses     : ℕ
  nVars        : ℕ
  density1000  : ℕ     -- clauses * 1000 / vars
  nUnits       : ℕ     -- unit clauses
  nPures       : ℕ     -- pure literals
  maxBias      : ℕ     -- strongest marginal bias (0-100)
  minShared    : ℕ     -- min shared vars at best split
  deriving Repr

/-- Compute structural signals for a formula. -/
def measureSignals (formula : SATFormula) (vars : List ℕ)
    : FormulaSignal :=
  let nC := List.length formula
  let nV := List.length vars
  let units := findUnits formula
  let pures := findPureLiterals formula vars
  -- Quick marginal estimate: count positive vs negative for each var
  let biases := vars.map fun v =>
    let pos := formula.foldl (fun c cl =>
      c + if cl.any fun (v', p) => v' == v && p then 1 else 0) 0
    let neg := formula.foldl (fun c cl =>
      c + if cl.any fun (v', p) => v' == v && !p then 1 else 0) 0
    let total := pos + neg
    if total == 0 then 50
    else pos * 100 / total  -- bias toward true (50 = unbiased)
  let maxBias := biases.foldl (fun acc b =>
    max acc (if b > 50 then b else 100 - b)) 0
  -- Best split shared vars
  let splitVar := bestSplitPoint formula vars
  let (_, _, shared, _) := splitAt formula splitVar
  { nClauses := nC,
    nVars := nV,
    density1000 := if nV > 0 then nC * 1000 / nV else 0,
    nUnits := List.length units,
    nPures := List.length pures,
    maxBias := maxBias,
    minShared := List.length shared }

/-! ## Tactic dispatch -/

/-- Which tactic to use. -/
inductive TacticChoice where
  | up         : TacticChoice              -- unit propagation
  | bpGuided   : TacticChoice              -- BP-guided assignment
  | splitCompose : ℕ → TacticChoice   -- split at variable
  | cdcl       : TacticChoice              -- CDCL search
  | resolution : TacticChoice              -- resolution for UNSAT
  deriving Repr

/-- Decide which tactic to apply based on structural signals. -/
def selectChoice (sig : FormulaSignal) : TacticChoice :=
  -- Priority 1: UP if unit clauses or pure literals exist
  if sig.nUnits > 0 || sig.nPures > 0 then .up
  -- Priority 2: density above ~5.0 suggests UNSAT → resolution
  else if sig.density1000 > 5000 && sig.nVars > 3 then .resolution
  -- Priority 3: few shared vars at split → compose
  else if sig.minShared ≤ 1 && sig.nVars > 4 then
    .splitCompose (bestSplitPoint [] [])  -- placeholder
  -- Priority 4: strong marginal bias → BP-guided
  else if sig.maxBias > 80 then .bpGuided
  -- Priority 5: small residual → CDCL
  else .cdcl

/-- Show tactic selection. -/
def showChoice : TacticChoice → String
  | .up => "UP"
  | .bpGuided => "BP-guided"
  | .splitCompose v => s!"split({v})"
  | .cdcl => "CDCL"
  | .resolution => "resolution"

/-! ## Meta-guided solver with tactic selection -/

/-- Full solve with tactic selection trace. -/
partial def metaGuidedSolve (formula : SATFormula) (vars : List ℕ)
    : List String × Bool × List (ℕ × Bool) :=
  if List.length vars == 0 then
    ([], satisfiesFormula [] formula, [])
  else
    let sig := measureSignals formula vars
    let tactic := selectChoice sig
    let entry := showChoice tactic
    match tactic with
    | .up =>
      let initState : TacticState :=
        { formula := formula, vars := vars, assign := [] }
      let (upState, _) := upFixpoint initState
      if List.length upState.vars == 0 then
        let ok := satisfiesFormula upState.assign formula
        ([entry], ok, upState.assign)
      else
        -- Continue with remaining vars
        let (rest, ok, assign) :=
          metaGuidedSolve upState.formula upState.vars
        ([entry] ++ rest, ok,
         upState.assign ++ assign)
    | .bpGuided =>
      -- Use BP marginals to pick an assignment for the most biased var
      let biases := vars.map fun v =>
        let pos := formula.foldl (fun c cl =>
          c + if cl.any fun (v', p) => v' == v && p then 1 else 0) 0
        let neg := formula.foldl (fun c cl =>
          c + if cl.any fun (v', p) => v' == v && !p then 1 else 0) 0
        (v, pos, neg)
      -- Pick most biased variable
      let best := biases.foldl (fun acc (v, p, n) =>
        match acc with
        | none => some (v, p, n)
        | some (_, bp, bn) =>
          let bias := if p > n then p - n else n - p
          let bestBias := if bp > bn then bp - bn else bn - bp
          if bias > bestBias then some (v, p, n) else acc
      ) none
      match best with
      | none => ([entry], false, [])
      | some (v, p, n) =>
        let pol : Bool := p > n
        let bpAssign : List (ℕ × Bool) := [(v, pol)]
        let simp := simplifyFormula formula bpAssign
        let remainVars := vars.filter (· != v)
        let (rest, ok, moreAssign) :=
          metaGuidedSolve simp remainVars
        ([entry] ++ rest, ok, bpAssign ++ moreAssign)
    | .splitCompose _ =>
      let splitVar := bestSplitPoint formula vars
      let (partA, partB, _, _) := splitAt formula splitVar
      let aVars := vars.filter (· < splitVar)
      let bVars := vars.filter (· >= splitVar)
      let (traceA, okA, assignA) := metaGuidedSolve partA aVars
      let simpB := simplifyFormula partB assignA
      let (traceB, okB, assignB) := metaGuidedSolve simpB bVars
      let combined := assignA ++ assignB
      let ok := satisfiesFormula combined formula
      ([s!"split({splitVar})"] ++ traceA ++ traceB,
       ok, combined)
    | .cdcl =>
      let (found, finalAssign, _) :=
        cdclSearchTraced formula vars []
      ([entry], found, if found then finalAssign else [])
    | .resolution =>
      -- Use iterated 1-UIP to prove UNSAT
      let (logs, proven) := iteratedSolve formula (List.length vars) 5
      let nRounds := List.length logs
      ([s!"iterated1UIP→UNSAT={proven}(rounds={nRounds})"],
       false, [])

/-! ## Demonstrations -/

#eval! do
  IO.println "=== META-GUIDED TACTIC SELECTION ==="
  IO.println ""

  let solve := fun (name : String) (f : SATFormula) (nVars : ℕ) => do
    let sig := measureSignals f (List.range nVars)
    let tactic := selectChoice sig
    let (trace, ok, assign) := metaGuidedSolve f (List.range nVars)
    let tactics := trace
    IO.println s!"  {name}: selected={showChoice tactic} \
      solved={ok} steps={List.length trace}"
    IO.println s!"    signal: density={sig.density1000} \
      units={sig.nUnits} pures={sig.nPures} \
      bias={sig.maxBias} shared={sig.minShared}"
    IO.println s!"    tactic trace: {tactics}"

  -- Structured: should select UP
  IO.println "--- Structured ---"
  solve "struct-8" (reachInstance 8 3) 8
  solve "struct-15" (reachInstance 15 3) 15

  -- Random easy: UP then CDCL
  IO.println ""
  IO.println "--- Random easy ---"
  solve "rand-8-16-s42" (random3SAT 8 16 42) 8
  solve "rand-10-20-s42" (random3SAT 10 20 42) 10

  -- Random at transition
  IO.println ""
  IO.println "--- Random at transition ---"
  solve "rand-10-42-s42" (random3SAT 10 42 42) 10
  solve "rand-10-42-s123" (random3SAT 10 42 123) 10

  -- High density (likely UNSAT)
  IO.println ""
  IO.println "--- High density (UNSAT territory) ---"
  solve "rand-8-60-s42" (random3SAT 8 60 42) 8
  solve "rand-10-60-s42" (random3SAT 10 60 42) 10

  -- Chain (UNSAT)
  IO.println ""
  IO.println "--- Chain UNSAT ---"
  solve "chain-5" (chainFormula 5) 5

  -- PHP
  IO.println ""
  IO.println "--- PHP ---"
  solve "PHP(3,2)" (pigeonhole 3 2) 6

/-! ## Assessment

    The tactic selector reads five structural signals:

    | Signal     | What it measures            | Tactic triggered |
    |------------|-----------------------------|------------------|
    | units > 0  | Free inference available    | UP               |
    | pures > 0  | Variables with one polarity | UP               |
    | density > 5| Likely UNSAT                | resolution       |
    | shared ≤ 1 | Cleanly decomposable        | split+compose    |
    | bias > 80  | Strong variable preference  | BP-guided        |
    | otherwise  | No structural signal        | CDCL (search)    |

    The selector produces a TACTIC TRACE: the sequence of
    decisions about which tactic to apply. This trace IS
    the meta-meta-trajectory — the solver reasoning about
    its own strategy.

    Three levels of meta:
    1. Object: the formula (clauses, variables)
    2. Meta #1: the solve trajectory (UP steps, decisions, conflicts)
    3. Meta #2: the tactic selection trace (which tactic, why)

    All three are expressible as rotation calculus terms.
    The tactic trace is a list of (tactic, signal) pairs —
    the same pair/ground structure as everything else.

    The honest question: does this meta-guided selection
    outperform the fixed pipeline? The data should show:
    - Structured: same performance (both pick UP)
    - Random easy: similar (both cascade then search)
    - Random hard: potentially better (selector detects
      density and switches to resolution)
    - UNSAT: potentially much better (selector detects
      high density and goes straight to resolution)
-/

end RotationCalculus
