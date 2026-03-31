/-
  Proof System Test: Strategy Independence and Optimality
  ========================================================

  Is the greedy proof optimal? Is the proof length a property
  of the FORMULA or of the STRATEGY?

  Method: try multiple resolution strategies for each formula.
  If all produce the same length → strategy-independent.
  If lengths vary → strategy matters.
-/

import SpectralArithmetic.Rotation.IteratedCDCL

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-- Resolution with randomized clause pair selection. -/
def randomResolution (formula : SATFormula) (maxSteps : ℕ)
    (seed : ℕ) : Derivation :=
  let cls := formula.toArray
  let rec go (cls : Array SATClause) (steps : Array ResolutionStep)
      (fuel : ℕ) (state : UInt32)
      : Array ResolutionStep × Bool :=
    match fuel with
    | 0 => (steps, false)
    | fuel + 1 =>
      if cls.any (·.isEmpty) then (steps, true)
      else
        let allPossible := Id.run do
          let mut pairs : Array (ℕ × ℕ × ℕ) := #[]
          for i in [:cls.size] do
            for j in [:cls.size] do
              if i < j then
                match findResolvable cls[i]! cls[j]! with
                | some v => pairs := pairs.push (i, j, v)
                | none => pure ()
          return pairs
        if allPossible.size == 0 then (steps, false)
        else
          let (rval, nextState) := xorshift32 state
          let idx := rval.toNat % allPossible.size
          let (i, j, v) := allPossible[idx]!
          let c1 := cls[i]!
          let c2 := cls[j]!
          let resolvent := resolveOn c1 c2 v
          if cls.any (· == resolvent) then
            go cls steps fuel nextState
          else
            let step : ResolutionStep :=
              { clause1 := c1, clause2 := c2,
                pivot := v, result := resolvent }
            go (cls.push resolvent) (steps.push step) fuel nextState
  let (steps, found) := go cls #[] maxSteps (seedToState seed)
  { steps := steps.toList,
    conclusion := if found then [] else [(999, true)] }

/-- Width-minimizing resolution: pick shortest resolvent. -/
def widthMinResolution (formula : SATFormula) (maxSteps : ℕ)
    : Derivation :=
  let cls := formula.toArray
  let rec go (cls : Array SATClause) (steps : Array ResolutionStep)
      (fuel : ℕ) : Array ResolutionStep × Bool :=
    match fuel with
    | 0 => (steps, false)
    | fuel + 1 =>
      if cls.any (·.isEmpty) then (steps, true)
      else
        let best := Id.run do
          let mut b : Option (ℕ × ℕ × ℕ × SATClause × ℕ) := none
          for i in [:cls.size] do
            for j in [:cls.size] do
              if i < j then
                match findResolvable cls[i]! cls[j]! with
                | some v =>
                  let resolvent := resolveOn cls[i]! cls[j]! v
                  if !cls.any (· == resolvent) then
                    let w := List.length resolvent
                    match b with
                    | none => b := some (i, j, v, resolvent, w)
                    | some (_, _, _, _, bw) =>
                      if w < bw then
                        b := some (i, j, v, resolvent, w)
                | none => pure ()
          return b
        match best with
        | none => (steps, false)
        | some (i, j, v, resolvent, _) =>
          let step : ResolutionStep :=
            { clause1 := cls[i]!, clause2 := cls[j]!,
              pivot := v, result := resolvent }
          go (cls.push resolvent) (steps.push step) fuel
  let (steps, found) := go cls #[] maxSteps
  { steps := steps.toList,
    conclusion := if found then [] else [(999, true)] }

/-! ## Tests -/

#eval! do
  IO.println "=== STRATEGY INDEPENDENCE ==="
  IO.println ""
  IO.println "formula\t\tgreedy\twidthMin\trandom(3seeds)"

  let test := fun (name : String) (f : SATFormula) (fuel : ℕ) => do
    let (greedy, _) := greedyResolution f fuel
    let gL := if greedy.conclusion.isEmpty
      then s!"{List.length greedy.steps}" else "fail"
    let wmin := widthMinResolution f fuel
    let wL := if wmin.conclusion.isEmpty
      then s!"{List.length wmin.steps}" else "fail"
    let r1 := randomResolution f fuel 1
    let r2 := randomResolution f fuel 2
    let r3 := randomResolution f fuel 3
    let showD := fun (d : Derivation) =>
      if d.conclusion.isEmpty then s!"{List.length d.steps}"
      else "fail"
    let rs := s!"{showD r1},{showD r2},{showD r3}"
    IO.println s!"  {name}\t\t{gL}\t{wL}\t\t{rs}"

  test "PHP(3,2)" (pigeonhole 3 2) 200
  test "PHP(4,3)" (pigeonhole 4 3) 200
  test "chain-3" (chainFormula 3) 50
  test "chain-5" (chainFormula 5) 50
  test "tseitin-3" (tseitinCycle 3) 50
  test "tseitin-5" (tseitinCycle 5) 50
  test "forced-3" (forcedContradiction 3) 50
  test "forced-5" (forcedContradiction 5) 50

/-! ## Assessment

    If greedy = widthMin = all random seeds for a formula,
    the proof length is strategy-independent: it's a property
    of the formula, not the resolver.

    If they differ, the minimum is the formula's resolution
    complexity, and the gap measures how much strategy matters.
-/

end RotationCalculus
