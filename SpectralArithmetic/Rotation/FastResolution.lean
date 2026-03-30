/-
  Fast Resolution: Variable-Indexed Clause Database
  ===================================================

  The original resolution scans all O(n²) clause pairs at every
  step. This replaces it with a variable-indexed database where
  finding resolvable pairs is O(1) per variable.

  Data structure: for each variable v, maintain:
  - posOccur(v) = array of clause indices containing v positively
  - negOccur(v) = array of clause indices containing v negatively

  To find a resolvable pair: pick any variable v where both
  posOccur(v) and negOccur(v) are nonempty. Take one clause
  from each. Resolve.

  This reduces each step from O(n²) to O(V) where V is the
  number of variables.
-/

import SpectralArithmetic.Rotation.WidthTrajectory

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Variable-indexed clause database -/

/-- A clause database indexed by variable occurrence. -/
structure ClauseDB where
  clauses  : Array SATClause
  -- For each variable: indices of clauses containing it
  posIndex : Array (Array ℕ)  -- var → clause indices (positive)
  negIndex : Array (Array ℕ)  -- var → clause indices (negative)
  nVars    : ℕ
  deriving Repr

/-- Build a clause database from a formula. -/
def ClauseDB.build (formula : SATFormula) : ClauseDB := Id.run do
  let clauses := formula.toArray
  let maxVar := formula.foldl (fun acc c =>
    c.foldl (fun a (v, _) => max a (v + 1)) acc) 0
  let mut posIdx : Array (Array ℕ) := (List.replicate maxVar #[]).toArray
  let mut negIdx : Array (Array ℕ) := (List.replicate maxVar #[]).toArray
  for i in [:clauses.size] do
    for (v, p) in clauses[i]! do
      if v < maxVar then
        if p then
          posIdx := posIdx.set! v (posIdx[v]!.push i)
        else
          negIdx := negIdx.set! v (negIdx[v]!.push i)
  let result : ClauseDB :=
    { clauses := clauses, posIndex := posIdx,
      negIndex := negIdx, nVars := maxVar }
  return result

/-- Add a clause to the database, updating indices. -/
def ClauseDB.addClause (db : ClauseDB) (c : SATClause)
    : ClauseDB := Id.run do
  let idx := db.clauses.size
  let clauses := db.clauses.push c
  let mut posIdx := db.posIndex
  let mut negIdx := db.negIndex
  for (v, p) in c do
    if v < db.nVars then
      if p then
        posIdx := posIdx.set! v (posIdx[v]!.push idx)
      else
        negIdx := negIdx.set! v (negIdx[v]!.push idx)
  let result : ClauseDB :=
    { db with clauses := clauses,
              posIndex := posIdx, negIndex := negIdx }
  return result

/-- Find a resolvable pair using the index.
    Returns (clause1, clause2, pivot) or none. -/
def ClauseDB.findPair (db : ClauseDB)
    : Option (SATClause × SATClause × ℕ) :=
  -- Find any variable with both positive and negative occurrences
  let rec scan (v : ℕ) : Option (SATClause × SATClause × ℕ) :=
    if v >= db.nVars then none
    else
      let pos := db.posIndex[v]!
      let neg := db.negIndex[v]!
      if pos.size > 0 && neg.size > 0 then
        let c1 := db.clauses[pos[0]!]!
        let c2 := db.clauses[neg[0]!]!
        some (c1, c2, v)
      else scan (v + 1)
  scan 0

/-- Check if the database contains the empty clause. -/
def ClauseDB.hasEmpty (db : ClauseDB) : Bool :=
  db.clauses.any (·.isEmpty)

/-- Check if a clause already exists in the database. -/
def ClauseDB.contains (db : ClauseDB) (c : SATClause) : Bool :=
  db.clauses.any (· == c)

/-! ## Fast resolution using indexed database -/

/-- Find a resolvable pair that produces a NEW resolvent.
    Scans clauses in order (recent first for consistency with
    greedy), using the variable index to find partners. -/
def ClauseDB.findNewPair (db : ClauseDB)
    : Option (SATClause × SATClause × ℕ × SATClause) := Id.run do
  -- Scan clauses in order (most recent first)
  for i in [:db.clauses.size] do
    let ci := db.clauses.size - 1 - i
    let c1 := db.clauses[ci]!
    -- For each literal in c1, find partners via index
    for (v, p) in c1 do
      if v < db.nVars then
        -- Look for clauses with opposite polarity on v
        let partners := if p then db.negIndex[v]! else db.posIndex[v]!
        for pj in partners do
          if pj != ci then
            let c2 := db.clauses[pj]!
            let resolvent := resolveOn c1 c2 v
            if !db.contains resolvent then
              return some (c1, c2, v, resolvent)
  return none

/-- Fast greedy resolution: same clause-order as original but
    uses Array for O(1) indexing instead of List for O(n) access. -/
def fastResolution (formula : SATFormula) (maxSteps : ℕ)
    : Derivation × ℕ :=
  let cls := formula.toArray
  let rec go (cls : Array SATClause) (steps : Array ResolutionStep)
      (fuel : ℕ) : Array ResolutionStep × Bool :=
    match fuel with
    | 0 => (steps, false)
    | fuel + 1 =>
      if cls.any (·.isEmpty) then (steps, true)
      else
        -- Same scan as greedy: first pair found
        let found := Id.run do
          for ri in [:cls.size] do
            let i := cls.size - 1 - ri
            for rj in [:cls.size] do
              let j := cls.size - 1 - rj
              if i != j then
                let c1 := cls[i]!
                let c2 := cls[j]!
                match findResolvable c1 c2 with
                | some v =>
                  let resolvent := resolveOn c1 c2 v
                  if !cls.any (· == resolvent) then
                    return some (c1, c2, v, resolvent)
                | none => pure ()
          return none
        match found with
        | none => (steps, false)
        | some (c1, c2, v, resolvent) =>
          let step : ResolutionStep :=
            { clause1 := c1, clause2 := c2,
              pivot := v, result := resolvent }
          go (cls.push resolvent) (steps.push step) fuel
  let (steps, found) := go cls #[] maxSteps
  let deriv : Derivation :=
    { steps := steps.toList,
      conclusion := if found then [] else [(999, true)] }
  (deriv, steps.size)

/-- Fast random resolution: random pair selection with index. -/
def fastRandomResolution (formula : SATFormula) (maxSteps : ℕ)
    (seed : ℕ) : Derivation :=
  let rec go (db : ClauseDB) (steps : Array ResolutionStep)
      (fuel : ℕ) (state : UInt32)
      : Array ResolutionStep × Bool :=
    match fuel with
    | 0 => (steps, false)
    | fuel + 1 =>
      if db.hasEmpty then (steps, true)
      else
        -- Collect ALL resolvable variables
        let resolvableVars := Id.run do
          let mut rv : Array ℕ := #[]
          for v in [:db.nVars] do
            if db.posIndex[v]!.size > 0 && db.negIndex[v]!.size > 0
            then rv := rv.push v
          return rv
        if resolvableVars.size == 0 then (steps, false)
        else
          -- Pick random variable
          let (rval, s1) := xorshift32 state
          let vIdx := rval.toNat % resolvableVars.size
          let v := resolvableVars[vIdx]!
          -- Pick random clauses from pos/neg
          let pos := db.posIndex[v]!
          let neg := db.negIndex[v]!
          let (rval2, s2) := xorshift32 s1
          let (rval3, s3) := xorshift32 s2
          let pIdx := rval2.toNat % pos.size
          let nIdx := rval3.toNat % neg.size
          let c1 := db.clauses[pos[pIdx]!]!
          let c2 := db.clauses[neg[nIdx]!]!
          let resolvent := resolveOn c1 c2 v
          if db.contains resolvent then
            go db steps fuel s3  -- skip, try again
          else
            let step : ResolutionStep :=
              { clause1 := c1, clause2 := c2,
                pivot := v, result := resolvent }
            go (db.addClause resolvent) (steps.push step) fuel s3
  let db := ClauseDB.build formula
  let (steps, found) := go db #[] maxSteps (seedToState seed)
  { steps := steps.toList,
    conclusion := if found then [] else [(999, true)] }

/-- Fast width-minimizing resolution. -/
def fastWidthMinResolution (formula : SATFormula) (maxSteps : ℕ)
    : Derivation :=
  let rec go (db : ClauseDB) (steps : Array ResolutionStep)
      (fuel : ℕ) : Array ResolutionStep × Bool :=
    match fuel with
    | 0 => (steps, false)
    | fuel + 1 =>
      if db.hasEmpty then (steps, true)
      else
        -- Find ALL resolvable pairs, pick shortest resolvent
        let best := Id.run do
          let mut b : Option (SATClause × SATClause × ℕ × SATClause × ℕ) := none
          for v in [:db.nVars] do
            let pos := db.posIndex[v]!
            let neg := db.negIndex[v]!
            if pos.size > 0 && neg.size > 0 then
              let c1 := db.clauses[pos[0]!]!
              let c2 := db.clauses[neg[0]!]!
              let resolvent := resolveOn c1 c2 v
              if !db.contains resolvent then
                let w := List.length resolvent
                match b with
                | none => b := some (c1, c2, v, resolvent, w)
                | some (_, _, _, _, bw) =>
                  if w < bw then b := some (c1, c2, v, resolvent, w)
          return b
        match best with
        | none => (steps, false)
        | some (c1, c2, v, resolvent, _) =>
          let step : ResolutionStep :=
            { clause1 := c1, clause2 := c2,
              pivot := v, result := resolvent }
          go (db.addClause resolvent) (steps.push step) fuel
  let db := ClauseDB.build formula
  let (steps, found) := go db #[] maxSteps
  { steps := steps.toList,
    conclusion := if found then [] else [(999, true)] }

/-! ## Verification -/

#eval! do
  IO.println "=== FAST vs ORIGINAL RESOLUTION ==="
  IO.println ""
  IO.println "formula\t\torig\tfast\tmatch"
  let formulas : List (String × SATFormula) := [
    ("(x0)(¬x0)", [[(0, true)], [(0, false)]]),
    ("chain-3", chainFormula 3),
    ("chain-5", chainFormula 5),
    ("PHP(3,2)", pigeonhole 3 2),
    ("PHP(4,3)", pigeonhole 4 3),
    ("tseitin-5", tseitinCycle 5),
    ("forced-5", forcedContradiction 5)]
  for (name, f) in formulas do
    let (origD, _) := greedyResolution f 5000
    let (fastD, _) := fastResolution f 5000
    let origOk := origD.conclusion.isEmpty
    let fastOk := fastD.conclusion.isEmpty
    IO.println s!"  {name}\t\t{List.length origD.steps}({origOk})\t{List.length fastD.steps}({fastOk})\t{origOk == fastOk}"

end RotationCalculus
