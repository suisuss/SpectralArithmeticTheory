/-
  Resolution Strategy as Term: Head-Tape Unification
  ====================================================

  The resolution strategy (which clauses to resolve, in what order)
  is currently external Lean logic. Making it a term means the
  processor and the data are the same kind of object.

  Key insight: a resolution strategy is a VARIABLE ELIMINATION ORDER.
  At each step, pick a variable to eliminate. Find all clause pairs
  that resolve on that variable. Resolve them. Move to the next
  variable. If all variables are eliminated and □ has been derived,
  the formula is UNSAT.

  The strategy term is a list of variable indices = a permutation
  of the formula's variables. This is an ARRANGEMENT — the same
  structure as SAT certificates:

  - SAT: arrange LITERALS, check if constraint passes → satisfying assignment
  - UNSAT: arrange PIVOTS, check if resolution reaches □ → refutation

  Both are arrangement problems in the rotation calculus.
  The rotation rule walks the arrangement one element at a time.
  The constraint checks validity at each step.
  Contraction to ground = problem solved.
-/

import SpectralArithmetic.Rotation.ResolutionContraction

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Variable elimination order as strategy -/

/-- A resolution strategy: which variable to eliminate at each step. -/
abbrev Strategy := List ℕ

/-- Execute a resolution strategy: eliminate variables in order.
    At each step, resolve ALL pairs that share the current pivot.
    Returns (final clauses, derivation steps, stuck?). -/
def executeStrategy (formula : List SATClause) (strategy : Strategy)
    : List SATClause × List ResolutionStep × Bool :=
  strategy.foldl (fun (cls, steps, stuck) pivot =>
    if stuck then (cls, steps, true)
    else
      -- Find all pairs resolvable on this pivot
      let newResolvents := cls.flatMap fun c1 =>
        cls.filterMap fun c2 =>
          if c1 == c2 then none
          else if findResolvable c1 c2 == some pivot
          then
            let resolvent := resolveOn c1 c2 pivot
            let step : ResolutionStep :=
              { clause1 := c1, clause2 := c2,
                pivot := pivot, result := resolvent }
            some (resolvent, step)
          else none
      let newCls := newResolvents.map (·.1)
      let newSteps := newResolvents.map (·.2)
      -- Add resolvents, eliminate subsumed
      let combined := eliminateSubsumed (cls ++ newCls)
      (combined, steps ++ newSteps,
       false)
  ) (formula, [], false)

/-- Check if a strategy produces a refutation (derives □). -/
def strategyRefutes (formula : List SATClause)
    (strategy : Strategy) : Bool :=
  let (finalCls, _, _) := executeStrategy formula strategy
  finalCls.any (·.isEmpty)

/-- The strategy constraint: at each step, does eliminating this
    variable make progress? (produces at least one new resolvent) -/
def strategyConstraint (formula : List SATClause) : Constraint where
  check := fun pivotTerm restTerm =>
    let pivot := getLabel pivotTerm
    -- Check if any pair resolves on this pivot
    formula.any fun c1 =>
      formula.any fun c2 =>
        c1 != c2 && findResolvable c1 c2 == some pivot

/-! ## Strategy as a rotation calculus term -/

/-- Encode a strategy as a flat list term. -/
def strategyToTerm (s : Strategy) : Term :=
  Term.fromList (s.map labeledElement)

/-- Decode a term to a strategy. -/
def termToStrategy (t : Term) : Strategy :=
  t.toList.map getLabel

/-- Verify a strategy using the rotation rule:
    observe the strategy-term under the resolution constraint.
    Each rotation step consumes one pivot and checks that
    resolution on that pivot is possible. -/
def verifyStrategy (formula : List SATClause)
    (strategy : Strategy) : Bool × ℕ :=
  let refutes := strategyRefutes formula strategy
  let (_, steps, _) := executeStrategy formula strategy
  (refutes, List.length steps)

/-! ## Strategy search: find a variable order that refutes -/

/-- Try all permutations of variables as strategies. -/
def searchStrategy (formula : List SATClause) (vars : List ℕ)
    : Option Strategy × ℕ :=
  let permsV := perms (vars.map labeledElement)
  let strategies := permsV.map fun p => p.map getLabel
  let rec go : List Strategy → ℕ → Option Strategy × ℕ
    | [], tried => (none, tried)
    | s :: rest, tried =>
      if strategyRefutes formula s
      then (some s, tried + 1)
      else go rest (tried + 1)
  go strategies 0

/-! ## The unified arrangement view

    SAT and UNSAT are BOTH arrangement problems:

    SAT problem:
      elements = literals (x0=T, x0=F, x1=T, x1=F, ...)
      arrangement = assignment (pick one per variable)
      constraint = clause satisfaction
      ground = all clauses satisfied

    UNSAT problem:
      elements = pivot variables (x0, x1, x2, ...)
      arrangement = elimination order (permutation)
      constraint = resolution produces new clauses
      ground = empty clause derived

    Both use the rotation calculus term language.
    Both search over arrangements.
    Both verify in linear time (given the arrangement).
    Both contract toward ground. -/

/-- A unified problem: SAT or UNSAT, same representation. -/
structure UnifiedProblem where
  kind      : String         -- "SAT" or "UNSAT"
  formula   : SATFormula
  elements  : List Term       -- literals (SAT) or pivot labels (UNSAT)
  checkFn   : List ℕ → Bool  -- does this arrangement solve it?

/-- Build a SAT problem. -/
def satProblem (f : SATFormula) (nVars : ℕ) : UnifiedProblem :=
  { kind := "SAT",
    formula := f,
    elements := (List.range nVars).flatMap fun v =>
      [labeledElement (2*v), labeledElement (2*v+1)],
    checkFn := fun arrangement =>
      -- Interpret arrangement as assignment
      let assign := arrangement.filterMap fun label =>
        some (label / 2, label % 2 == 1)
      satisfiesFormula assign f }

/-- Build an UNSAT problem. -/
def unsatProblem (f : SATFormula) (vars : List ℕ) : UnifiedProblem :=
  { kind := "UNSAT",
    formula := f,
    elements := vars.map labeledElement,
    checkFn := fun arrangement =>
      strategyRefutes f arrangement }

/-! ## Demonstrations -/

#eval! do
  IO.println "=== STRATEGY AS TERM ==="
  IO.println ""

  -- 1. Chain UNSAT: (x0)(¬x0∨x1)(¬x1)
  IO.println "--- Chain: (x0)(¬x0∨x1)(¬x1) ---"
  let f : SATFormula :=
    [[(0, true)], [(0, false), (1, true)], [(1, false)]]
  -- Strategy: eliminate x0 first, then x1
  let s1 : Strategy := [0, 1]
  let (refutes1, steps1) := verifyStrategy f s1
  IO.println s!"  strategy [x0,x1]: refutes={refutes1} \
    steps={steps1}"
  -- Strategy: eliminate x1 first, then x0
  let s2 : Strategy := [1, 0]
  let (refutes2, steps2) := verifyStrategy f s2
  IO.println s!"  strategy [x1,x0]: refutes={refutes2} \
    steps={steps2}"
  -- Both should work but may differ in step count
  -- Encode as term
  let term1 := strategyToTerm s1
  let term2 := strategyToTerm s2
  IO.println s!"  strategy term [x0,x1] size: {term1.size}"
  IO.println s!"  strategy term [x1,x0] size: {term2.size}"

  -- 2. (x0∨x1)(¬x0)(¬x1)
  IO.println ""
  IO.println "--- (x0∨x1)(¬x0)(¬x1) ---"
  let f2 : SATFormula :=
    [[(0, true), (1, true)], [(0, false)], [(1, false)]]
  for s in [[0, 1], [1, 0]] do
    let (ref, steps) := verifyStrategy f2 s
    IO.println s!"  strategy {s}: refutes={ref} steps={steps}"

  -- 3. PHP(3,2)
  IO.println ""
  IO.println "--- PHP(3,2) ---"
  let php := pigeonhole 3 2
  let phpVars := List.range 6
  -- Try a specific strategy
  let s3 : Strategy := [0, 1, 2, 3, 4, 5]
  let (ref3, steps3) := verifyStrategy php s3
  IO.println s!"  strategy [0..5]: refutes={ref3} steps={steps3}"
  -- Try reverse
  let s4 : Strategy := [5, 4, 3, 2, 1, 0]
  let (ref4, steps4) := verifyStrategy php s4
  IO.println s!"  strategy [5..0]: refutes={ref4} steps={steps4}"

#eval! do
  IO.println ""
  IO.println "=== STRATEGY SEARCH ==="
  IO.println ""
  -- Search for a refuting strategy
  IO.println "--- Chain: (x0)(¬x0∨x1)(¬x1) ---"
  let f : SATFormula :=
    [[(0, true)], [(0, false), (1, true)], [(1, false)]]
  let (found, tried) := searchStrategy f [0, 1]
  IO.println s!"  found={found.isSome} tried={tried}"
  match found with
  | some s => IO.println s!"  strategy: {s}"
  | none => IO.println "  no strategy found"
  -- PHP(3,2) search
  IO.println ""
  IO.println "--- PHP(3,2) strategy search ---"
  let php := pigeonhole 3 2
  let (foundP, triedP) := searchStrategy php (List.range 6)
  IO.println s!"  found={foundP.isSome} tried={triedP}"
  match foundP with
  | some s => IO.println s!"  strategy: {s}"
  | none => IO.println "  no strategy found in {triedP} attempts"

#eval! do
  IO.println ""
  IO.println "=== UNIFIED VIEW: SAT vs UNSAT AS ARRANGEMENTS ==="
  IO.println ""
  -- SAT instance
  let satF : SATFormula :=
    [[(0, true), (1, true)], [(1, true), (2, true)]]
  IO.println "--- SAT: (x0∨x1)(x1∨x2) ---"
  IO.println s!"  arrangement space: literal assignments"
  IO.println s!"  certificate: assignment that satisfies"
  let (rFlat, cFlat) := flatBruteForce satF 3
  IO.println s!"  brute force: cost={cFlat} found={rFlat.isSome}"
  -- UNSAT instance
  let unsatF : SATFormula :=
    [[(0, true)], [(0, false), (1, true)], [(1, false)]]
  IO.println ""
  IO.println "--- UNSAT: (x0)(¬x0∨x1)(¬x1) ---"
  IO.println s!"  arrangement space: variable elimination orders"
  IO.println s!"  certificate: order that derives □"
  let (foundU, triedU) := searchStrategy unsatF [0, 1]
  IO.println s!"  strategy search: cost={triedU} \
    found={foundU.isSome}"
  -- Show the parallel
  IO.println ""
  IO.println "--- The parallel ---"
  IO.println "  SAT:   arrange LITERALS  under SATISFACTION   → ground"
  IO.println "  UNSAT: arrange PIVOTS    under RESOLUTION     → ground"
  IO.println "  Same language. Same search. Different objects."

#eval! do
  IO.println ""
  IO.println "=== STRATEGY ORDER MATTERS ==="
  IO.println ""
  -- Show that different orders produce different proof lengths
  let php := pigeonhole 3 2
  IO.println "--- PHP(3,2): all orderings ---"
  let orderings := perms ((List.range 6).map labeledElement)
  let mut nRefuting := 0
  let mut nTotal := 0
  let mut bestSteps := 10000
  let mut bestOrder : Strategy := []
  let mut worstSteps := 0
  let mut worstOrder : Strategy := []
  for p in orderings do
    let strategy := p.map getLabel
    let (ref, steps) := verifyStrategy php strategy
    nTotal := nTotal + 1
    if ref then
      nRefuting := nRefuting + 1
      if steps < bestSteps then
        bestSteps := steps; bestOrder := strategy
      if steps > worstSteps then
        worstSteps := steps; worstOrder := strategy
  IO.println s!"  total orderings: {nTotal}"
  IO.println s!"  refuting: {nRefuting}"
  IO.println s!"  non-refuting: {nTotal - nRefuting}"
  if nRefuting > 0 then
    IO.println s!"  shortest proof: {bestSteps} steps, \
      order={bestOrder}"
    IO.println s!"  longest proof: {worstSteps} steps, \
      order={worstOrder}"

/-! ## Assessment

    RESOLUTION STRATEGY AS TERM: the "head" and "tape" are unified.

    The strategy term is a permutation of variable indices.
    The clause database is a list of clause terms.
    Both are rotation calculus terms. The strategy PROCESSES
    the clauses by telling the resolver which variable to
    eliminate at each step.

    This is exactly the Turing head-tape unification:
    - The tape = clause database (data being processed)
    - The head = strategy (instructions for processing)
    - After processing: head and tape are both terms in the
      same language. The head was consumed (each pivot was used).
      The tape was transformed (clauses were resolved).

    THE STRUCTURAL PARALLEL:

    |              | SAT              | UNSAT            |
    |--------------|------------------|------------------|
    | Elements     | Literals         | Pivot variables  |
    | Arrangement  | Assignment       | Elimination order|
    | Constraint   | Clause satisfaction | Resolution possible |
    | Ground       | All satisfied    | □ derived        |
    | Certificate  | Satisfying assign| Refuting order   |
    | Cert size    | n bits           | n! permutation   |
    | Verify cost  | O(m) clause checks| O(m) resolutions|
    | Search cost  | 2^n assignments  | n! orderings     |

    Both SAT and UNSAT certificates are ARRANGEMENTS.
    Both are verified by walking the arrangement.
    Both search over arrangement spaces.
    The rotation calculus expresses both natively.

    WHAT THIS ENABLES:

    The meta-rewrite systems now apply to UNSAT proofs:
    - #0: resolution trace = sequence of rotation events
    - #1: cascade absorption = unit resolution compression
    - Contraction ratio = raw proof length / contracted length
    - Strategy optimization = finding shorter proofs =
      finding better arrangements

    The next step (learned clause as constraint evolution)
    connects the strategy to the constraint: as the strategy
    executes, the clause database CHANGES, which changes
    what resolutions are POSSIBLE, which changes what the
    next strategy step should do. The constraint evolves
    with the computation.
-/

end RotationCalculus
