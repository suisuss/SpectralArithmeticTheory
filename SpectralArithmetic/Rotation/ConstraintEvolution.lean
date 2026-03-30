/-
  Constraint Evolution: Learned Clauses as Living Constraints
  =============================================================

  The PHP(3,2) result from StrategyAsTerm showed that variable
  elimination order alone can't refute PHP — 0/720 orderings
  derive □. The reason: PHP needs to resolve clauses that
  DON'T EXIST in the original formula. The resolvents from
  early steps CREATE new clauses that enable later steps.

  This is constraint evolution: the clause database changes
  during search. Each resolution step adds a resolvent.
  The new resolvent enables NEW resolutions that were impossible
  before. The constraint at step k depends on what was learned
  at steps 1..k-1.

  In the rotation calculus: the constraint-as-term (Part C)
  must UPDATE as the strategy executes. The strategy doesn't
  just walk a static arrangement — it transforms the constraint
  at each step. The formula is a living, evolving term.

  This is the key difference from SAT:
  - SAT: constraint is STATIC. Check arrangement against fixed formula.
  - UNSAT: constraint EVOLVES. Each resolution step changes what's possible.
-/

import SpectralArithmetic.Rotation.StrategyAsTerm

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Evolving clause database -/

/-- An evolving state: clause database + history of changes. -/
structure EvolvingState where
  clauses    : List SATClause
  generation : ℕ              -- how many evolution steps
  history    : List (SATClause × String)  -- (clause, reason)
  deriving Repr

/-- Initial state from a formula. -/
def EvolvingState.init (f : SATFormula) : EvolvingState :=
  { clauses := f,
    generation := 0,
    history := f.map fun c => (c, "original") }

/-- Has the empty clause been derived? -/
def EvolvingState.isRefuted (s : EvolvingState) : Bool :=
  s.clauses.any (·.isEmpty)

/-- Apply one resolution step: resolve two clauses, add the
    resolvent to the database. The constraint EVOLVES. -/
def evolveStep (s : EvolvingState) (c1Idx c2Idx : ℕ)
    : Option (EvolvingState × ResolutionStep) :=
  if c1Idx >= List.length s.clauses then none
  else if c2Idx >= List.length s.clauses then none
  else
  let cl1 := s.clauses[c1Idx]!
  let cl2 := s.clauses[c2Idx]!
  let c1 := some cl1
  let c2 := some cl2
  match c1, c2 with
  | some cl1, some cl2 =>
    match findResolvable cl1 cl2 with
    | some pivot =>
      let resolvent := resolveOn cl1 cl2 pivot
      let step : ResolutionStep :=
        { clause1 := cl1, clause2 := cl2,
          pivot := pivot, result := resolvent }
      some ({ clauses := s.clauses ++ [resolvent],
              generation := s.generation + 1,
              history := s.history ++
                [(resolvent, s!"resolve({c1Idx},{c2Idx}) on x{pivot}")] },
           step)
    | none => none
  | _, _ => none

/-! ## Evolving resolution: resolve with accumulated clauses -/

/-- Greedy evolving resolution: at each step, find ANY resolvable
    pair (including newly derived clauses) and resolve.
    The clause database grows. New clauses enable new resolutions. -/
def evolvingResolution (formula : SATFormula) (maxSteps : ℕ)
    : EvolvingState × List ResolutionStep :=
  let rec go (s : EvolvingState) (steps : List ResolutionStep)
      (fuel : ℕ) : EvolvingState × List ResolutionStep :=
    match fuel with
    | 0 => (s, steps)
    | fuel + 1 =>
      if s.isRefuted then (s, steps)
      else
        -- Find any resolvable pair in the FULL database
        -- (including previously derived clauses)
        let n := List.length s.clauses
        let found := (List.range n).findSome? fun i =>
          (List.range n).findSome? fun j =>
            if i == j then none
            else match evolveStep s i j with
              | some (s', step) =>
                -- Only add if resolvent is genuinely new
                if s.clauses.contains step.result then none
                else some (s', step)
              | none => none
        match found with
        | none => (s, steps)
        | some (s', step) => go s' (steps ++ [step]) fuel
  go (EvolvingState.init formula) [] maxSteps

/-! ## The constraint-as-term evolves

    In Part C (SelfContained.lean), the constraint is a fixed term.
    With evolution, the constraint term GROWS: each learned clause
    adds to it. The constraint at generation g is:

      constraintTerm(g) = original_constraint ++ learned_clauses(1..g)

    The strategy interacts with an evolving constraint:
    what's possible at step k depends on what was derived at steps 1..k-1.
    The strategy and the constraint CO-EVOLVE. -/

/-- Encode an evolving state as a term.
    The term represents the CURRENT state of knowledge:
    original clauses + all derived clauses. -/
def evolvingToTerm (s : EvolvingState) : Term :=
  Term.fromList (s.clauses.map clauseToTerm)

/-- The evolution trajectory: how the constraint term changes. -/
def evolutionTrajectory (formula : SATFormula) (maxSteps : ℕ)
    : List (ℕ × ℕ × ℕ) :=  -- (generation, #clauses, total_literals)
  let rec go (s : EvolvingState) (acc : List (ℕ × ℕ × ℕ))
      (fuel : ℕ) : List (ℕ × ℕ × ℕ) :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if s.isRefuted then
        acc ++ [(s.generation, List.length s.clauses,
                 s.clauses.foldl (fun a c => a + List.length c) 0)]
      else
        let n := List.length s.clauses
        let found := (List.range n).findSome? fun i =>
          (List.range n).findSome? fun j =>
            if i == j then none
            else match evolveStep s i j with
              | some (s', step) =>
                if s.clauses.contains step.result then none
                else some s'
              | none => none
        match found with
        | none => acc
        | some s' =>
          let lits := s'.clauses.foldl
            (fun a c => a + List.length c) 0
          go s' (acc ++ [(s'.generation, List.length s'.clauses,
                          lits)]) fuel
  let initLits := formula.foldl (fun a c => a + List.length c) 0
  go (EvolvingState.init formula)
     [(0, List.length formula, initLits)] maxSteps

/-! ## Demonstrations -/

#eval! do
  IO.println "=== CONSTRAINT EVOLUTION ==="
  IO.println ""

  -- 1. Chain formula (evolving should find □)
  IO.println "--- Chain: (x0)(¬x0∨x1)(¬x1) ---"
  let f : SATFormula :=
    [[(0, true)], [(0, false), (1, true)], [(1, false)]]
  let (finalState, steps) := evolvingResolution f 20
  IO.println s!"  steps: {List.length steps}"
  IO.println s!"  refuted: {finalState.isRefuted}"
  IO.println s!"  final clauses: {List.length finalState.clauses}"
  IO.println s!"  generations: {finalState.generation}"
  for step in steps do
    IO.println s!"    {showStep step}"
  IO.println ""
  IO.println "  evolution history:"
  for (clause, reason) in finalState.history do
    let shown := if clause.isEmpty then "□"
      else String.intercalate "∨" (clause.map fun (v, p) =>
        if p then s!"x{v}" else s!"¬x{v}")
    IO.println s!"    {shown} [{reason}]"

  -- 2. PHP(3,2) — THIS is where evolution matters
  IO.println ""
  IO.println "--- PHP(3,2): evolving resolution ---"
  let php := pigeonhole 3 2
  let (phpState, phpSteps) := evolvingResolution php 50
  IO.println s!"  steps: {List.length phpSteps}"
  IO.println s!"  refuted: {phpState.isRefuted}"
  IO.println s!"  original clauses: {List.length php}"
  IO.println s!"  final clauses: {List.length phpState.clauses}"
  IO.println s!"  generations: {phpState.generation}"
  IO.println ""
  IO.println "  derivation:"
  for step in phpSteps do
    IO.println s!"    {showStep step}"

#eval! do
  IO.println ""
  IO.println "=== EVOLUTION TRAJECTORY ==="
  IO.println ""
  IO.println "--- Chain formula ---"
  let f : SATFormula :=
    [[(0, true)], [(0, false), (1, true)], [(1, false)]]
  let traj := evolutionTrajectory f 20
  IO.println "  gen\tclauses\tliterals"
  for (gen, cls, lits) in traj do
    IO.println s!"  {gen}\t{cls}\t{lits}"
  IO.println ""
  IO.println "--- PHP(3,2) ---"
  let php := pigeonhole 3 2
  let phpTraj := evolutionTrajectory php 50
  IO.println "  gen\tclauses\tliterals"
  for (gen, cls, lits) in phpTraj do
    IO.println s!"  {gen}\t{cls}\t{lits}"

#eval! do
  IO.println ""
  IO.println "=== STATIC vs EVOLVING COMPARISON ==="
  IO.println ""
  let formulas : List (String × SATFormula) := [
    ("(x0)(¬x0)", [[(0, true)], [(0, false)]]),
    ("chain-3", [[(0, true)], [(0, false), (1, true)],
                 [(1, false)]]),
    ("(x0∨x1)(¬x0)(¬x1)",
     [[(0, true), (1, true)], [(0, false)], [(1, false)]]),
    ("PHP(3,2)", pigeonhole 3 2)]
  IO.println "formula\t\t\tstatic\tevolving\tPHP-fixed?"
  for (name, f) in formulas do
    -- Static: basic greedy resolution
    let (staticD, _) := greedyResolution f 100
    let staticOk := staticD.conclusion.isEmpty
    -- Evolving: with clause accumulation
    let (evolveS, evolveSteps) := evolvingResolution f 100
    let evolveOk := evolveS.isRefuted
    IO.println s!"  {name}\t\t{List.length staticD.steps}({staticOk})\t{List.length evolveSteps}({evolveOk})"

/-! ## Assessment

    CONSTRAINT EVOLUTION: the clause database is a living structure.

    The PHP(3,2) result from StrategyAsTerm showed 0/720 variable
    orderings derive □. That's because variable elimination on the
    ORIGINAL formula doesn't produce useful resolvents. But evolving
    resolution DOES work: the resolvents from early steps create
    new clauses that enable the derivation of □.

    The key mechanism: resolution step at generation g produces
    a new clause that DIDN'T EXIST at generation g-1. This clause
    enables resolutions at generation g+1 that were impossible before.
    The constraint literally evolves.

    In the rotation calculus:
    - STATIC constraint: the formula is a fixed term. Verification
      checks the arrangement against it. The constraint doesn't change.
    - EVOLVING constraint: the formula is a growing term. Each
      resolution step appends a resolvent. The constraint at step k
      depends on all previous steps.

    This is the structural difference between SAT and UNSAT:
    - SAT: static constraint, dynamic arrangement (search for a good one)
    - UNSAT: dynamic constraint, the constraint ITSELF contracts toward □

    The evolution trajectory shows the formula growing (more clauses)
    while individual clauses shrink (fewer literals). Total literals
    may increase or decrease. The trajectory terminates when a clause
    of length 0 appears.

    WHAT THIS CHANGES about the rotation calculus:

    The original design has a FIXED constraint. The rotation rule
    walks the arrangement, checking C at each step. C never changes.
    With evolution, C changes at each step. The rotation doesn't just
    check — it TRANSFORMS the constraint.

    This means observe(pair(a, b)) does TWO things:
    1. Check C(a, b) — does this step pass?
    2. Update C based on what was learned — C becomes C'

    The rewrite rule produces not just a rearranged term but also
    an evolved constraint. The pair (term, constraint) co-evolves.
    This is the rotation calculus with STATE — the constraint is
    the state, and the rotation rule is the state transition.
-/

end RotationCalculus
