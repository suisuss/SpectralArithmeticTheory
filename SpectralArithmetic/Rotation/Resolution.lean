/-
  Resolution in the Rotation Calculus
  ====================================

  Resolution is the proof system behind UNSAT:
  from two clauses sharing a variable in opposite polarities,
  derive a new clause covering both without that variable.

    C1 = (x OR A)     -- x appears positive
    C2 = (NOT x OR B)  -- x appears negative
    ───────────────────
    C3 = (A OR B)      -- resolved: x eliminated

  When resolution derives the EMPTY clause, the formula is
  proved unsatisfiable.

  In the rotation calculus, this becomes:
  - A clause is a set of literals (a term encoding accepted arrangements)
  - Two clauses that conflict on a variable can be COMPOSED
  - The composition eliminates the conflicting variable
  - The empty term (ground) = contradiction

  This file:
  1. Encodes clauses and resolution as rotation calculus terms
  2. Implements resolution derivation
  3. Shows resolution as a CONTRACTION process — the formula
     contracts toward ground (empty clause = contradiction)
  4. Connects resolution to the constraint-as-term encoding (Part C)
-/

import SpectralArithmetic.Rotation.UNSATProof

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Clauses as terms

    A clause is a disjunction of literals.
    Encoded as a flat list of literal terms:
      clause [x0=T, x1=F, x2=T]
        = pair(literal 0 true, pair(literal 1 false, pair(literal 2 true, ground)))

    The empty clause (contradiction) = ground. -/

/-- Encode a SAT clause as a rotation calculus term. -/
def clauseToTerm (clause : SATClause) : Term :=
  Term.fromList (clause.map fun (v, p) => literal v p)

/-- Decode a term back to a clause. -/
def termToClause (t : Term) : SATClause :=
  t.toList.map fun lit => (litVar lit, litPol lit)

/-- The empty clause = ground = contradiction. -/
def emptyClause : Term := .ground

/-- Is this term the empty clause? -/
def isContradiction (t : Term) : Bool := t == .ground

/-! ## Resolution as term composition

    Resolution of two clauses on variable x:
    1. Find a variable that appears positive in C1, negative in C2
    2. Remove the resolved literals
    3. Combine the remaining literals

    In terms: the resolved pair is ELIMINATED and the remaining
    elements are MERGED into a new list term. -/

/-- Find a variable that can be resolved between two clauses.
    Returns the variable index, or none if no resolution is possible. -/
def findResolvable (c1 c2 : SATClause) : Option ℕ :=
  c1.findSome? fun (v, p) =>
    if c2.any fun (v', p') => v == v' && p != p'
    then some v
    else none

/-- Resolve two clauses on a specific variable.
    Removes the resolved literal from both and merges. -/
def resolveOn (c1 c2 : SATClause) (v : ℕ) : SATClause :=
  let c1' := c1.filter fun (v', _) => v' != v
  let c2' := c2.filter fun (v', _) => v' != v
  -- Merge and deduplicate
  let merged := c1' ++ c2'
  merged.eraseDups

/-- Resolve two clauses (find the pivot automatically). -/
def resolveClauses (c1 c2 : SATClause) : Option SATClause :=
  match findResolvable c1 c2 with
  | some v => some (resolveOn c1 c2 v)
  | none => none

/-! ## Resolution as term rewriting

    Resolution of two clause-terms:
      observe(pair(clauseTerm1, clauseTerm2))
    If they share a resolvable variable, the rotation rule
    produces the resolvent (a shorter clause-term).
    If not, stuck (no resolution possible). -/

/-- The resolution constraint: two clause-terms can be composed
    if they share a resolvable variable. -/
def resolutionConstraint : Constraint where
  check := fun a b =>
    let c1 := termToClause a
    let c2 := termToClause b
    (findResolvable c1 c2).isSome

/-- Apply resolution as a term operation.
    Takes two clause-terms, resolves them, returns the resolvent. -/
def resolveTerms (a b : Term) : Option Term :=
  let c1 := termToClause a
  let c2 := termToClause b
  match resolveClauses c1 c2 with
  | some resolvent => some (clauseToTerm resolvent)
  | none => none

/-! ## Resolution derivation

    A derivation is a sequence of resolution steps that
    produces the empty clause from the initial formula.
    Each step records: which two clauses were resolved,
    on which variable, producing which resolvent. -/

/-- A single resolution step. -/
structure ResolutionStep where
  clause1 : SATClause
  clause2 : SATClause
  pivot   : ℕ
  result  : SATClause
  deriving Repr

/-- A resolution derivation: a sequence of steps. -/
structure Derivation where
  steps      : List ResolutionStep
  conclusion : SATClause  -- should be [] for UNSAT proof
  deriving Repr

/-- Show a resolution step. -/
def showStep (s : ResolutionStep) : String :=
  let showClause := fun (c : SATClause) =>
    if c.isEmpty then "□"
    else String.intercalate " ∨ " (c.map fun (v, p) =>
      if p then s!"x{v}" else s!"¬x{v}")
  s!"{showClause s.clause1}  ⊗  {showClause s.clause2}  " ++
  s!"[x{s.pivot}]  →  {showClause s.result}"

/-! ## Resolution strategies -/

/-- Greedy resolution: at each step, resolve two clauses that
    produce the shortest resolvent. Repeat until empty clause
    or no more resolutions possible.
    Returns (derivation, remaining_clauses). -/
def greedyResolution (clauses : List SATClause)
    (maxSteps : ℕ) : Derivation × List SATClause :=
  let rec go (cls : List SATClause) (steps : List ResolutionStep)
      (fuel : ℕ) : Derivation × List SATClause :=
    match fuel with
    | 0 =>
      ({ steps := steps,
         conclusion := cls.head?.getD [] }, cls)
    | fuel + 1 =>
      if cls.any (·.isEmpty) then
        ({ steps := steps, conclusion := [] }, cls)
      else
        let found := cls.findSome? fun c1 =>
          cls.findSome? fun c2 =>
            if c1 == c2 then none
            else match findResolvable c1 c2 with
              | some v => some (c1, c2, v)
              | none => none
        match found with
        | none =>
          ({ steps := steps,
             conclusion := cls.head?.getD [] }, cls)
        | some (c1, c2, v) =>
          let resolvent := resolveOn c1 c2 v
          let step : ResolutionStep :=
            { clause1 := c1, clause2 := c2,
              pivot := v, result := resolvent }
          go (resolvent :: cls) (steps ++ [step]) fuel
  go clauses [] maxSteps

/-- Unit resolution: only resolve with unit clauses (1 literal).
    This is the resolution analogue of unit propagation. -/
def unitResolution (clauses : List SATClause)
    (maxSteps : ℕ) : Derivation × List SATClause :=
  let rec go (cls : List SATClause) (steps : List ResolutionStep)
      (fuel : ℕ) : Derivation × List SATClause :=
    match fuel with
    | 0 =>
      ({ steps := steps, conclusion := cls.head?.getD [] }, cls)
    | fuel + 1 =>
      if cls.any (·.isEmpty) then
        ({ steps := steps, conclusion := [] }, cls)
      else
        let units := cls.filter fun c => c.length == 1
        match units with
        | [] =>
          ({ steps := steps,
             conclusion := cls.head?.getD [] }, cls)
        | unit :: _ =>
          let partner := cls.find? fun c =>
            c != unit && (findResolvable unit c).isSome
          match partner with
          | none =>
            ({ steps := steps,
               conclusion := cls.head?.getD [] }, cls)
          | some p =>
            match findResolvable unit p with
            | some v =>
              let resolvent := resolveOn unit p v
              let step : ResolutionStep :=
                { clause1 := unit, clause2 := p,
                  pivot := v, result := resolvent }
              go (resolvent :: cls) (steps ++ [step]) fuel
            | none =>
              ({ steps := steps,
                 conclusion := cls.head?.getD [] }, cls)
  go clauses [] maxSteps

/-! ## Resolution as contraction

    Resolution has the structure of contraction:
    - Start: formula = list of clauses (large term)
    - Each step: two clauses → one shorter clause (contraction)
    - End: empty clause = ground (fully contracted)

    The formula SHRINKS (in total literal count) with each
    successful resolution. This is contraction toward ground.

    The resolution constraint: two clauses can be composed
    (resolved) if they share a variable in opposite polarities.
    This is exactly the rotation calculus constraint pattern.

    A resolution derivation IS a rotation:
      observe(pair(clause1, pair(clause2, ...rest...)))
    with the resolution constraint. If clause1 and clause2
    can be resolved, the rotation produces their resolvent
    and the rest. The resolvent is shorter. The process
    contracts until ground (empty clause) or stuck (no
    more resolutions). -/

/-- Encode a formula as a clause-list term for resolution. -/
def formulaToClauseList (f : SATFormula) : Term :=
  Term.fromList (f.map clauseToTerm)

/-- Resolution as tree fold: at each pair node, try to resolve
    the two clause-terms. -/
def resolutionTreeFold : Term → List ResolutionStep
  | .ground => []
  | .pair a .ground => []
  | .pair a b =>
    let c1 := termToClause a
    let c2 := termToClause b
    match findResolvable c1 c2 with
    | some v =>
      let resolvent := resolveOn c1 c2 v
      [{ clause1 := c1, clause2 := c2,
         pivot := v, result := resolvent }]
      ++ resolutionTreeFold a
      ++ resolutionTreeFold b
    | none =>
      resolutionTreeFold a ++ resolutionTreeFold b
  | .observe t => resolutionTreeFold t

/-! ## Demonstrations -/

#eval! do
  IO.println "=== RESOLUTION IN THE ROTATION CALCULUS ==="
  IO.println ""

  -- 1. Trivial UNSAT: (x0) AND (NOT x0)
  IO.println "--- Trivial: (x0) AND (NOT x0) ---"
  let f : SATFormula := [[(0, true)], [(0, false)]]
  IO.println s!"  clauses: {f}"
  let r := resolveClauses [(0, true)] [(0, false)]
  IO.println s!"  resolve(x0, ¬x0) = {repr r}"
  let (deriv, remaining) := greedyResolution f 10
  IO.println s!"  derivation: {deriv.steps.length} steps"
  IO.println s!"  conclusion: {deriv.conclusion}"
  IO.println s!"  empty clause derived: {deriv.conclusion.isEmpty}"
  for step in deriv.steps do
    IO.println s!"    {showStep step}"

  -- 2. Slightly harder: (x0 OR x1) AND (NOT x0) AND (NOT x1)
  IO.println ""
  IO.println "--- (x0 ∨ x1) ∧ (¬x0) ∧ (¬x1) ---"
  let f2 : SATFormula :=
    [[(0, true), (1, true)], [(0, false)], [(1, false)]]
  let (deriv2, _) := greedyResolution f2 20
  IO.println s!"  derivation: {deriv2.steps.length} steps"
  IO.println s!"  conclusion: {deriv2.conclusion}"
  for step in deriv2.steps do
    IO.println s!"    {showStep step}"

  -- 3. Chain: (x0) AND (NOT x0 OR x1) AND (NOT x1)
  IO.println ""
  IO.println "--- chain: (x0) ∧ (¬x0 ∨ x1) ∧ (¬x1) ---"
  let f3 : SATFormula :=
    [[(0, true)], [(0, false), (1, true)], [(1, false)]]
  let (deriv3, _) := greedyResolution f3 20
  IO.println s!"  derivation: {deriv3.steps.length} steps"
  IO.println s!"  conclusion: {deriv3.conclusion}"
  for step in deriv3.steps do
    IO.println s!"    {showStep step}"

  -- 4. Unit resolution on the chain
  IO.println ""
  IO.println "--- unit resolution on chain ---"
  let (uderiv3, _) := unitResolution f3 20
  IO.println s!"  derivation: {uderiv3.steps.length} steps"
  IO.println s!"  conclusion: {uderiv3.conclusion}"
  for step in uderiv3.steps do
    IO.println s!"    {showStep step}"

/-! ### Demo 2: Resolution on PHP -/

#eval! do
  IO.println ""
  IO.println "=== RESOLUTION ON PHP(3,2) ==="
  IO.println ""
  let php := pigeonhole 3 2
  IO.println s!"  clauses: {List.length php}"
  -- Unit resolution (won't get far — PHP has no unit clauses)
  let (uderiv, ucls) := unitResolution php 50
  IO.println s!"  unit resolution: {uderiv.steps.length} steps"
  IO.println s!"  conclusion: {uderiv.conclusion}"
  -- Greedy resolution
  let (gderiv, gcls) := greedyResolution php 100
  IO.println s!"  greedy resolution: {gderiv.steps.length} steps"
  IO.println s!"  conclusion empty: {gderiv.conclusion.isEmpty}"
  if gderiv.steps.length ≤ 20 then
    for step in gderiv.steps do
      IO.println s!"    {showStep step}"
  else
    IO.println s!"  (showing first 10 steps)"
    for step in gderiv.steps.take 10 do
      IO.println s!"    {showStep step}"

/-! ### Demo 3: Resolution as clause-term contraction -/

#eval! do
  IO.println ""
  IO.println "=== RESOLUTION AS CONTRACTION ==="
  IO.println ""
  -- Encode the chain formula as a clause-list term
  let f : SATFormula :=
    [[(0, true)], [(0, false), (1, true)], [(1, false)]]
  let encoded := formulaToClauseList f
  IO.println s!"  formula term size: {encoded.size}"
  IO.println s!"  formula term depth: {encoded.depth}"
  -- Resolution tree fold
  let steps := resolutionTreeFold encoded
  IO.println s!"  resolution steps found: {steps.length}"
  for step in steps do
    IO.println s!"    {showStep step}"
  -- Track contraction
  IO.println ""
  IO.println "--- Contraction trajectory ---"
  let (deriv, _) := greedyResolution f 20
  let mut totalLits := f.foldl (fun acc c => acc + List.length c) 0
  IO.println s!"  initial: {List.length f} clauses, {totalLits} literals"
  for step in deriv.steps do
    totalLits := totalLits + step.result.length
    IO.println s!"  + {showStep step}  [total lits: {totalLits}]"
  IO.println s!"  final: conclusion={deriv.conclusion}"

/-! ### Demo 4: Comparing resolution with CDCL -/

#eval! do
  IO.println ""
  IO.println "=== RESOLUTION vs CDCL ==="
  IO.println ""
  -- Same formula, two proof systems
  let f : SATFormula :=
    [[(0, true), (1, true)], [(0, false)], [(1, false)]]
  -- Resolution
  let (rderiv, _) := greedyResolution f 20
  IO.println s!"  resolution: {rderiv.steps.length} steps, \
    empty={rderiv.conclusion.isEmpty}"
  -- CDCL
  let (found, cost, learned) := cdclSearch f (List.range 2) []
  IO.println s!"  CDCL: found={found} cost={cost} \
    learned={List.length learned}"
  IO.println ""
  IO.println "  resolution steps:"
  for step in rderiv.steps do
    IO.println s!"    {showStep step}"
  IO.println "  CDCL learned clauses:"
  let mut i := 0
  for c in learned do
    let shown := String.intercalate " ∨ " (c.map fun (v, p) =>
      if p then s!"x{v}" else s!"¬x{v}")
    IO.println s!"    {i}: {shown}"
    i := i + 1

/-! ## Assessment

    Resolution in the rotation calculus:

    1. CLAUSES AS TERMS: each clause is a flat list of literal
       terms. The empty clause is ground. Resolution CONTRACTS
       clauses toward ground.

    2. RESOLUTION = CONSTRAINED COMPOSITION: two clause-terms
       compose (resolve) if they share a variable in opposite
       polarities. The constraint is "resolvable." The result
       is shorter. This IS the rotation pattern: observe a pair
       of clauses, check if they can resolve, produce the resolvent.

    3. THE RESOLUTION CONSTRAINT is structural, not arbitrary:
       it detects complementary literals by comparing label parity
       (variable index) and polarity (odd/even encoding). This is
       a property of the TERM STRUCTURE, not an external predicate.

    4. CONTRACTION TRAJECTORY: resolution produces a contraction
       trajectory — the formula's total literal count decreases
       toward zero. Ground = empty clause = contradiction.
       This trajectory IS the UNSAT proof.

    5. THE GAP between SAT and UNSAT proofs:
       - SAT proof = selector term (one arrangement that works)
       - UNSAT proof = resolution derivation (sequence of clause
         compositions that reach ground)
       - The selector is O(tree depth). The derivation can be
         O(n^2) for easy formulas, exponential for hard ones.
       - Both are expressible as rotation calculus terms:
         the selector is a list of directions, the derivation
         is a list of resolution steps.

    6. WHAT RESOLUTION ADDS to the rotation calculus:
       The rotation rule contracts ARRANGEMENTS (structural).
       Resolution contracts CLAUSES (logical). Both are contraction
       toward ground. But they operate on different objects:
       arrangements are spatial (tree shapes), clauses are logical
       (disjunctions). Resolution is the logical dual of rotation.

    The rotation calculus with resolution can express both:
    - SAT: find an arrangement (selector) that contracts
    - UNSAT: find a derivation (resolution sequence) that contracts
    Both use the same term language. Both contract toward ground.
    The difference is WHAT contracts: the data (SAT) or the
    constraints (UNSAT).
-/

end RotationCalculus
