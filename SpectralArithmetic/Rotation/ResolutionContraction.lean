/-
  Resolution Contraction: Subsumption, UP Bridge, Extended Resolution
  ====================================================================

  Three operations that contract UNSAT proofs:

  1. SUBSUMPTION: if clause C's literals ⊆ D's literals, D is
     redundant. Remove it. The clause database shrinks.

  2. UP-RESOLUTION BRIDGE: unit propagation = unit resolution.
     A unit clause [l] resolved with any clause containing ¬l
     removes ¬l from that clause. A UP cascade = a sequence of
     unit resolutions. This connects meta-rewrite #1 (cascade
     absorption) to resolution (clause contraction).

  3. EXTENDED RESOLUTION: introduce new variables that abbreviate
     subformulas. y = (a AND b) adds 3 clauses but allows y to
     replace (a AND b) everywhere. This can exponentially compress
     proofs — PHP has polynomial extended resolution proofs but
     requires exponential basic resolution.

  All three are contraction operations on clause-terms in the
  rotation calculus.
-/

import SpectralArithmetic.Rotation.Resolution

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ================================================================
    1. SUBSUMPTION
    ================================================================

    Clause C subsumes D if every literal in C appears in D.
    C is more general (shorter). D is redundant.
    Removing D contracts the clause database. -/

/-- Does clause C subsume D? (all literals of C appear in D) -/
def subsumes (c d : SATClause) : Bool :=
  c.all fun lit => d.any fun lit' => lit == lit'

/-- Remove all clauses subsumed by any other clause. -/
def eliminateSubsumed (clauses : List SATClause) : List SATClause :=
  clauses.filter fun c =>
    !clauses.any fun d => d != c && subsumes d c

/-- Self-subsumption: resolve C with D, and if the resolvent
    subsumes C, replace C with the resolvent (strengthening). -/
def selfSubsume (c d : SATClause) : Option SATClause :=
  match findResolvable c d with
  | some v =>
    let resolvent := resolveOn c d v
    if subsumes resolvent c && resolvent.length < List.length c
    then some resolvent
    else none
  | none => none

/-- Apply self-subsumption to all clause pairs. -/
def strengthenAll (clauses : List SATClause) : List SATClause :=
  clauses.map fun c =>
    let strengthened := clauses.findSome? fun d =>
      if d != c then selfSubsume c d else none
    strengthened.getD c

/-! ================================================================
    2. UP-RESOLUTION BRIDGE
    ================================================================

    Unit propagation = unit resolution:
    - Unit clause [l] + clause containing ¬l
    - Resolve on the variable of l
    - Result: clause with ¬l removed

    A UP cascade (k unit propagations) = k unit resolution steps.
    The cascade absorbs into one meta-event (#1).
    The resolution derivation compresses into k steps.

    This bridges:
    - Meta-rewrite #1: CASCADE(k) = k UP steps absorbed
    - Resolution: k unit resolution steps = k clauses shortened
    - Both are the same contraction viewed differently -/

/-- Extract unit clauses from a formula. -/
def extractUnits (clauses : List SATClause)
    : List SATClause × List SATClause :=
  (clauses.filter fun c => List.length c == 1,
   clauses.filter fun c => List.length c != 1)

/-- Perform all possible unit resolutions in one sweep.
    Returns (new_clauses, derivation_steps). -/
def unitSweep (clauses : List SATClause)
    : List SATClause × List ResolutionStep :=
  let (units, rest) := extractUnits clauses
  let result := units.foldl (fun (cls, steps) unit =>
    let resolved := cls.filterMap fun c =>
      match findResolvable unit c with
      | some v =>
        let resolvent := resolveOn unit c v
        let step : ResolutionStep :=
          { clause1 := unit, clause2 := c,
            pivot := v, result := resolvent }
        some (resolvent, step)
      | none => none
    let newClauses := resolved.map (·.1)
    let newSteps := resolved.map (·.2)
    (cls ++ newClauses, steps ++ newSteps)
  ) (clauses, [])
  result

/-- Repeated unit sweeps until fixpoint (= UP cascade as resolution).
    Returns (final_clauses, all_steps, sweeps). -/
def unitCascadeAsResolution (clauses : List SATClause)
    (maxSweeps : ℕ) : List SATClause × List ResolutionStep × ℕ :=
  match maxSweeps with
  | 0 => (clauses, [], 0)
  | maxSweeps + 1 =>
    let (newCls, steps) := unitSweep clauses
    if steps.isEmpty then (clauses, [], 0)
    else
      -- Eliminate subsumed before next sweep
      let cleaned := eliminateSubsumed newCls
      let (finalCls, moreSteps, moreSweeps) :=
        unitCascadeAsResolution cleaned maxSweeps
      (finalCls, steps ++ moreSteps, moreSweeps + 1)

/-! ================================================================
    3. EXTENDED RESOLUTION
    ================================================================

    Introduce a new variable y that abbreviates a conjunction:
      y ≡ (a AND b)
    Encoded as three clauses:
      (¬y ∨ a)        -- y implies a
      (¬y ∨ b)        -- y implies b
      (y ∨ ¬a ∨ ¬b)   -- a and b implies y

    Then replace all occurrences of (a AND b) in the formula
    with y. This can exponentially compress proofs.

    In the rotation calculus: introducing y is adding a new
    labeled element that ABBREVIATES a pair of existing elements.
    The abbreviation term is pair(y, pair(a, b)) — y is the
    label, (a, b) is what it stands for. -/

/-- An extension: a new variable abbreviating a conjunction. -/
structure Extension where
  newVar  : ℕ       -- the new variable index
  litA    : ℕ × Bool  -- first literal of the conjunction
  litB    : ℕ × Bool  -- second literal of the conjunction
  deriving Repr

/-- Generate the three definition clauses for an extension. -/
def extensionClauses (ext : Extension) : List SATClause :=
  let (va, pa) := ext.litA
  let (vb, pb) := ext.litB
  [ [(ext.newVar, false), (va, pa)],           -- ¬y ∨ a
    [(ext.newVar, false), (vb, pb)],           -- ¬y ∨ b
    [(ext.newVar, true), (va, !pa), (vb, !pb)] -- y ∨ ¬a ∨ ¬b
  ]

/-- Apply an extension to a formula: add definition clauses
    and replace occurrences of (a AND b) pattern. -/
def applyExtension (formula : List SATClause) (ext : Extension)
    : List SATClause :=
  let defClauses := extensionClauses ext
  -- Find clauses containing both litA and litB and
  -- replace them with a clause using newVar
  let modified := formula.map fun clause =>
    let hasA := clause.any fun l => l == ext.litA
    let hasB := clause.any fun l => l == ext.litB
    if hasA && hasB then
      -- Replace both literals with the extension variable
      let stripped := clause.filter fun l =>
        l != ext.litA && l != ext.litB
      (ext.newVar, true) :: stripped
    else clause
  defClauses ++ modified

/-- Find a pair of literals that co-occur in many clauses
    (good abbreviation candidate). -/
def findFrequentPair (formula : List SATClause)
    : Option (ℕ × Bool × ℕ × Bool) :=
  let pairs := formula.flatMap fun clause =>
    clause.flatMap fun l1 =>
      clause.filterMap fun l2 =>
        if l1.1 < l2.1 then some (l1, l2) else none
  -- Count each pair
  let counted := pairs.foldl (fun acc (l1, l2) =>
    let key := (l1.1, l1.2, l2.1, l2.2)
    if acc.any fun (k, _) => k == key
    then acc.map fun (k, n) => if k == key then (k, n + 1) else (k, n)
    else acc ++ [(key, 1)]
  ) ([] : List ((ℕ × Bool × ℕ × Bool) × ℕ))
  -- Find the most frequent
  let best := counted.foldl (fun acc (k, n) =>
    match acc with
    | none => some (k, n)
    | some (_, m) => if n > m then some (k, n) else acc
  ) none
  best.map (·.1)

/-! ================================================================
    COMBINED: Subsumption + UP + Resolution
    ================================================================

    The full UNSAT contraction pipeline:
    1. Unit propagation cascade (= unit resolution)
    2. Subsumption elimination (remove redundant clauses)
    3. Resolution (resolve remaining clauses)
    4. Repeat until □ or stuck -/

/-- Full contraction pipeline for UNSAT proving. -/
def contractedResolution (formula : List SATClause)
    (maxSteps : ℕ) : Derivation × List SATClause :=
  -- Phase 1: UP cascade as resolution
  let (afterUP, upSteps, nSweeps) :=
    unitCascadeAsResolution formula 10
  -- Phase 2: Subsumption
  let afterSub := eliminateSubsumed afterUP
  -- Phase 3: Greedy resolution on the residual
  let (resDeriv, remaining) := greedyResolution afterSub maxSteps
  -- Combine
  let allSteps := upSteps ++ resDeriv.steps
  ({ steps := allSteps, conclusion := resDeriv.conclusion },
   remaining)

/-! ================================================================
    DEMONSTRATIONS
    ================================================================ -/

#eval! do
  IO.println "=== RESOLUTION CONTRACTION ==="
  IO.println ""

  -- 1. Subsumption
  IO.println "--- Subsumption ---"
  let clauses : List SATClause :=
    [[(0, true)],
     [(0, true), (1, false)],    -- subsumed by [x0]
     [(0, true), (1, true)],     -- subsumed by [x0]
     [(1, false)],
     [(1, false), (2, true)]]    -- subsumed by [¬x1]
  IO.println s!"  before: {List.length clauses} clauses"
  let cleaned := eliminateSubsumed clauses
  IO.println s!"  after subsumption: {List.length cleaned} clauses"
  IO.println s!"  remaining: {cleaned}"

  -- 2. UP-Resolution bridge
  IO.println ""
  IO.println "--- UP as Resolution ---"
  let f : SATFormula :=
    [[(0, true)], [(0, false), (1, true)],
     [(1, false), (2, true)], [(2, false)]]
  IO.println s!"  formula: {List.length f} clauses"
  IO.println s!"  chain: x0 → x1 → x2 → □"
  let (afterUP, upSteps, nSweeps) :=
    unitCascadeAsResolution f 10
  IO.println s!"  UP sweeps: {nSweeps}"
  IO.println s!"  UP resolution steps: {List.length upSteps}"
  for step in upSteps do
    IO.println s!"    {showStep step}"
  let hasEmpty := afterUP.any (·.isEmpty)
  IO.println s!"  derived □: {hasEmpty}"

  -- 3. Compare basic vs contracted resolution
  IO.println ""
  IO.println "--- Basic vs Contracted ---"
  let f2 : SATFormula :=
    [[(0, true), (1, true)], [(0, false)],
     [(1, false)], [(2, true)], [(2, false)]]
  IO.println s!"  formula: {List.length f2} clauses"
  let (basicDeriv, _) := greedyResolution f2 20
  IO.println s!"  basic resolution: {List.length basicDeriv.steps} \
    steps, □={basicDeriv.conclusion.isEmpty}"
  let (contDeriv, _) := contractedResolution f2 20
  IO.println s!"  contracted: {List.length contDeriv.steps} \
    steps, □={contDeriv.conclusion.isEmpty}"
  IO.println ""
  IO.println "  basic steps:"
  for step in basicDeriv.steps do
    IO.println s!"    {showStep step}"
  IO.println "  contracted steps:"
  for step in contDeriv.steps do
    IO.println s!"    {showStep step}"

#eval! do
  IO.println ""
  IO.println "=== CONTRACTED RESOLUTION ON PHP(3,2) ==="
  IO.println ""
  let php := pigeonhole 3 2
  IO.println s!"  clauses: {List.length php}"
  -- Basic
  let (basicDeriv, _) := greedyResolution php 100
  IO.println s!"  basic: {List.length basicDeriv.steps} steps, \
    □={basicDeriv.conclusion.isEmpty}"
  -- Contracted
  let (contDeriv, remaining) := contractedResolution php 100
  IO.println s!"  contracted: {List.length contDeriv.steps} steps, \
    □={contDeriv.conclusion.isEmpty}"
  IO.println s!"  remaining clauses: {List.length remaining}"
  IO.println ""
  IO.println "  contracted derivation:"
  for step in contDeriv.steps.take 15 do
    IO.println s!"    {showStep step}"
  if List.length contDeriv.steps > 15 then
    IO.println s!"    ... ({List.length contDeriv.steps - 15} more)"

#eval! do
  IO.println ""
  IO.println "=== EXTENDED RESOLUTION ==="
  IO.println ""
  -- Show how extension compresses a formula
  let f : SATFormula :=
    [[(0, true), (1, true), (2, true)],    -- x0 ∨ x1 ∨ x2
     [(0, true), (1, true), (3, false)],   -- x0 ∨ x1 ∨ ¬x3
     [(0, true), (1, true), (4, true)],    -- x0 ∨ x1 ∨ x4
     [(0, false)],                          -- ¬x0
     [(1, false)]]                          -- ¬x1
  IO.println s!"  original: {List.length f} clauses"
  let pair := findFrequentPair f
  IO.println s!"  most frequent pair: {repr pair}"
  -- Apply extension: y5 = (x0 AND x1)
  let ext : Extension :=
    { newVar := 5, litA := (0, true), litB := (1, true) }
  let extended := applyExtension f ext
  IO.println s!"  after extension y5=(x0∧x1): \
    {List.length extended} clauses"
  IO.println "  extended clauses:"
  for c in extended do
    let shown := String.intercalate " ∨ " (c.map fun (v, p) =>
      if p then s!"x{v}" else s!"¬x{v}")
    IO.println s!"    {shown}"
  -- Now resolve the extended formula
  let (extDeriv, _) := contractedResolution extended 30
  IO.println s!"  resolution on extended: \
    {List.length extDeriv.steps} steps, \
    □={extDeriv.conclusion.isEmpty}"
  -- Compare with resolving the original
  let (origDeriv, _) := contractedResolution f 30
  IO.println s!"  resolution on original: \
    {List.length origDeriv.steps} steps, \
    □={origDeriv.conclusion.isEmpty}"

#eval! do
  IO.println ""
  IO.println "=== CONTRACTION COMPARISON SUMMARY ==="
  IO.println ""
  IO.println "formula\t\t\tbasic\tcontracted\tsavings"
  let formulas : List (String × SATFormula) := [
    ("(x0)(¬x0)", [[(0, true)], [(0, false)]]),
    ("chain-3", [[(0, true)], [(0, false), (1, true)],
                 [(1, false)]]),
    ("chain-4", [[(0, true)], [(0, false), (1, true)],
                 [(1, false), (2, true)], [(2, false)]]),
    ("(x0∨x1)(¬x0)(¬x1)",
     [[(0, true), (1, true)], [(0, false)], [(1, false)]]),
    ("PHP(3,2)", pigeonhole 3 2)]
  for (name, f) in formulas do
    let (basicD, _) := greedyResolution f 100
    let (contD, _) := contractedResolution f 100
    let bSteps := List.length basicD.steps
    let cSteps := List.length contD.steps
    let savings := if bSteps > 0
      then (bSteps - cSteps) * 100 / bSteps else 0
    IO.println s!"  {name}\t\t{bSteps}\t{cSteps}\t\t{savings}%"

/-! ## Assessment

    THREE CONTRACTION OPERATIONS, each reducing UNSAT proof size:

    1. SUBSUMPTION: removes redundant clauses.
       If [x0] exists, then [x0, x1] is redundant.
       Contraction: clause database shrinks.
       Cost: O(n^2) pairwise check.

    2. UP-RESOLUTION BRIDGE: unit propagation = unit resolution.
       A unit clause [l] resolves with every clause containing ¬l,
       shortening those clauses by one literal.
       A cascade of k unit propagations = k unit resolution steps.
       This connects meta-rewrite #1 (CASCADE absorption) to
       resolution proof compression: the cascade IS the proof.

    3. EXTENDED RESOLUTION: abbreviation variables compress clauses.
       y = (a AND b) replaces all (a AND b) occurrences with y.
       Adds 3 definition clauses but can shorten many others.
       Exponentially more powerful than basic resolution.

    COMBINED PIPELINE:
       UP cascade → subsumption → resolution
    The UP cascade handles the deterministic part (forced resolutions).
    Subsumption cleans up redundancies created by UP.
    Resolution handles the remaining non-unit interactions.

    WHERE THE LANGUAGE BOUNDARY IS:

    All three operations are term operations:
    - Subsumption: compare two clause-terms structurally (subset check)
    - UP-resolution: compose a unit clause-term with a longer one
    - Extended resolution: introduce a new labeled element (abbreviation)

    The rotation calculus can express all three. Each is a contraction:
    - Subsumption contracts the clause database (fewer terms)
    - UP-resolution contracts individual clauses (shorter terms)
    - Extended resolution contracts the representation (fewer literals per occurrence)

    The UNSAT proof is the sequence of contractions that reaches ground.
    Different contraction strategies produce different proof lengths.
    Finding the shortest proof is itself a search problem — the meta-level
    analogue of finding the best arrangement for SAT.
-/

end RotationCalculus
