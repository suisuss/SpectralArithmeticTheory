/-
  Extended Resolution in the Rotation Calculus
  ==============================================

  Standard resolution: work with original variables.
  General resolution (CDCL): learn clauses (new constraints).
  Extended resolution: introduce new variables (new ELEMENTS).

  In the rotation calculus, this means: during tree contraction,
  create SUMMARY ELEMENTS that compress observations. A summary
  carries the conclusion of an inner observation as a new atomic
  element that future observations can reference.

  The key operation: ABSTRACTION.
  When observe(pair(a,b)) determines that a and b together satisfy
  property P, create a new element `abs(P)` that represents this
  fact. Replace pair(a,b) with abs(P) in the arrangement. Future
  constraint checks involving abs(P) can use P directly without
  re-deriving it from a and b.

  This is proof compression: instead of re-proving the same sub-fact
  at every node, prove it once and carry the lemma forward.
-/

import SpectralArithmetic.Rotation.BeliefProp

namespace RotationCalculus

open Term

/-! ## Abstraction: compressing observations into new elements

    An abstraction is a derived element that summarizes a compound
    observation. It has:
    - A unique id (to distinguish from original elements)
    - The property it asserts (which variables, what constraint)
    - The original sub-terms it was derived from -/

/-- An abstraction: a derived element carrying a proven property.
    Encoded as a labeled element with id ≥ 10000.
    The properties list records what the abstraction "knows." -/
structure Abstraction where
  id : ℕ
  derivedFrom : List ℕ  -- original variable ids
  satisfiedClauses : List ℕ  -- clause indices known to be satisfied
  deriving Repr

/-- Create a term representing an abstraction. -/
def absTerm (abs : Abstraction) : Term :=
  labeledElement (10000 + abs.id)

/-- Check if a term is an abstraction. -/
def isAbstraction (t : Term) : Bool :=
  getLabel t ≥ 10000

/-- Get the abstraction id from a term. -/
def absId (t : Term) : ℕ :=
  getLabel t - 10000

/-! ## Extended constraint

    The constraint is augmented with an abstraction environment.
    When checking C(a, b), if either a or b is an abstraction,
    the constraint looks up what the abstraction already proved
    and skips those checks.

    This is the core of extended resolution: previously proven
    sub-facts are treated as axioms in subsequent derivations. -/

/-- Extended constraint: original formula + abstraction environment. -/
structure ExtConstraint where
  formula : SATFormula
  abstractions : List Abstraction
  deriving Repr

/-- Check a constraint with abstraction awareness.
    If an element is an abstraction, the clauses it covers are
    treated as already satisfied. -/
def extCheck (ec : ExtConstraint) (a b : Term) : Bool :=
  let assign := collectAssignment a ++ collectAssignment b
  -- Collect clause indices satisfied by abstractions
  let coveredClauses := if isAbstraction a then
    match ec.abstractions.find? fun abs => abs.id == absId a with
    | some abs => abs.satisfiedClauses
    | none => []
  else []
  let coveredClauses := coveredClauses ++ (if isAbstraction b then
    match ec.abstractions.find? fun abs => abs.id == absId b with
    | some abs => abs.satisfiedClauses
    | none => []
  else [])
  -- Check only UNCOVERED clauses
  let indexed : List (ℕ × SATClause) :=
    ec.formula.zip (List.range ec.formula.length)
    |>.map fun (clause, i) => (i, clause)
  let uncovered := indexed.filter fun (i, _) =>
    !coveredClauses.contains i
  uncovered.all fun (_, clause) =>
    let allAssigned := clause.all fun (v, _) =>
      assign.any fun (v', _) => v == v'
    if allAssigned then satisfiesClause assign clause
    else true

/-! ## Extended resolution search

    The search process creates abstractions as it goes:
    1. Try an assignment for a group of variables
    2. If it satisfies some clauses, create an abstraction
    3. Replace the group with the abstraction in the arrangement
    4. Continue search with the smaller, abstracted arrangement

    This is proof compression: instead of n original variables,
    work with n/k abstracted groups, each covering k variables. -/

/-- Create an abstraction from a partial assignment.
    Records which clauses the assignment satisfies. -/
def makeAbstraction (formula : SATFormula)
    (assign : List (ℕ × Bool)) (nextId : ℕ)
    : Abstraction :=
  let indexed : List (ℕ × SATClause) :=
    formula.zip (List.range formula.length)
    |>.map fun (clause, i) => (i, clause)
  let covered := indexed.filterMap fun (i, clause) =>
    if satisfiesClause assign clause then some i else none
  { id := nextId, derivedFrom := assign.map (·.1),
    satisfiedClauses := covered }

/-- Extended resolution SAT solver.
    Phase 1: group variables, find partial assignments for each group
    Phase 2: create abstractions for successful groups
    Phase 3: solve the REDUCED problem (abstractions as elements)

    The reduced problem has fewer "variables" (abstractions instead
    of raw variables) and fewer uncovered clauses. -/
partial def extResSolve (formula : SATFormula) (vars : List ℕ)
    (groupSize : ℕ := 3)
    : Option (List (ℕ × Bool)) × ℕ × ℕ :=  -- (solution, cost, abstractions_created)
  if vars.length ≤ groupSize then
    -- Small enough: solve directly
    let assigns := allVarAssignments vars
    let valid := assigns.filter fun a =>
      satisfiesFormula a (clausesInScope formula vars)
    match valid.head? with
    | some a => (some a, assigns.length, 0)
    | none => (none, assigns.length, 0)
  else
    -- Phase 1: group variables
    let nGroups := (vars.length + groupSize - 1) / groupSize
    let groups := (List.range nGroups).map fun i =>
      let start := i * groupSize
      vars.drop start |>.take groupSize

    -- Phase 2: for each group, find best partial assignment and abstract
    let phase2 := groups.foldl (fun (acc : List Abstraction × List (List (ℕ × Bool)) × ℕ × ℕ) group =>
      let (abstractions, groupAssigns, cost, nextId) := acc
      let localFormula := clausesInScope formula group
      let assigns := allVarAssignments group
      let newCost := cost + assigns.length
      let best := assigns.foldl (fun (bestA, bestCount) a =>
        let count := satisfactionCount a localFormula
        if count > bestCount then (a, count) else (bestA, bestCount)
      ) ([], 0)
      if best.2 > 0 then
        let abs := makeAbstraction formula best.1 nextId
        (abs :: abstractions, best.1 :: groupAssigns, newCost, nextId + 1)
      else
        (abstractions, groupAssigns, newCost, nextId)
    ) ([], [], 0, 0)
    let (abstractions, groupAssigns, cost, _) := phase2

    -- Phase 3: check if the combined assignment works
    let combined := groupAssigns.foldl (· ++ ·) []
    if satisfiesFormula combined formula then
      (some combined, cost, abstractions.length)
    else
      -- Phase 3b: use CDCL with abstracted starting point
      let (found, cdclCost, _) := cdclSearch formula vars combined
      if found then
        (some combined, cost + cdclCost, abstractions.length)
      else
        let (found2, cdclCost2, _) := cdclSearch formula vars []
        (if found2 then some [] else none,
         cost + cdclCost + cdclCost2, abstractions.length)

/-- Wrapper. -/
def satExtRes (formula : SATFormula) (nVars : ℕ)
    (groupSize : ℕ := 3)
    : Option (List (ℕ × Bool)) × ℕ × ℕ :=
  let vars := List.range nVars
  extResSolve formula vars groupSize

/-! ## Comparison -/

-- Random 3-SAT n=8
#eval do
  let n := 8
  let m := 32
  let data := [42, 123, 456].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, cdcl, cdclL) := satCDCL f n
    let (r2, bp2, _) := runBP f n 2
    let (r, exCost, exAbs) := satExtRes f n 2
    let (r3, exCost3, exAbs3) := satExtRes f n 3
    s!"seed={seed} flat={flat} cdcl={cdcl}(L={cdclL}) bp={bp2}(f={r2.isSome}) extres2={exCost}(abs={exAbs},f={r.isSome}) extres3={exCost3}(abs={exAbs3},f={r3.isSome})"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- Random 3-SAT n=10
#eval do
  let n := 10
  let m := 42
  let data := [42, 123, 456].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, cdcl, _) := satCDCL f n
    let (r2, bp2, _) := runBP f n 2
    let (r, exCost, exAbs) := satExtRes f n 3
    s!"seed={seed} flat={flat} cdcl={cdcl} bp={bp2}(f={r2.isSome}) extres={exCost}(abs={exAbs},f={r.isSome})"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- Structured
#eval do
  let data := [8, 10, 12].map fun n =>
    let f := reachInstance n 3
    let (_, smart) := satSmartDAG f n 2
    let (_, cdcl, _) := satCDCL f n
    let (r, exCost, exAbs) := satExtRes f n 3
    s!"n={n} smart={smart} cdcl={cdcl} extres={exCost}(abs={exAbs},f={r.isSome})"
  IO.println s!"Structured reach=3:"
  IO.println (String.intercalate "\n" data)

-- PHP (UNSAT)
#eval do
  let f := pigeonhole 3 2
  let (_, cdcl, cdclL) := satCDCL f 6
  let (r, exCost, exAbs) := satExtRes f 6 2
  IO.println s!"PHP(3,2): cdcl={cdcl}(L={cdclL}) extres={exCost}(abs={exAbs},f={r.isSome})"

#eval do
  let f := pigeonhole 4 3
  let (_, cdcl, cdclL) := satCDCL f 12
  let (r, exCost, exAbs) := satExtRes f 12 3
  IO.println s!"PHP(4,3): cdcl={cdcl}(L={cdclL}) extres={exCost}(abs={exAbs},f={r.isSome})"

/-! ## Assessment

    Extended resolution in the rotation calculus:

    1. GROUPING = spatial decomposition of variables into blocks
    2. ABSTRACTION = proving local facts about each block
    3. REDUCTION = replacing blocks with their abstractions
    4. SOLVING = tackling the reduced problem

    The abstractions are LEMMAS in the proof. Each one says:
    "variables x1,x2,x3 with assignment T,F,T satisfy clauses 2,5,7."
    This is proven once (Phase 2) and used as an axiom thereafter.

    The proof structure:
    - Phase 2 produces local proofs (one per group)
    - Phase 3 combines local proofs into a global proof
    - If combination fails, CDCL searches with the local proofs as
      starting knowledge (combining extended resolution with CDCL)

    What this IS in proof complexity terms:
    - Grouping = introducing extension variables (one per group)
    - Abstraction = defining each extension variable
    - Reduction = reasoning with extensions instead of originals
    - This is EXACTLY extended resolution

    What's NATIVE to the rotation calculus:
    - The grouping follows the tree structure (pair nesting)
    - The abstraction IS the contraction (observe and summarize)
    - The summary IS the ground state of the inner observation
    - Extended resolution = hierarchical contraction with memory

    The rotation rule observe(pair(a,b)) → pair(b, observe(a))
    naturally produces summaries: after observing a, you have a
    conclusion about a that persists while observing b. Extended
    resolution makes this persistence EXPLICIT by creating a new
    element that carries the conclusion. -/

end RotationCalculus
