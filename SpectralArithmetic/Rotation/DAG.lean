/-
  DAG Arrangements: Shared Subtrees and Memoization
  ===================================================

  Trees enforce independent subtrees — each sub-computation is done once.
  DAGs allow shared subtrees — a sub-computation can be referenced from
  multiple parents. This is the structural difference between
  divide-and-conquer and dynamic programming.

  Implementation: extend Term with `ref(name)` for back-references.
  A `let` binding introduces a named subtree. `ref` dereferences it.
  The result is a DAG (directed acyclic graph) expressed as a term
  with sharing.

  Key question: does sharing reduce the construction cost for problems
  that have overlapping subproblems?
-/

import SpectralArithmetic.Rotation.SATEncoding

namespace RotationCalculus

open Term

/-! ## DAG representation

    Rather than modifying the Term type (which would break all existing
    code), we represent DAGs as terms with an explicit environment
    mapping names to subtrees. A "ref" is encoded as a labeled element
    with a special marker, and the environment resolves it.

    This is a lightweight approach that lets us test the DAG hypothesis
    without restructuring the codebase. -/

/-- A DAG is a term plus an environment mapping names to shared subtrees. -/
structure DAGTerm where
  root : Term
  env : List (ℕ × Term)  -- name → shared subtree
  deriving Repr

/-- Resolve all references in a term using the environment.
    Uses fuel to prevent infinite loops from cyclic references. -/
partial def resolve (env : List (ℕ × Term)) : Term → ℕ → Term
  | t, 0 => t
  | .ground, _ => .ground
  | .pair a .ground, fuel =>
    -- Check if this is a reference (label > 1000 used as ref marker)
    let label := getLabel (.pair a .ground)
    if label ≥ 1000 then
      let refName := label - 1000
      match env.find? fun (n, _) => n == refName with
      | some (_, subtree) => resolve env subtree (fuel - 1)
      | none => .pair a .ground  -- unresolved ref, keep as-is
    else .pair a .ground
  | .pair a b, fuel =>
    .pair (resolve env a (fuel - 1)) (resolve env b (fuel - 1))
  | .observe t, fuel => .observe (resolve env t (fuel - 1))

/-- Create a reference to a named subtree.
    Uses label = 1000 + name as a marker. -/
def ref (name : ℕ) : Term := labeledElement (1000 + name)

/-- Check if a term is a reference. -/
def isRef (t : Term) : Bool := getLabel t ≥ 1000

/-- Get the reference name from a ref term. -/
def refName (t : Term) : ℕ := getLabel t - 1000

/-! ## DAG verification

    Verify a DAG by first resolving all references, then running
    the standard tree verifier. The resolution expands sharing —
    each ref becomes the shared subtree.

    The key insight: the RESOLVED term is a tree (no sharing).
    The DAG is a compressed representation. Verification on the
    resolved tree has the same semantics as tree verification.
    But the DAG may be exponentially smaller than the resolved tree. -/

/-- Verify a DAG: resolve refs, then verify the expanded tree. -/
def verifyDAG (C : Constraint) (dag : DAGTerm) : Bool :=
  let resolved := resolve dag.env dag.root (dag.env.length * 10 + 100)
  verifyTree C resolved

/-- Collect assignments from a DAG (resolve first). -/
def dagAssignment (dag : DAGTerm) : List (ℕ × Bool) :=
  let resolved := resolve dag.env dag.root (dag.env.length * 10 + 100)
  collectAssignment resolved

/-! ## Example: shared sub-computation in SAT

    Consider a SAT instance where the same variable group appears
    in multiple clause clusters. Without sharing, each appearance
    is a separate subtree. With sharing, it's computed once.

    Instance: (x0 OR x1) AND (x1 OR x2) AND (x0 OR x2)
    Variable x1 interacts with both x0 and x2.

    Tree (no sharing):
      pair(pair(x0=T, x1=T), pair(x1=T, x2=T))
      — x1 appears twice, independently

    DAG (with sharing):
      let shared_x1 = literal 1 true in
      pair(pair(x0=T, ref(1)), pair(ref(1), x2=T))
      — x1 computed once, referenced twice -/

-- Tree version: x1 appears in both subtrees independently
def satTreeVersion : Term :=
  .pair (.pair (literal 0 true) (literal 1 true))
        (.pair (literal 1 true) (literal 2 true))

-- DAG version: x1 is shared via reference
def satDAGVersion : DAGTerm where
  root := .pair (.pair (literal 0 true) (ref 1))
                (.pair (ref 1) (literal 2 true))
  env := [(1, literal 1 true)]

-- Both should produce the same assignment
#eval collectAssignment satTreeVersion
#eval dagAssignment satDAGVersion

-- Both should satisfy the triangle formula
#eval verifyTree (satConstraint triangleFormula) satTreeVersion
#eval verifyDAG (satConstraint triangleFormula) satDAGVersion

/-! ## DAG-aware construction

    The key benefit of DAGs: when constructing a satisfying
    arrangement, shared subtrees are solved ONCE. If variable x1
    appears in multiple clause groups, its assignment is determined
    once and reused.

    For tree construction: each subtree independently assigns x1,
    then the root must check consistency. This is wasted work —
    the independent assignments might conflict.

    For DAG construction: x1 is assigned once (in the shared
    subtree). All references see the same value. No consistency
    check needed for shared variables. -/

/-- DAG-aware SAT solver: identify shared variables (those appearing
    in clauses on both sides of a split), create shared refs for them,
    and solve the remaining variables in each subtree independently.

    Shared variables are resolved first, then each subtree only
    needs to solve its LOCAL variables. -/
partial def dagSATSolve (formula : SATFormula)
    (vars : List ℕ)
    : List (List (ℕ × Bool)) × ℕ :=
  match vars with
  | [] => ([[]], 0)
  | [v] =>
    let solutions := [true, false].filterMap fun pol =>
      let assign := [(v, pol)]
      let localClauses := clausesInScope formula [v]
      if satisfiesFormula assign localClauses then some assign
      else none
    (solutions, 2)
  | vs =>
    let mid := vs.length / 2
    let leftVars := vs.take mid
    let rightVars := vs.drop mid
    -- Identify SHARED variables: those appearing in cross-clauses
    let cross := crossClauses formula leftVars rightVars
    let sharedVars := (cross.flatMap fun clause =>
      clause.map fun (v, _) => v).eraseDups
    -- Assign shared variables FIRST (try all combinations)
    let sharedAssigns := allSharedAssignments sharedVars
    -- Solve left and right LOCAL variables (independent of shared)
    let leftLocal := leftVars.filter fun v => !sharedVars.contains v
    let leftFormula := clausesInScope formula leftVars
    let (leftSols, lc) := dagSATSolve leftFormula leftLocal
    let rightLocal := rightVars.filter fun v => !sharedVars.contains v
    let rightFormula := clausesInScope formula rightVars
    let (rightSols, rc) := dagSATSolve rightFormula rightLocal
    -- For each shared assignment, combine with local solutions
    let results := sharedAssigns.flatMap fun shared =>
      if satisfiesFormula shared cross then
        leftSols.flatMap fun lSol =>
          rightSols.filterMap fun rSol =>
            let merged := shared ++ lSol ++ rSol
            if satisfiesFormula merged formula then some merged
            else none
      else []
    let combineCost := sharedAssigns.length *
      leftSols.length * rightSols.length
    (results, lc + rc + combineCost)
where
  allSharedAssignments : List ℕ → List (List (ℕ × Bool))
    | [] => [[]]
    | v :: vs =>
      let rest := allSharedAssignments vs
      rest.flatMap fun a => [(v, true) :: a, (v, false) :: a]

/-- Wrapper for DAG solver. -/
def satDAGDecomp (formula : SATFormula) (nVars : ℕ)
    : Option (List (ℕ × Bool)) × ℕ :=
  let vars := List.range nVars
  let (solutions, cost) := dagSATSolve formula vars
  let valid := solutions.filter fun a => satisfiesFormula a formula
  (valid.head?, cost)

/-! ## Three-way comparison: flat vs tree vs DAG -/

-- Hard path (4 vars, tw=1)
#eval
  let (r, c) := flatBruteForce hardPath 4
  (r, s!"flat: {c}")

#eval
  let (r, c) := satTreeDecomp hardPath 4
  (r, s!"tree: {c}")

#eval
  let (r, c) := satDAGDecomp hardPath 4
  (r, s!"dag: {c}")

-- Triangle formula (3 vars, tw=2, shared variable x1)
#eval
  let (r, c) := flatBruteForce triangleFormula 3
  (r, s!"flat: {c}")

#eval
  let (r, c) := satTreeDecomp triangleFormula 3
  (r, s!"tree: {c}")

#eval
  let (r, c) := satDAGDecomp triangleFormula 3
  (r, s!"dag: {c}")

-- Dense formula (4 vars, tw=3, many shared variables)
#eval
  let (r, c) := flatBruteForce denseFormula 4
  (r, s!"flat: {c}")

#eval
  let (r, c) := satTreeDecomp denseFormula 4
  (r, s!"tree: {c}")

#eval
  let (r, c) := satDAGDecomp denseFormula 4
  (r, s!"dag: {c}")

-- All-negative path (10 vars, tw=0)
#eval
  let (r, c) := flatBruteForce (allNegPath 10) 10
  (r, s!"flat: {c}")

#eval
  let (r, c) := satTreeDecomp (allNegPath 10) 10
  (r, s!"tree: {c}")

#eval
  let (r, c) := satDAGDecomp (allNegPath 10) 10
  (r, s!"dag: {c}")

-- Restrictive instance (10 vars, 5 cross-links)
#eval
  let (r, c) := flatBruteForce (restrictedInstance 10 5) 10
  (r, s!"flat: {c}")

#eval
  let (r, c) := satTreeDecomp (restrictedInstance 10 5) 10
  (r, s!"tree: {c}")

#eval
  let (r, c) := satDAGDecomp (restrictedInstance 10 5) 10
  (r, s!"dag: {c}")

/-! ## Assessment

    The DAG solver differs from the tree solver in one key way:
    it identifies SHARED variables (those in cross-partition clauses)
    and assigns them BEFORE splitting into subtrees. This means:

    1. Shared variables are assigned globally (tried all combinations)
    2. Local variables are assigned per-subtree (independent)
    3. No consistency check needed between subtrees for shared vars

    Expected behavior:
    - For tw=0 (no sharing): DAG = tree (no shared variables)
    - For tw=1 (path): DAG slightly better (1 shared var per split)
    - For tw=k: DAG tries 2^k shared combinations, then solves
      subtrees independently. Cost = 2^k × (subtree costs).
      Better than tree when 2^k << cross-clause filtering cost.
    - For tw=n: all variables are shared, DAG = flat brute force -/

end RotationCalculus
