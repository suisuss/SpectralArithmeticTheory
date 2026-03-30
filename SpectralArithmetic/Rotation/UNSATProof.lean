/-
  UNSAT in the Rotation Calculus
  ===============================

  Everything so far has been SAT: find an arrangement that contracts.
  UNSAT is structurally different: prove NO arrangement contracts.

  Questions this file investigates:
  1. What do #0 and #1 produce on UNSAT instances?
  2. What does an UNSAT proof look like as rotation calculus terms?
  3. Can we express the proof of non-contractibility WITHIN the language?

  The key gap: a SAT certificate is a selector term (small, checkable).
  An UNSAT proof must cover the ENTIRE arrangement space — it's a
  statement about ALL possible selectors, not a specific one.
-/

import SpectralArithmetic.Rotation.MetaRewriting
import SpectralArithmetic.Rotation.SelfContained

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Part 1: What happens on UNSAT instances -/

/-! ### Trivial UNSAT: (x0) AND (NOT x0) -/

#eval! do
  IO.println "=== UNSAT BEHAVIOR ==="
  IO.println ""
  IO.println "--- Trivial UNSAT: (x0) AND (NOT x0) ---"
  let f : SATFormula := [[(0, true)], [(0, false)]]
  let satC := satConstraint f
  -- Try both arrangements
  let t1 := Term.pair (literal 0 true) (literal 0 false)
  let t2 := Term.pair (literal 0 false) (literal 0 true)
  IO.println s!"  pair(T,F): {verifyTree satC t1}"
  IO.println s!"  pair(F,T): {verifyTree satC t2}"
  -- Count valid trees
  let lits := [literal 0 true, literal 0 false]
  let (valid, total) := countValidTrees satC lits
  IO.println s!"  valid/total: {valid}/{total}"
  -- Selector search
  let (found, tried) := selectorSearch satC t1 4
  IO.println s!"  selector search: found={found.isSome} tried={tried}"

/-! ### PHP(3,2) via CDCL -/

#eval! do
  IO.println ""
  IO.println "--- PHP(3,2) via CDCL ---"
  let php := pigeonhole 3 2
  let (found, cost, learned) := cdclSearch php (List.range 6) []
  IO.println s!"  found={found} cost={cost} \
    learned={List.length learned}"
  IO.println "  learned clauses:"
  let mut i := 0
  for c in learned do
    IO.println s!"    {i}: {c}"
    i := i + 1

/-! ### PHP(3,2) via pipeline trace -/

#eval! do
  IO.println ""
  IO.println "--- PHP(3,2) pipeline trajectory ---"
  let php := pigeonhole 3 2
  let ms := buildTrajectory php 6
  let mp := metaProfile ms.trajectory
  IO.println s!"  events={mp.totalEvents} \
    cascade={mp.nCascade}({mp.cascadeTotal}v) \
    search={mp.nSearch} cycles={mp.nConflictCycle} \
    abs={mp.nAbstraction}"
  for pt in ms.trajectory do
    IO.println s!"    {showMetaEvent pt.event}"
  -- Also the raw trace
  IO.println ""
  IO.println "  Raw trace:"
  let (_, trace, _) := runPipeline php 6
  let mut i := 0
  for step in trace do
    IO.println s!"    {i}: {stepTag step}"
    i := i + 1

/-! ## Part 2: Exhaustive tree verification

    For UNSAT, we need to show ALL arrangements fail.
    The rotation calculus version: try every tree shape
    and every leaf placement, verify each. -/

/-- Exhaustive UNSAT check: try all trees, return failure witnesses.
    Each failed arrangement produces a (tree, stuck_pair).
    If ALL fail, the formula is UNSAT. -/
def exhaustiveUNSAT (C : Constraint) (elements : List Term)
    (maxPerms : ℕ := 1000)
    : List (List ℕ × String) × ℕ :=
  let ps := (perms elements).take maxPerms
  let failures := ps.flatMap fun perm =>
    (allTrees perm).map fun tree =>
      let ok := verifyTree C tree
      let labs := leafLabels tree
      if ok then (labs, "SAT")
      else
        -- Find where it fails
        let reason := match tree with
          | .pair a b =>
            if C.check a b then "inner-fail"
            else s!"root-fail"
          | _ => "degenerate"
        (labs, reason)
  let total := failures.length
  let satCount := failures.filter (fun (_, s) => s == "SAT")
    |>.length
  if satCount > 0 then
    (failures.filter (fun (_, s) => s == "SAT") |>.take 3, total)
  else
    (failures.take 5, total)

#eval! do
  IO.println ""
  IO.println "=== EXHAUSTIVE UNSAT PROOF ==="
  IO.println ""
  -- Trivial UNSAT
  IO.println "--- (x0) AND (NOT x0) ---"
  let f : SATFormula := [[(0, true)], [(0, false)]]
  let satC := satConstraint f
  let lits := [literal 0 true, literal 0 false]
  let (witnesses, total) := exhaustiveUNSAT satC lits
  IO.println s!"  total arrangements: {total}"
  IO.println s!"  sample failures:"
  for (labs, reason) in witnesses do
    IO.println s!"    {labs}: {reason}"
  -- Small SAT for comparison
  IO.println ""
  IO.println "--- SAT: (x0 OR x1) ---"
  let f2 : SATFormula := [[(0, true), (1, true)]]
  let satC2 := satConstraint f2
  let lits2 := [literal 0 true, literal 0 false,
                literal 1 true, literal 1 false]
  let (witnesses2, total2) := exhaustiveUNSAT satC2 lits2
  IO.println s!"  total arrangements: {total2}"
  IO.println s!"  sample results:"
  for (labs, reason) in witnesses2 do
    IO.println s!"    {labs}: {reason}"

/-! ## Part 3: The UNSAT proof as a term

    For SAT, the certificate is a selector term (small).
    For UNSAT, what is the proof?

    Option 1: the proof is the list of ALL failures.
    Size = Catalan(n) x n! x (failure reason per arrangement).
    This is exponential. Not useful.

    Option 2: the proof is a RESOLUTION derivation.
    Each step combines two constraint failures to derive
    a stronger constraint failure. The derivation terminates
    when the empty constraint (contradiction) is derived.

    Option 3: the proof is a term that CONTRACTS to ground
    under a META-constraint encoding "all arrangements fail."
    The meta-constraint checks: for every possible leaf placement
    at this node, the constraint fails.

    Option 3 is the rotation calculus native approach. -/

/-- A refutation term: encodes why every arrangement fails.
    At each tree node, the refutation carries evidence that
    both subtree assignments lead to constraint failure. -/
inductive Refutation where
  | leaf : Term → Refutation  -- a specific literal assignment
  | split : Refutation → Refutation → Refutation  -- both branches fail
  | conflict : Term → Term → Refutation  -- (a, b) violates constraint
  deriving Repr

/-- Build a refutation by exhaustive tree search.
    At each split, try all ways to partition elements.
    If EVERY partition fails, record why. -/
partial def buildRefutation (C : Constraint) (elements : List Term)
    : Option Refutation :=
  match elements with
  | [] => some (.leaf .ground)
  | [x] => some (.leaf x)
  | xs =>
    -- Try all splits
    let n := xs.length
    let splits := List.range (n - 1) |>.map fun i =>
      (xs.take (i + 1), xs.drop (i + 1))
    -- For UNSAT, ALL splits must fail
    let allFail := splits.all fun (left, right) =>
      let leftTrees := allTrees left
      let rightTrees := allTrees right
      let pairs := leftTrees.flatMap fun lt =>
        rightTrees.map fun rt => (lt, rt)
      pairs.all fun (lt, rt) => !C.check lt rt
    if allFail then
      -- Every split fails at the root level
      -- Pick the first split as the refutation witness
      match splits with
      | (left, right) :: _ =>
        let leftRef := buildRefutation C left
        let rightRef := buildRefutation C right
        match leftRef, rightRef with
        | some lr, some rr => some (.split lr rr)
        | _, _ => some (.conflict (fromList left) (fromList right))
      | _ => none
    else
      -- Some split succeeds at root — need to go deeper
      -- Check if any complete tree works
      let anyWorks := (allTrees xs).any fun t => verifyTree C t
      if anyWorks then none  -- SAT, not UNSAT
      else
        -- UNSAT but can't prove at root level alone
        -- All splits pass at root but fail deeper
        some (.conflict (fromList xs) .ground)

/-- Count nodes in a refutation. -/
def Refutation.size : Refutation → ℕ
  | .leaf _ => 1
  | .split a b => 1 + a.size + b.size
  | .conflict _ _ => 1

#eval! do
  IO.println ""
  IO.println "=== REFUTATION TERMS ==="
  IO.println ""
  -- Trivial UNSAT
  IO.println "--- (x0) AND (NOT x0) ---"
  let f : SATFormula := [[(0, true)], [(0, false)]]
  let satC := satConstraint f
  let lits := [literal 0 true, literal 0 false]
  let ref := buildRefutation satC lits
  match ref with
  | some r =>
    IO.println s!"  refutation size: {r.size}"
    IO.println s!"  refutation: {repr r}"
  | none =>
    IO.println "  no refutation (SAT)"
  -- SAT instance (should return none)
  IO.println ""
  IO.println "--- SAT: (x0 OR x1) ---"
  let f2 : SATFormula := [[(0, true), (1, true)]]
  let satC2 := satConstraint f2
  let lits2 := [literal 0 true, literal 1 true]
  let ref2 := buildRefutation satC2 lits2
  match ref2 with
  | some r =>
    IO.println s!"  refutation size: {r.size}"
  | none =>
    IO.println "  no refutation (SAT) -- correct"
  -- 3-literal UNSAT
  IO.println ""
  IO.println "--- UNSAT: (x0) AND (NOT x0) AND (x1) ---"
  let f3 : SATFormula :=
    [[(0, true)], [(0, false)], [(1, true)]]
  let satC3 := satConstraint f3
  let lits3 := [literal 0 true, literal 0 false,
                literal 1 true]
  let ref3 := buildRefutation satC3 lits3
  match ref3 with
  | some r =>
    IO.println s!"  refutation size: {r.size}"
  | none =>
    IO.println "  no refutation -- SAT or can't prove at root"

/-! ## Assessment

    WHAT THE DATA SHOWS:

    SAT proof = selector term. Small (O(tree depth)).
    Checkable in linear time (one tree fold).

    UNSAT proof = ???. Three options explored:

    1. EXHAUSTIVE ENUMERATION: try all Catalan(n) x n! arrangements.
       This IS the brute-force proof. Size = exponential.
       Not a rotation calculus term — it's external computation.

    2. REFUTATION TREE: a tree where each node records WHY a
       partition fails. Size = polynomial in the refutation depth,
       but building it requires exhaustive search.

    3. RESOLUTION DERIVATION: not yet implemented. This is what
       CDCL produces — a sequence of learned clauses that derive
       the empty clause. Each learned clause is a constraint failure
       that prunes future search.

    THE GAP:

    In the rotation calculus, SAT has a native certificate
    (the selector term = the arrangement that contracts).
    UNSAT has no native certificate. The refutation must
    cover ALL arrangements, and the rotation calculus has no
    primitive for universal quantification over arrangements.

    This IS the P vs NP gap seen from the proof side:
    - SAT certificate: exists an arrangement → here it is (term)
    - UNSAT proof: for all arrangements → they all fail (???)

    The existential is a term. The universal is... what?
    In the rotation calculus, the universal would need to be
    a term that, when rotated, checks every possible arrangement.
    But "every possible arrangement" is exponential in the number
    of elements. The rotation rule processes one arrangement at
    a time. There is no rotation rule for "for all arrangements."

    This is where the language hits its boundary. To express
    UNSAT natively, you'd need either:
    - A quantifier over arrangements (making the language second-order)
    - A proof system that derives contradiction from constraint
      interactions (resolution/CDCL)
    - A structural argument that the constraint graph itself
      forces all arrangements to fail (graph-theoretic)

    The third option is most aligned with the rotation calculus:
    instead of searching arrangements, analyze the CONSTRAINT TERM
    (from Part C of SelfContained.lean) and derive a structural
    impossibility. The constraint term encodes the problem. If the
    constraint term has a property that provably prevents any
    arrangement from contracting, that property IS the UNSAT proof.
-/

end RotationCalculus
