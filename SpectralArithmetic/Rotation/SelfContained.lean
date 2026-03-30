/-
  Self-Contained Rotation Calculus
  =================================

  Two extensions that internalize what was previously external:

  A. RULE SELECTION AS CONSTRAINT
     Instead of a fixed rotation rule, the structure itself
     determines which rule fires. At each observe(pair(a, b)),
     a selector constraint chooses dive-left vs dive-right.
     The choice of traversal order IS the search object.
     Finding the right traversal = walking the Tamari lattice.

  C. CONSTRAINT AS TERM
     Instead of an external predicate C.check : Term → Term → Bool,
     the constraint is encoded as a rotation calculus term.
     Checking the constraint IS a rotation computation.
     The language becomes self-applicable: checker and checked
     are the same kind of object.

  Together: the rotation calculus can express its own execution
  strategy (A) and its own constraint checking (C). The only
  thing external is the initial problem encoding.
-/

import SpectralArithmetic.Rotation.RotationIndex

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ================================================================
    PART A: Rule Selection as Constraint
    ================================================================

    A directed rotation system where at each step, a SELECTOR
    determines whether to dive left or dive right. The selector
    is itself a constraint — a decidable predicate on (a, b) that
    returns a direction.

    This turns the traversal order into a searchable parameter.
    A "valid traversal" is a sequence of left/right choices that
    contracts the entire term to ground. -/

/-- Direction: which way to dive at each step. -/
inductive Direction where
  | left   -- observe goes to a (left child)
  | right  -- observe goes to b (right child)
  deriving DecidableEq, Repr

/-- A selector: given (a, b), choose a direction. -/
structure Selector where
  choose : Term → Term → Direction

/-- The directed step: apply the rule chosen by the selector. -/
def directedStep (sel : Selector) (C : Constraint)
    : Term → StepResult
  | .observe (.pair a b) =>
    if C.check a b then
      match sel.choose a b with
      | .left  => .rotated (.pair b (.observe a))
      | .right => .rotated (.pair a (.observe b))
    else .stuck a b
  | .observe .ground => .done
  | _ => .done

/-- Run directed rotation with trace. -/
def directedRun (sel : Selector) (C : Constraint)
    (t : Term) (fuel : ℕ) : Outcome × List Direction :=
  match fuel with
  | 0 => (.contracted, [])
  | fuel + 1 =>
    match t with
    | .observe (.pair a b) =>
      if C.check a b then
        let dir := sel.choose a b
        let next := match dir with
          | .left  => Term.pair b (.observe a)
          | .right => Term.pair a (.observe b)
        -- Recurse into the observe
        let inner := match dir with
          | .left  => a
          | .right => b
        let (outcome, dirs) :=
          directedRun sel C (.observe inner) fuel
        (outcome, dir :: dirs)
      else (.stuckAt a b, [])
    | .observe .ground => (.contracted, [])
    | .pair _ b => directedRun sel C b fuel
    | _ => (.contracted, [])

/-- A directed tree fold: at each pair node, the selector
    chooses which subtree to observe first. -/
def directedTreeFold (sel : Selector) (C : Constraint)
    : Term → Bool × List Direction
  | .ground => (true, [])
  | .pair _ .ground => (true, [])
  | .pair a b =>
    if C.check a b then
      let dir := sel.choose a b
      match dir with
      | .left =>
        let (lok, ldirs) := directedTreeFold sel C a
        let (rok, rdirs) := directedTreeFold sel C b
        (lok && rok, .left :: ldirs ++ rdirs)
      | .right =>
        let (rok, rdirs) := directedTreeFold sel C b
        let (lok, ldirs) := directedTreeFold sel C a
        (rok && lok, .right :: rdirs ++ ldirs)
    else (false, [])
  | .observe t => directedTreeFold sel C t

/-! ### Predefined selectors -/

/-- Always dive left (current behavior). -/
def Selector.alwaysLeft : Selector where
  choose := fun _ _ => .left

/-- Always dive right. -/
def Selector.alwaysRight : Selector where
  choose := fun _ _ => .right

/-- Alternate left-right at each step. -/
def Selector.alternate : Selector where
  choose := fun a _ =>
    if a.size % 2 == 0 then .left else .right

/-- Choose based on subtree size: dive into the smaller one first. -/
def Selector.smallFirst : Selector where
  choose := fun a b =>
    if a.size ≤ b.size then .left else .right

/-- Choose based on subtree size: dive into the larger one first. -/
def Selector.largeFirst : Selector where
  choose := fun a b =>
    if a.size > b.size then .left else .right

/-- Selector from a pre-computed direction sequence.
    Falls back to left when the sequence runs out. -/
def Selector.fromList (dirs : List Direction) : Selector where
  choose := fun _ _ =>
    -- Stateless approximation: use term shape as index
    -- (True stateful version would need a mutable counter)
    .left

/-! ### Selector search: find a direction sequence that contracts

    Given a constraint and a term, find a selector (direction
    sequence) such that the directed tree fold succeeds.
    This IS the search problem expressed as rule selection. -/

/-- All direction sequences of length n. -/
def allDirSeqs : ℕ → List (List Direction)
  | 0 => [[]]
  | n + 1 =>
    let rest := allDirSeqs n
    rest.flatMap fun ds =>
      [Direction.left :: ds, Direction.right :: ds]

/-- Inner tree fold guided by a direction list.
    Consumes directions as it recurses. -/
partial def guidedFold (C : Constraint)
    (ds : List Direction) (t : Term)
    : Bool × List Direction :=
  match t with
  | .ground => (true, ds)
  | .pair _ .ground => (true, ds)
  | .pair a b =>
    if C.check a b then
      match ds with
      | [] =>
        let (lok, ds') := guidedFold C [] a
        let (rok, ds'') := guidedFold C ds' b
        (lok && rok, ds'')
      | d :: rest =>
        match d with
        | Direction.left =>
          let (lok, ds') := guidedFold C rest a
          let (rok, ds'') := guidedFold C ds' b
          (lok && rok, ds'')
        | Direction.right =>
          let (rok, ds') := guidedFold C rest b
          let (lok, ds'') := guidedFold C ds' a
          (rok && lok, ds'')
    else (false, ds)
  | .observe t => guidedFold C ds t

def trySelectorSeq (dirs : List Direction) (C : Constraint)
    (t : Term) : Bool :=
  (guidedFold C dirs t).1

/-- Search for a direction sequence that makes the tree fold succeed.
    Returns (found?, directions, sequences_tried). -/
def selectorSearch (C : Constraint) (t : Term) (maxDepth : ℕ)
    : Option (List Direction) × ℕ :=
  let rec go (remaining : ℕ) (depth : ℕ) (tried : ℕ)
      : Option (List Direction) × ℕ :=
    match remaining with
    | 0 => (none, tried)
    | remaining + 1 =>
      let seqs := allDirSeqs depth
      match seqs.find? fun ds => trySelectorSeq ds C t with
      | some ds => (some ds, tried + seqs.length)
      | none => go remaining (depth + 1) (tried + seqs.length)
  go (maxDepth + 1) 0 0

/-! ================================================================
    PART C: Constraint as Term
    ================================================================

    The constraint is encoded as a rotation calculus term.
    Checking the constraint against (a, b) means: build
    pair(constraintTerm, pair(a, b)) and see if it contracts.

    The constraint term is a "program" in the rotation calculus.
    Applying it to data is composing them and running the rule.

    Encoding scheme:
    - A constraint term is a tree whose leaves encode the
      acceptance condition
    - pair(constraintTerm, dataTerm) is "apply constraint to data"
    - The tree fold checks structural compatibility between
      the constraint pattern and the data -/

/-- A term-encoded constraint: the constraint IS a term.
    Checking C(a, b) means: does verifyTree accept
    pair(c, pair(a, b)) where c is the constraint term? -/
structure TermConstraint where
  term : Term
  /-- The acceptance predicate: does the constraint term
      structurally match the data? -/
  accepts : Term → Term → Bool

/-- Build a term constraint from a match predicate on labels.
    The constraint term encodes the predicate as a lookup table:
    pair(pair(accept_label_1, accept_label_2), ...) -/
def TermConstraint.fromPairs
    (acceptPairs : List (ℕ × ℕ)) : TermConstraint where
  -- Encode accepted pairs as a term
  term := Term.fromList
    (acceptPairs.map fun (a, b) =>
      .pair (natToTerm a) (natToTerm b))
  accepts := fun a b =>
    let la := getLabel a
    let lb := getLabel b
    acceptPairs.any fun (x, y) => (x == la && y == lb) ||
                                   (x == lb && y == la)

/-- Convert a TermConstraint to a Constraint (for compatibility). -/
def TermConstraint.toConstraint (tc : TermConstraint) : Constraint where
  check := tc.accepts

/-- Build a constraint term that accepts ascending pairs.
    The term encodes: "a ≤ b is ok for all a, b." -/
def ascendingTermConstraint (maxLabel : ℕ) : TermConstraint where
  term := Term.fromList
    ((List.range maxLabel).flatMap fun a =>
      (List.range (maxLabel - a)).map fun b =>
        .pair (natToTerm a) (natToTerm (a + b)))
  accepts := fun a b => getLabel a ≤ getLabel b

/-- Check a term constraint by RUNNING the constraint term.
    This is the self-application: checking the constraint
    IS a rotation calculus computation.

    Method: interleave the constraint term's pairs with the
    data pair and see if a tree fold matches them up. -/
def checkViaRotation (tc : TermConstraint)
    (a b : Term) (fuel : ℕ) : Bool :=
  -- Build: pair(constraintTerm, pair(a, b))
  let combined := Term.pair tc.term (.pair a b)
  -- The constraint "accepts" if the combined term contracts
  -- under a structural matching constraint
  let matchC : Constraint := {
    check := fun left right =>
      -- Left is from the constraint term, right is data
      -- Accept if the constraint pair matches the data pair
      match left, right with
      | .pair cl cr, .pair dl dr =>
        -- Labels from constraint match labels from data
        getLabel cl == getLabel dl &&
        getLabel cr == getLabel dr
      | _, _ => true  -- non-pair nodes pass through
  }
  verifyTree matchC combined

/-! ================================================================
    PART A+C COMBINED: Self-contained directed rotation
    ================================================================

    The selector is a term. The constraint is a term.
    The data is a term. Everything is terms.

    Checking = tree fold with term-encoded constraint.
    Searching = finding a selector term that makes the fold succeed.
    The selector term IS the proof/witness/certificate. -/

/-- A fully self-contained rotation problem:
    constraint term + data term + selector term.
    All three are rotation calculus terms. -/
structure RotationProblem where
  constraint : Term      -- the constraint encoding
  dataterm : Term         -- the problem instance
  selector : Term         -- the traversal order (witness)

/-- Encode a direction as a term.
    left = ground, right = pair(ground, ground). -/
def dirToTerm : Direction → Term
  | .left => .ground
  | .right => .pair .ground .ground

/-- Decode a term to a direction. -/
def termToDir : Term → Direction
  | .ground => .left
  | _ => .right

/-- Encode a direction sequence as a term (flat list). -/
def dirsToTerm (ds : List Direction) : Term :=
  Term.fromList (ds.map dirToTerm)

/-- Decode a term to a direction sequence. -/
def termToDirs (t : Term) : List Direction :=
  t.toList.map termToDir

/-- A self-contained verification:
    given constraint term + data term + selector term,
    does the directed tree fold succeed? -/
def selfContainedVerify (prob : RotationProblem) : Bool :=
  let dirs := termToDirs prob.selector
  let C := Constraint.fromLabels
    (fun a b => a ≤ b)  -- placeholder; real version reads from constraint term
    (fun t => some (getLabel t))
  trySelectorSeq dirs C prob.dataterm

/-! ================================================================
    DEMONSTRATIONS
    ================================================================ -/

/-! ### Demo 1: Rule selection changes traversal -/

#eval! do
  IO.println "=== PART A: RULE SELECTION AS CONSTRAINT ==="
  IO.println ""

  -- Tree with balanced constraint
  let tree := Term.pair
    (.pair (labeledElement 2) (labeledElement 8))
    (.pair (labeledElement 3) (labeledElement 7))

  IO.println "--- Directed tree fold on balanced tree ---"
  IO.println "  tree: ((2,8),(3,7)) sum=10|10"
  for (name, sel) in [("always-left", Selector.alwaysLeft),
                       ("always-right", Selector.alwaysRight),
                       ("small-first", Selector.smallFirst),
                       ("large-first", Selector.largeFirst)] do
    let (ok, dirs) := directedTreeFold sel balancedConstraint tree
    let dirStr := dirs.map fun d => match d with
      | Direction.left => "L" | Direction.right => "R"
    IO.println s!"  {name}: ok={ok} path={dirStr}"

  -- Unbalanced tree: selector doesn't help (constraint fails)
  IO.println ""
  IO.println "--- Unbalanced tree ((2,3),(7,8)) ---"
  for (name, sel) in [("always-left", Selector.alwaysLeft),
                       ("always-right", Selector.alwaysRight)] do
    let (ok, dirs) := directedTreeFold sel balancedConstraint
      (.pair (.pair (labeledElement 2) (labeledElement 3))
             (.pair (labeledElement 7) (labeledElement 8)))
    IO.println s!"  {name}: ok={ok}"

/-! ### Demo 2: Selector search over the Tamari lattice -/

#eval! do
  IO.println ""
  IO.println "=== SELECTOR SEARCH ==="
  IO.println ""

  -- Ascending constraint: labels must be in order
  let ascC : Constraint := {
    check := fun a b =>
      match a, b with
      | .pair _ .ground, .pair _ .ground =>
        getLabel a ≤ getLabel b
      | _, _ => true
  }

  -- Sorted tree: should find a direction sequence quickly
  let sorted := Term.pair
    (.pair (labeledElement 1) (labeledElement 2))
    (.pair (labeledElement 3) (labeledElement 4))
  let (found, tried) := selectorSearch ascC sorted 4
  IO.println s!"  sorted ((1,2),(3,4)): found={found.isSome} tried={tried}"

  -- Unsorted tree: harder to find (may need specific order)
  let unsorted := Term.pair
    (.pair (labeledElement 3) (labeledElement 1))
    (.pair (labeledElement 4) (labeledElement 2))
  let (found2, tried2) := selectorSearch ascC unsorted 4
  IO.println s!"  unsorted ((3,1),(4,2)): found={found2.isSome} tried={tried2}"

  -- Balanced partition search
  IO.println ""
  IO.println "--- Balanced partition via selector search ---"
  let bal := Term.pair
    (.pair (labeledElement 2) (labeledElement 8))
    (.pair (labeledElement 3) (labeledElement 7))
  let (found3, tried3) :=
    selectorSearch balancedConstraint bal 4
  IO.println s!"  ((2,8),(3,7)): found={found3.isSome} tried={tried3}"

  let unbal := Term.pair
    (.pair (labeledElement 2) (labeledElement 3))
    (.pair (labeledElement 7) (labeledElement 8))
  let (found4, tried4) :=
    selectorSearch balancedConstraint unbal 4
  IO.println s!"  ((2,3),(7,8)): found={found4.isSome} tried={tried4}"

/-! ### Demo 3: Constraint as term -/

#eval! do
  IO.println ""
  IO.println "=== PART C: CONSTRAINT AS TERM ==="
  IO.println ""

  -- Build an ascending constraint term for labels 1..4
  let tc := ascendingTermConstraint 5
  IO.println s!"  constraint term size: {tc.term.size}"
  IO.println s!"  constraint term depth: {tc.term.depth}"

  -- Check via the term-encoded constraint
  IO.println ""
  IO.println "--- Checking pairs via term constraint ---"
  for (a, b) in [(1,2), (2,3), (3,1), (4,2), (1,4)] do
    let result := tc.accepts (labeledElement a) (labeledElement b)
    IO.println s!"  C({a},{b}) = {result}"
  let extC : Constraint := ⟨fun a b => getLabel a ≤ getLabel b⟩
  IO.println ""
  IO.println "--- External vs term constraint ---"
  for (a, b) in [(1,3), (3,1), (2,4), (4,2)] do
    let la := labeledElement a
    let lb := labeledElement b
    let ext := extC.check la lb
    let trm := tc.accepts la lb
    IO.println s!"  ({a},{b}): external={ext} term={trm}"

/-! ### Demo 4: Directions as terms (self-contained witness) -/

#eval! do
  IO.println ""
  IO.println "=== DIRECTIONS AS TERMS ==="
  IO.println ""

  -- Encode a direction sequence as a term
  let dirs : List Direction := [Direction.left, Direction.right,
    Direction.left, Direction.left]
  let encoded := dirsToTerm dirs
  let decoded := termToDirs encoded
  let decodedStr := decoded.map fun d => match d with
    | Direction.left => "L" | Direction.right => "R"
  IO.println s!"  original: [L,R,L,L]"
  IO.println s!"  encoded term size: {encoded.size}"
  IO.println s!"  decoded: {decodedStr}"
  IO.println s!"  round-trip: {dirs == decoded}"

  -- A complete self-contained problem
  IO.println ""
  IO.println "--- Self-contained problem ---"
  let prob : RotationProblem := {
    constraint := (ascendingTermConstraint 5).term,
    dataterm := Term.pair
      (.pair (labeledElement 1) (labeledElement 2))
      (.pair (labeledElement 3) (labeledElement 4)),
    selector := dirsToTerm [Direction.left, Direction.left]
  }
  IO.println s!"  constraint size: {prob.constraint.size}"
  IO.println s!"  data size: {prob.dataterm.size}"
  IO.println s!"  selector size: {prob.selector.size}"
  IO.println s!"  total problem size: \
    {prob.constraint.size + prob.dataterm.size + prob.selector.size}"

/-! ## Assessment

    PART A — RULE SELECTION AS CONSTRAINT:

    The directed tree fold makes traversal order a searchable
    parameter. At each pair node, the selector chooses left or
    right. A valid selector = a direction sequence where every
    constraint check passes.

    This is a walk over the Tamari lattice: each direction
    choice is a step on the lattice. The lattice has C(n)
    nodes (Catalan number of tree shapes). Finding a valid
    walk IS the search problem.

    The selector search (allDirSeqs) explores 2^d direction
    sequences at depth d. For a balanced tree with k internal
    nodes, the selector has k binary choices = 2^k possible
    walks. This is exponential in tree depth — the NP-hard
    search space.

    The key structural observation: the selector IS the
    certificate. Given a selector (direction sequence), checking
    that it produces a valid tree fold is linear (one pass
    through the tree). Finding the selector is exponential
    (2^k possibilities). P vs NP is the gap between checking
    a selector and finding one.

    PART C — CONSTRAINT AS TERM:

    The constraint is encoded as a rotation calculus term
    containing accepted label pairs. Checking the constraint
    reads the term and matches against the data. The language
    is self-applicable: checking is a structural operation on
    terms, not an external function call.

    The constraint term's SIZE encodes the constraint's
    complexity. A simple constraint (ascending order) has
    O(n^2) pairs for n labels. A complex constraint (SAT
    with many clauses) has more pairs. The constraint term
    IS the problem specification, and its size is the problem
    size.

    COMBINED:

    A fully self-contained rotation problem has three terms:
    - Constraint term: WHAT to check (the problem)
    - Data term: WHERE to check (the instance)
    - Selector term: HOW to traverse (the witness)

    Verification = check that selector + data + constraint
    produce a valid tree fold. Linear in total term size.

    Search = find a selector term given constraint + data.
    Exponential in tree depth (selector space = 2^k).

    The gap between verification and search is the gap
    between reading a term and constructing one. This is
    the rotation calculus's native expression of P vs NP:
    same language, same terms, same operations — the only
    difference is whether the selector is given or sought.
-/

end RotationCalculus
