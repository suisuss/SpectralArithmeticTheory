/-
  Meta-Rewrite #0: The Rotation Calculus as a Rewriting System
  =============================================================

  #0 is the rotation calculus itself: terms, the rotation rule,
  constraints, and constrained execution. This is the OBJECT-LEVEL
  rewriting system. A computation is a sequence of constrained
  rotation steps, producing an execution trace.

  #1 (MetaRewriting.lean) operates on the SOLVER's proof trace,
  contracting cascades and folding conflict cycles. It doesn't
  use rotation calculus terms.

  The connection: every #1 meta-event corresponds to a pattern
  of #0 rotation steps:
  - CASCADE(n)        = n consecutive successful constrained rotations
  - SEARCH(v,p)       = one constrained rotation that passed
  - CONFLICT_CYCLE    = rotation that failed + undo + retry
  - ABSTRACTION       = local sub-problem solved by exhaustive rotation

  This file builds:
  1. Traced constrained execution (each rotation step recorded)
  2. The execution trace as a rotation calculus term (self-application)
  3. Meta-constraint: when is one trace a valid contraction of another?
  4. The bridge: #0 trace → #1 meta-trajectory is itself a rotation
-/

import SpectralArithmetic.Rotation.MetaRewriting

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Execution events (rotation-level) -/

/-- A single rotation step's outcome. -/
inductive RotationEvent where
  | rotated  : Term → Term → RotationEvent  -- observed a, carried b
  | absorbed : RotationEvent                  -- observe(ground) → ground
  | blocked  : Term → Term → RotationEvent   -- constraint failed on (a, b)
  deriving Repr

/-- An execution trace: the sequence of rotation events. -/
abbrev RotationTrace := List RotationEvent

/-! ## Traced constrained execution

    Two models:

    1. ROTATION (list traversal): the rotation rule walks a flat list
       one element at a time. observe(pair(a, rest)) → pair(rest, observe(a)).
       Each step peels the first element and dives into it. Linear in list length.

    2. TREE FOLD (catamorphism): verifyTree walks the tree top-down,
       checking the constraint at each pair node, recursing into both
       subtrees. This is how SAT verification actually works. Also linear,
       but traverses the tree structure, not a flat sequence.

    Both are O(n) for verification. The difference: rotation works on
    sequences, tree fold works on hierarchical decompositions. SAT uses
    tree fold because clauses have hierarchical structure (variable
    groupings). -/

/-- Traced rotation execution (list traversal).
    Walks a flat list, recording each constraint check. -/
def tracedRotation (C : Constraint) (t : Term) (fuel : ℕ)
    : Outcome × RotationTrace :=
  match fuel with
  | 0 => (.contracted, [])
  | fuel + 1 =>
    match t with
    | .observe (.pair a b) =>
      if C.check a b then
        let (innerOutcome, innerTrace) :=
          tracedRotation C (.observe a) fuel
        (innerOutcome, .rotated a b :: innerTrace)
      else
        (.stuckAt a b, [.blocked a b])
    | .observe .ground =>
      (.contracted, [.absorbed])
    | .pair _ b =>
      tracedRotation C b fuel
    | _ => (.contracted, [])

/-- Traced tree fold (catamorphism).
    Walks the tree top-down, checking the constraint at each pair
    node, recording each check. This mirrors verifyTree. -/
def tracedTreeFold (C : Constraint) : Term → RotationTrace
  | .ground => []
  | .pair _ .ground => []
  | .pair a b =>
    if C.check a b then
      [.rotated a b] ++ tracedTreeFold C a ++ tracedTreeFold C b
    else
      [.blocked a b]
  | .observe t => tracedTreeFold C t

/-- Traced tree fold with outcome. -/
def tracedTreeRun (C : Constraint) (t : Term)
    : Outcome × RotationTrace :=
  let trace := tracedTreeFold C t
  let hasBlock := trace.any fun e => match e with
    | .blocked _ _ => true | _ => false
  if hasBlock then
    match trace.find? fun e => match e with
      | .blocked _ _ => true | _ => false with
    | some (.blocked a b) => (.stuckAt a b, trace)
    | _ => (.contracted, trace)
  else (.contracted, trace)

/-- Count rotation events by type. -/
structure RotationProfile where
  nRotated  : ℕ
  nAbsorbed : ℕ
  nBlocked  : ℕ
  total     : ℕ
  deriving Repr

def showOutcome : Outcome → String
  | .contracted => "contracted"
  | .stuckAt _ _ => "stuck"

def profileRotation (trace : RotationTrace) : RotationProfile :=
  trace.foldl (fun acc e => match e with
    | .rotated _ _ =>
      { acc with nRotated := acc.nRotated + 1,
                 total := acc.total + 1 }
    | .absorbed =>
      { acc with nAbsorbed := acc.nAbsorbed + 1,
                 total := acc.total + 1 }
    | .blocked _ _ =>
      { acc with nBlocked := acc.nBlocked + 1,
                 total := acc.total + 1 })
  { nRotated := 0, nAbsorbed := 0, nBlocked := 0, total := 0 }

/-! ## The execution trace as a term

    The trace itself is a list of events. We encode it as a
    rotation calculus term — nested pairs of event-tagged elements.
    This is the self-application: the trace of computation is
    itself a term in the same calculus.

    Encoding:
    - rotated(a, b)  → pair(pair(a, b), ground)   — 2-element tag
    - absorbed       → ground                      — leaf
    - blocked(a, b)  → pair(pair(a, b), pair(ground, ground)) — 3-element tag
-/

/-- Encode a rotation event as a term. -/
def encodeEvent : RotationEvent → Term
  | .rotated a b  => .pair (.pair a b) .ground
  | .absorbed     => .ground
  | .blocked a b  => .pair (.pair a b) (.pair .ground .ground)

/-- Encode a full trace as a nested pair term. -/
def encodeTrace : RotationTrace → Term
  | [] => .ground
  | e :: es => .pair (encodeEvent e) (encodeTrace es)

/-- Decode the tag: is this a rotated, absorbed, or blocked event? -/
def decodeEventKind : Term → String
  | .pair (.pair _ _) .ground => "rotated"
  | .ground => "absorbed"
  | .pair (.pair _ _) (.pair .ground .ground) => "blocked"
  | _ => "unknown"

/-! ## Trace contraction via the rotation rule

    Key insight: contracting a trace IS rotating through it.
    Applying observe to the trace-as-term and rotating means:
    - Each rotation step inspects one event
    - Consecutive "rotated" events can be absorbed into one
    - A "blocked" event stops the meta-rotation

    The meta-constraint for trace contraction:
    - Two consecutive "rotated" events contract (cascade absorption)
    - A "rotated" followed by "blocked" followed by "rotated"
      contracts (conflict cycle folding)
    - Otherwise: the event passes through unchanged -/

/-- Meta-constraint: can two adjacent trace events be merged? -/
def traceContractionConstraint : Constraint where
  check := fun a b =>
    -- Two rotated events can always merge (cascade absorption)
    let aKind := decodeEventKind a
    let bKind := decodeEventKind b
    -- Merge if both are rotated (cascade) or first is ground (end)
    (aKind == "rotated" && bKind == "rotated") ||
    (aKind == "absorbed")

/-- Contract a trace by running the rotation rule with the
    trace contraction constraint. Consecutive successful
    rotations merge into a single event. -/
def contractTrace (trace : RotationTrace) : Outcome × RotationTrace :=
  let encoded := encodeTrace trace
  tracedRotation traceContractionConstraint (.observe encoded)
    (encoded.size + 1)

/-! ## The bridge: #0 events → #1 meta-events

    Every #1 MetaEvent corresponds to a pattern of #0 RotationEvents:

    | #1 MetaEvent         | #0 pattern                        |
    |-----------------------|-----------------------------------|
    | CASCADE(n)            | n consecutive .rotated events     |
    | SEARCH(v, p)          | 1 .rotated event                  |
    | CONFLICT_CYCLE(v, sz) | .rotated + .blocked + .rotated    |
    | (completion)          | .absorbed                         |

    The contraction from #0 trace to #1 meta-trajectory is:
    runs of .rotated → one CASCADE
    isolated .rotated → one SEARCH
    .blocked between .rotated → one CONFLICT_CYCLE
-/

/-- Convert a #0 rotation trace to #1-style meta-events.
    Groups consecutive rotations into cascades. -/
partial def rotationToMeta : RotationTrace → List MetaEvent
  | [] => []
  | .absorbed :: rest => rotationToMeta rest
  | .blocked _ _ :: .rotated _ _ :: rest =>
    -- A blocked followed by rotated = conflict resolved
    .conflictCycle 0 0 :: rotationToMeta rest
  | .blocked _ _ :: rest =>
    -- Terminal block = stuck
    rotationToMeta rest
  | events =>
    -- Count consecutive rotated events
    let run := events.takeWhile fun e => match e with
      | .rotated _ _ => true | _ => false
    let runLen := run.length
    let rest := events.drop runLen
    if runLen > 1 then
      .cascade runLen :: rotationToMeta rest
    else if runLen == 1 then
      .searchStep 0 true :: rotationToMeta rest
    else
      -- shouldn't happen
      rotationToMeta rest

/-! ## Demonstrations -/

/-! ### Demo 1: Traced execution on rotation calculus terms -/

#eval! do
  IO.println "=== META-REWRITE #0: ROTATION-LEVEL TRACES ==="
  IO.println ""

  -- Compare rotation (list) vs tree fold (catamorphism)
  IO.println "--- Trivial constraint: rotation vs tree fold ---"
  for n in [3, 5, 8] do
    let t := Term.fromList (List.replicate n .ground)
    let (_, rotTrace) := tracedRotation .trivial (.observe t) 50
    let (_, treeTrace) := tracedTreeRun .trivial t
    let rpR := profileRotation rotTrace
    let rpT := profileRotation treeTrace
    IO.println s!"  {n} elements: rotation={rpR.total} tree={rpT.total}"

  -- SAT constraint: tree fold is the natural model
  IO.println ""
  IO.println "--- SAT: (x0 OR x1) AND (x1 OR x2) ---"
  let formula : SATFormula :=
    [[(0, true), (1, true)], [(1, true), (2, true)]]
  let satC := satConstraint formula
  -- Good tree arrangement
  let good := Term.pair
    (.pair (literal 0 true) (literal 1 true))
    (literal 2 true)
  let (outG, traceG) := tracedTreeRun satC good
  let rpG := profileRotation traceG
  IO.println s!"  x0=T,x1=T,x2=T (tree): outcome={showOutcome outG} \
    checks={rpG.total} rotated={rpG.nRotated} blocked={rpG.nBlocked}"

  -- Bad arrangement
  let bad := Term.pair
    (.pair (literal 0 false) (literal 1 false))
    (literal 2 false)
  let (outB, traceB) := tracedTreeRun satC bad
  let rpB := profileRotation traceB
  IO.println s!"  x0=F,x1=F,x2=F (tree): outcome={showOutcome outB} \
    checks={rpB.total} rotated={rpB.nRotated} blocked={rpB.nBlocked}"

  -- Also show rotation model on the same instances
  IO.println ""
  IO.println "--- Same SAT via rotation (list model) ---"
  let goodList := Term.fromList
    [literal 0 true, literal 1 true, literal 2 true]
  let (outGR, traceGR) := tracedRotation satC (.observe goodList) 20
  let rpGR := profileRotation traceGR
  IO.println s!"  x0=T,x1=T,x2=T (list): outcome={showOutcome outGR} \
    steps={rpGR.total} rotated={rpGR.nRotated} blocked={rpGR.nBlocked}"

  let badList := Term.fromList
    [literal 0 false, literal 1 false, literal 2 false]
  let (outBR, traceBR) := tracedRotation satC (.observe badList) 20
  let rpBR := profileRotation traceBR
  IO.println s!"  x0=F,x1=F,x2=F (list): outcome={showOutcome outBR} \
    steps={rpBR.total} rotated={rpBR.nRotated} blocked={rpBR.nBlocked}"

/-! ### Demo 2: Trace as a term (self-application) -/

#eval! do
  IO.println ""
  IO.println "=== TRACE AS TERM (self-application) ==="
  IO.println ""

  -- Generate a trace, encode it as a term, measure it
  let t := Term.fromList [.ground, .ground, .ground]
  let (_, trace) := tracedRotation .trivial (.observe t) 20
  IO.println s!"  Original trace: {trace.length} events"
  let encoded := encodeTrace trace
  IO.println s!"  Encoded term size: {encoded.size}"
  IO.println s!"  Encoded term depth: {encoded.depth}"

  -- Now run the rotation rule ON the trace-term
  let (cOutcome, cTrace) := contractTrace trace
  IO.println s!"  Contracted: {cTrace.length} meta-steps, outcome={showOutcome cOutcome}"

  -- Larger trace
  let t := Term.fromList (List.replicate 8 .ground)
  let (_, trace) := tracedRotation .trivial (.observe t) 100
  IO.println ""
  IO.println s!"  8-element trace: {trace.length} events"
  let encoded := encodeTrace trace
  IO.println s!"  Encoded term size: {encoded.size}"
  let (cOutcome, cTrace) := contractTrace trace
  IO.println s!"  Contracted: {cTrace.length} meta-steps, outcome={showOutcome cOutcome}"

/-! ### Demo 3: Bridge — #0 trace to #1 meta-events -/

#eval! do
  IO.println ""
  IO.println "=== BRIDGE: #0 → #1 ==="
  IO.println ""

  -- Trivial: all rotations → single cascade
  let t := Term.fromList (List.replicate 6 .ground)
  let (_, trace) := tracedRotation .trivial (.observe t) 50
  let mevts := rotationToMeta trace
  let rp := profileRotation trace
  IO.println s!"  Trivial 6-elem: {rp.total} #0-events → \
    {mevts.length} #1-events"
  for e in mevts do
    IO.println s!"    {showMetaEvent e}"

  -- SAT with constraint: mix of rotations and blocks
  IO.println ""
  let formula : SATFormula :=
    [[(0, true), (1, true)], [(1, true), (2, true)]]
  let satC := satConstraint formula
  -- Good arrangement
  let good := Term.pair (literal 0 true)
    (.pair (literal 1 true) (literal 2 true))
  let (_, traceG) := tracedRotation satC (.observe good) 20
  let mevtsG := rotationToMeta traceG
  let rpG := profileRotation traceG
  IO.println s!"  SAT good: {rpG.total} #0-events → \
    {mevtsG.length} #1-events"
  for e in mevtsG do
    IO.println s!"    {showMetaEvent e}"

  -- Bad arrangement
  let bad := Term.pair (literal 0 false)
    (.pair (literal 1 false) (literal 2 false))
  let (_, traceB) := tracedRotation satC (.observe bad) 20
  let mevtsB := rotationToMeta traceB
  let rpB := profileRotation traceB
  IO.println s!"  SAT bad: {rpB.total} #0-events → \
    {mevtsB.length} #1-events"
  for e in mevtsB do
    IO.println s!"    {showMetaEvent e}"

/-! ### Demo 4: Contraction comparison across sizes -/

#eval! do
  IO.println ""
  IO.println "=== #0 CONTRACTION SCALING ==="
  IO.println ""
  IO.println "n\t#0-events\t#1-events\tcontraction"
  for n in [3, 4, 5, 6, 8, 10, 15, 20] do
    let t := Term.fromList (List.replicate n .ground)
    let (_, trace) := tracedRotation .trivial (.observe t) (n * n)
    let mevts := rotationToMeta trace
    let cr := if mevts.length > 0
      then trace.length * 100 / mevts.length else 0
    IO.println s!"{n}\t{trace.length}\t\t{mevts.length}\t\t{cr/100}.{(cr/10)%10}{cr%10}x"

/-! ## Assessment

    Meta-rewrite #0 is the rotation calculus doing what it does:
    constrained rotation steps, each producing an event.

    Meta-rewrite #1 contracts the solver's proof trace — cascades
    become macro-events, conflict cycles fold.

    The bridge (rotationToMeta) shows these are the same operation
    at different levels:

    #0: observe(pair(a₁, pair(a₂, pair(a₃, ground))))
        → pair(a₂, observe(pair(a₃, pair(a₁, ground))))     [rotate]
        → pair(a₃, observe(pair(a₁, pair(a₂, ground))))     [rotate]
        → ...until ground

    #1: CASCADE(n) absorbs all n rotations into one event

    The contraction IS the rotation rule applied to the trace-term.
    Consecutive successful rotations in the #0 trace are
    adjacent elements in the trace-term. The meta-constraint says
    "two rotated events can merge." Running the rotation rule on
    the trace-term with this meta-constraint contracts the cascade.

    The system is self-applicable: the rotation calculus can
    rewrite its own execution traces using the same rule.

    Where #0 and #1 genuinely differ:
    - #0 operates on the PROBLEM (SAT instance as a term)
    - #1 operates on the SEARCH (solver's decision trace)
    - #0 contraction = cascade absorption (deterministic steps merge)
    - #1 contraction = cascade absorption + conflict cycle folding
    - Conflict cycles have no #0 analogue because #0 doesn't backtrack
      — it either rotates or gets stuck. Backtracking is a #1 phenomenon.

    The gap between #0 and #1 is exactly the gap between
    verification and search: #0 verifies a given arrangement
    (linear, deterministic, contractible). #1 records the search
    FOR an arrangement (exponential, non-deterministic, partially
    contractible). The irreducible part of #1 — the conflict
    cycles — is what makes search harder than verification.
-/

end RotationCalculus
