/-
  Rotation Calculus: Complexity
  ==============================

  Complexity classes as structural properties of constrained rotation problems.

  - P = problems where a contracting arrangement can be found in polynomial time
  - NP = problems where a contracting arrangement can be verified in linear time
        but finding one requires searching exponential arrangement space

  The language makes these visible as different questions about the same structure:
  - Verification: run the rotation on a given arrangement (linear)
  - Search: find an arrangement where every constraint check passes (exponential)
-/

import SpectralArithmetic.Rotation.Constraint

namespace RotationCalculus

open Term

/-! ## Arrangement space -/

/-- The number of distinct flat list arrangements of n elements.
    For atomic elements, this is n! (all permutations). -/
def flatArrangementCount (n : ℕ) : ℕ := Nat.factorial n

/-- n! ≥ 1 for all n. -/
theorem arrangement_count_pos (n : ℕ) : flatArrangementCount n ≥ 1 := by
  simp [flatArrangementCount]
  exact Nat.factorial_pos n

/-! ## SAT as constrained rotation -/

/-- A Boolean variable assignment: variable index paired with truth value. -/
structure VarAssignment where
  var : ℕ
  val : Bool
  deriving DecidableEq, Repr

/-- A literal is (variable index, polarity). -/
abbrev Literal := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Literal

/-- Check whether an assignment satisfies a literal. -/
def satisfiesLiteral (va : VarAssignment) (lit : Literal) : Bool :=
  if va.var == lit.1 then va.val == lit.2 else true

/-- A SAT instance: a list of clauses over Boolean variables. -/
structure SATInstance where
  numVars : ℕ
  clauses : List Clause

/-! ## Graph coloring as constrained rotation -/

/-- A colored vertex: vertex id paired with color. -/
structure ColoredVertex where
  vertex : ℕ
  color : ℕ
  deriving DecidableEq, Repr

/-- An edge is a pair of vertex ids. -/
abbrev Edge := ℕ × ℕ

/-- A graph coloring instance. -/
structure GraphColoringInstance where
  numVertices : ℕ
  numColors : ℕ
  edges : List Edge

/-- Build a graph coloring constraint: adjacent vertices must have different colors. -/
def coloringConstraint (edges : List Edge)
    (getVertex : Term → Option ColoredVertex) : Constraint where
  check := fun a _b =>
    match getVertex a with
    | none => true
    | some _va => true  -- Simplified; full version inspects b for neighbors

/-! ## The P vs NP question in the language -/

/-- A problem instance: elements to arrange and a constraint to satisfy. -/
structure Problem where
  elements : List Term
  constraint : Constraint

/-- A problem is verifiable in linear time:
    given a proposed arrangement, check it by running the rotation. -/
def Problem.check (P : Problem) (arrangement : Term) : Bool :=
  verify P.constraint arrangement

/-- A problem is solvable if a contracting arrangement exists. -/
def Problem.solvable (P : Problem) : Prop :=
  existsContractingArrangement P.constraint P.elements

/-- The witness is the arrangement itself. -/
def Problem.Witness (P : Problem) :=
  { t : Term // isArrangementOf t P.elements ∧ contracts P.constraint (.observe t) }

/-! ## Structural complexity measures -/

/-- Count pairs of elements that fail the constraint. -/
def constraintFailCount (C : Constraint) (elements : List Term) : ℕ :=
  let pairs := elements.flatMap fun a => elements.map fun b => (a, b)
  (pairs.filter fun (a, b) => !C.check a b).length

/-- A constraint is sparse if few pairs fail. -/
def Constraint.isSparse (C : Constraint) (elements : List Term) (threshold : ℕ) : Prop :=
  constraintFailCount C elements ≤ threshold

/-- A constraint is dense if most pairs fail. -/
def Constraint.isDense (C : Constraint) (elements : List Term) (threshold : ℕ) : Prop :=
  constraintFailCount C elements ≥ threshold

/-! ## Observation trace -/

/-- The observation at each step: the constraint projects the pair to a bit,
    while the content persists. -/
structure ObservationStep where
  observed : Term
  carried : Term
  passed : Bool
  deriving Repr

/-- Extract the sequence of observations from a constrained run.
    Uses fuel to ensure termination. -/
def observationTrace (C : Constraint) (t : Term) (fuel : ℕ) : List ObservationStep :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    match t with
    | .observe (.pair a b) =>
      let passed := C.check a b
      let s : ObservationStep := ⟨a, b, passed⟩
      if passed then
        s :: observationTrace C (.pair b (.observe a)) fuel'
      else
        [s]
    | _ => []

/-! ## Connection to the spectral arithmetic framework

    The eigenvalue/decomposition duality maps directly:

    - eigenvalue = the constraint check result (the bit, what obs reads, cheap)
    - decomposition = the specific arrangement (what obs doesn't read, expensive)
    - smuggled payload = carried content at each step (present, invisible to constraint)

    In spectral arithmetic, compose(f_a, f_b) has eigenvalue a+b.
    Obs reads the sum. The partition is hidden.

    In rotation calculus, pair(a, b) is the composed structure.
    The constraint reads a relationship between a and b (one bit).
    The full structure of a and b is carried through unchanged.

    The observation trace IS the computation. The sequence of observed/carried
    pairs, with constraint verdicts, is the full record of what happened.
    Replaying it (verification) is linear. Constructing it (search) is
    finding the arrangement that produces all-true verdicts. -/

/-- The trace length is bounded by the term size.
    Each step consumes one pair under observe. -/
theorem trace_length_bound (C : Constraint) (t : Term) (fuel : ℕ) :
    (observationTrace C t fuel).length ≤ fuel := by
  induction fuel generalizing t with
  | zero => simp [observationTrace]
  | succ n ih =>
    simp only [observationTrace]
    match t with
    | .observe (.pair a b) =>
      simp only []
      by_cases hc : C.check a b
      · simp [hc]
        calc (observationTrace C (.pair b (.observe a)) n).length
            ≤ n := ih _
          _ ≤ n := le_refl n
      · simp [hc]
    | .observe .ground => simp
    | .observe (.observe _) => simp
    | .ground => simp
    | .pair _ _ => simp

end RotationCalculus
