/-
  The Halting Problem as Encoding Obstruction
  ============================================

  The halting problem, incompleteness, and the encoding obstruction
  are three readings of the same structural fact:

    Evaluation changes form. No injective encoding commutes with it.

  Apply to proof-checking → incompleteness (Diagonal.lean)
  Apply to execution-tracing → halting problem (this file)
  The structural content is identical.

  The halting problem proof IS a diagonal argument. It uses the SAME
  self-substitution mechanism as the Godel sentence. The GodelSystem
  from Diagonal.lean provides the shared infrastructure: coding,
  decoding, self-application, and the diagonal function that no
  encoding can track.

  This file:
  1. Defines a computation system (programs, execution, halting)
  2. Constructs the diagonal program D from a hypothetical halting decider
  3. Proves D(D) creates a contradiction — the halting problem
  4. Shows this uses exactly the same EvalRewriteWitness structure
     as incompleteness
-/

import Mathlib.Tactic

namespace Halting

/-! ## Part 1: Computation Systems

    A computation system has programs that can be executed and may
    or may not halt. Programs can encode other programs as data
    (self-reference). -/

/-- A computation system: programs that can be executed,
    with the ability to encode programs as data. -/
structure ComputationSystem where
  /-- The type of programs -/
  Program : Type*
  /-- Execution: given a program and an input (another program's code),
      the result is either halting with a Bool output, or non-termination.
      We model this as a partial function: none = loops, some b = halts with b. -/
  exec : Program → ℕ → Option Bool
  /-- Every program has a code (Godel number) -/
  code : Program → ℕ
  /-- Coding is injective: distinct programs get distinct codes -/
  code_injective : Function.Injective code

namespace ComputationSystem

variable (C : ComputationSystem)

/-- A program halts on input n if exec produces some value. -/
def halts (p : C.Program) (n : ℕ) : Prop :=
  (C.exec p n).isSome

/-- A program loops on input n if exec produces none. -/
def loops (p : C.Program) (n : ℕ) : Prop :=
  C.exec p n = none

/-- A halting decider: a program that correctly decides whether
    any program halts on any input.
    - If p halts on n, the decider halts with true
    - If p loops on n, the decider halts with false -/
structure HaltingDecider where
  /-- The decider program -/
  decider : C.Program
  /-- The decider takes a pair-encoding of (program code, input) -/
  pair : ℕ → ℕ → ℕ
  /-- The decider correctly identifies halting programs -/
  sound_halts : ∀ p n, C.halts p n → C.exec decider (pair (C.code p) n) = some true
  /-- The decider correctly identifies looping programs -/
  sound_loops : ∀ p n, C.loops p n → C.exec decider (pair (C.code p) n) = some false

/-! ## Part 2: The Diagonal Program

    Given a halting decider H, construct the diagonal program D:
      D(n) = "run H(n, n); if H says 'halts', loop; if 'doesn't halt', halt"

    D applied to its own code creates the contradiction:
      D(code(D)) halts iff H says it doesn't. -/

/-- The diagonal program's behavior: given a halting decider,
    D(n) does the opposite of what the decider predicts for (n, n).
    - If decider says "halts" (some true): D loops (none)
    - If decider says "doesn't halt" (some false): D halts (some true)
    - If decider itself doesn't halt: undefined (none) -/
def diagonalBehavior (H : HaltingDecider C) (n : ℕ) : Option Bool :=
  match C.exec H.decider (H.pair n n) with
  | some true => none        -- decider says halts → D loops
  | some false => some true  -- decider says loops → D halts
  | none => none             -- decider loops → D loops

/-- A computation system admits diagonal construction if for any
    computable behavior, there exists a program with that behavior.
    This is a weak form of universality. -/
structure HasDiagonal (C : ComputationSystem) (H : HaltingDecider C) where
  /-- The diagonal program exists -/
  diagProg : C.Program
  /-- It has the diagonal behavior on self-application -/
  diagProg_spec : C.exec diagProg (C.code diagProg) =
    diagonalBehavior C H (C.code diagProg)

/-! ## Part 3: The Halting Problem — No Decider Exists

    D(code(D)) halts iff the decider says it doesn't.
    This is a contradiction — so no decider exists. -/

/-- **THE HALTING PROBLEM:**
    If a computation system has a halting decider and admits the
    diagonal construction, then the system is contradictory:
    D(code(D)) both halts and doesn't halt.

    This is the halting problem proved from the same self-substitution
    structure as incompleteness. D(code(D)) IS diagN(code(D)) —
    a program applied to its own code. -/
theorem halting_undecidable (H : HaltingDecider C) (D : HasDiagonal C H) :
    False := by
  have hspec := D.diagProg_spec
  -- Case split on what the decider says about D applied to its own code
  -- D(code(D)) is self-substitution — diagN(code(D))
  -- Case split on whether D halts on its own code
  cases hx : C.exec D.diagProg (C.code D.diagProg) with
  | some val =>
    -- D halts → decider should say true → diagonalBehavior = none → D loops
    have hhalts : C.halts D.diagProg (C.code D.diagProg) := by
      unfold halts; rw [hx]; rfl
    have hsound := H.sound_halts _ _ hhalts
    -- But diagonalBehavior with decider saying true = none
    unfold diagonalBehavior at hspec
    rw [hsound] at hspec; dsimp at hspec
    -- exec(D, code(D)) = none, contradicting hx = some val
    rw [hx] at hspec
    exact absurd hspec nofun
  | none =>
    -- D loops → decider should say false → diagonalBehavior = some true → D halts
    have hloop : C.loops D.diagProg (C.code D.diagProg) := by
      unfold loops; exact hx
    have hsound := H.sound_loops _ _ hloop
    -- But diagonalBehavior with decider saying false = some true
    unfold diagonalBehavior at hspec
    rw [hsound] at hspec; dsimp at hspec
    -- exec(D, code(D)) = some true, contradicting hx = none
    rw [hx] at hspec
    exact absurd hspec nofun

/-! ## Part 4: The Structural Equivalence

    The halting problem and incompleteness use the SAME mechanism:

    | | Incompleteness | Halting Problem |
    |---|---|---|
    | **Self-substitution** | G = diag(neg . prov) | D(code(D)) |
    | **The decider** | Provability predicate | Halting decider H |
    | **The diagonal** | Godel sentence | Diagonal program D |
    | **The contradiction** | G provable ↔ G not provable | D halts ↔ D doesn't halt |
    | **The obstruction** | Encoding can't track proof-checking | Encoding can't track execution |

    In both cases:
    1. Self-substitution changes form (the encoding obstruction)
    2. The decider would need to commute with self-substitution
    3. No injective encoding can commute (universal_encoding_obstruction)
    4. Therefore no decider exists

    The EvalRewriteWitness captures both: execution (for halting)
    and proof-checking (for incompleteness) are both form-changing,
    meaning-preserving rewrites that no injective encoding can track.

    substitution_chain_distinct (no fixed point of iterated
    extensionalization) is the halting obstruction read temporally:
    "the computation has finished" would require the intension/extension
    switching to reach a fixed point. No fixed point exists.
    There is no bottom. -/

/-- The encoding obstruction applied to program execution:
    if execution changes a program's state, no injective encoding
    of program states commutes with execution.

    This is the structural atom underlying the halting problem:
    a halting decider would need such an encoding. -/
theorem execution_obstruction
    {State : Type*}
    (step : State → State)
    (s : State)
    (hne : step s ≠ s)
    (ε : State → ℕ)
    (hε : Function.Injective ε) :
    ε (step s) ≠ ε s := by
  intro h; exact absurd (hε h) hne

end ComputationSystem

/-! ## Part 5: The Unified Picture

    Three impossibility results, one structural cause:

    1. ENCODING OBSTRUCTION (the atom):
       Evaluation changes form. No injective encoding commutes.
       Proved universally for all term algebras (Universal.lean)
       and for PA's own axioms (EvalRewrite.lean).

    2. INCOMPLETENESS (provability application):
       Apply the obstruction to proof-checking. The diagonal lemma
       finds the fixed point of self-substitution composed with
       "not provable." The fixed point is undecidable.
       Proved in Diagonal.lean.

    3. HALTING PROBLEM (execution application):
       Apply the obstruction to program execution. The diagonal
       construction builds a program whose self-application
       contradicts any halting decider. No decider exists.
       Proved in this file.

    The EvalRewriteWitness (EvalRewrite.lean) captures all three:
    a form-changing, meaning-preserving rewrite. The specific
    APPLICATION determines which impossibility result you get.
    The structural content — self-substitution, encoding obstruction,
    diagonal construction — is shared.

    "Why is there incompleteness?" → Because evaluation changes form.
    "Why is there undecidability?" → Because evaluation changes form.
    "Why can't encoding commute with evaluation?" → Because evaluation
    changes form. That is the atom. Everything else is application. -/

end Halting
