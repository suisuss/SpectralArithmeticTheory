/-
  Boolean Expression ADT with Two Evaluation Strategies
  ======================================================

  A third computational framework for testing SAT indistinguishability,
  independent of both SK combinatory reduction and DynSemiring
  normalization.

  The key structural property: boolean values are *constructors* of
  an inductive type (T and F), making them structurally distinct in
  the term — analogous to K vs SK in combinators, f₀ vs f₁ in
  DynSemiring. This provides the structural entanglement between
  data and computation needed for meaningful intermediate analysis.

  Two evaluation strategies:
  - Eager (innermost-first): reduce deepest redexes first.
    Always processes all subformulas before enclosing connectives.
  - Lazy (outermost-first): reduce topmost redex first.
    Short-circuits (AND F _ → F without evaluating second arg).

  RESULT: Unlike SK combinators and DynSemiring normalization,
  ADT pattern-matching reduction DOES separate SAT from UNSAT
  at intermediate fuel levels. Both eager and lazy evaluation
  achieve separation by fuel 3.

  This is a critical negative result for the indistinguishability
  hypothesis: the phenomenon is NOT universal across all
  computational frameworks with structural booleans. It appears
  specific to frameworks where reduction creates structural
  complexity (SK duplication, Leibniz tree expansion) rather
  than frameworks where reduction monotonically simplifies
  (pattern matching eliminates constructors).
-/

import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace BoolExpr

/-! ## Syntax -/

/-- Boolean expressions with structural T/F constructors. -/
inductive Expr where
  | T : Expr
  | F : Expr
  | not : Expr → Expr
  | and : Expr → Expr → Expr
  | or : Expr → Expr → Expr
  deriving DecidableEq, Repr

namespace Expr

/-! ## Term measurements -/

/-- Count of T constructors in the expression tree. -/
def countT : Expr → Nat
  | .T => 1
  | .F => 0
  | .not e => countT e
  | .and a b => countT a + countT b
  | .or a b => countT a + countT b

/-- Count of F constructors in the expression tree. -/
def countF : Expr → Nat
  | .T => 0
  | .F => 1
  | .not e => countF e
  | .and a b => countF a + countF b
  | .or a b => countF a + countF b

/-- Total number of nodes in the expression tree. -/
def size : Expr → Nat
  | .T => 1
  | .F => 1
  | .not e => 1 + size e
  | .and a b => 1 + size a + size b
  | .or a b => 1 + size a + size b

/-- Count of connective nodes (not, and, or). -/
def countOps : Expr → Nat
  | .T => 0
  | .F => 0
  | .not e => 1 + countOps e
  | .and a b => 1 + countOps a + countOps b
  | .or a b => 1 + countOps a + countOps b

/-! ## Eager evaluation (innermost-first / call-by-value) -/

/-- One step of eager (innermost-first) reduction.
    Reduces the deepest redex first: subexpressions are
    fully evaluated before the enclosing connective fires. -/
def eagerStep : Expr → Option Expr
  -- not: reduce argument first, then fire
  | .not (.T) => some .F
  | .not (.F) => some .T
  | .not e => match eagerStep e with
    | some e' => some (.not e')
    | none => none
  -- and: reduce left first, then right, then fire
  | .and .T .T => some .T
  | .and .T .F => some .F
  | .and .F _ => some .F
  | .and .T e => match eagerStep e with
    | some e' => some (.and .T e')
    | none => none
  | .and a b => match eagerStep a with
    | some a' => some (.and a' b)
    | none => match eagerStep b with
      | some b' => some (.and a b')
      | none => none
  -- or: reduce left first, then right, then fire
  | .or .T _ => some .T
  | .or .F .T => some .T
  | .or .F .F => some .F
  | .or .F e => match eagerStep e with
    | some e' => some (.or .F e')
    | none => none
  | .or a b => match eagerStep a with
    | some a' => some (.or a' b)
    | none => match eagerStep b with
      | some b' => some (.or a b')
      | none => none
  -- Values
  | _ => none

/-- Multi-step eager reduction with fuel. -/
def eagerReduce (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel + 1 => match eagerStep e with
    | some e' => eagerReduce fuel e'
    | none => e

/-! ## Lazy evaluation (outermost-first / call-by-name) -/

/-- One step of lazy (outermost-first) reduction.
    Reduces the topmost redex first. Short-circuits:
    AND F _ → F and OR T _ → T without evaluating
    the second argument. -/
def lazyStep : Expr → Option Expr
  -- not: fire if argument is a value, otherwise reduce argument
  | .not .T => some .F
  | .not .F => some .T
  | .not e => match lazyStep e with
    | some e' => some (.not e')
    | none => none
  -- and: short-circuit on F, otherwise fire or reduce
  | .and .F _ => some .F
  | .and .T b => some b
  | .and a b => match lazyStep a with
    | some a' => some (.and a' b)
    | none => match lazyStep b with
      | some b' => some (.and a b')
      | none => none
  -- or: short-circuit on T, otherwise fire or reduce
  | .or .T _ => some .T
  | .or .F b => some b
  | .or a b => match lazyStep a with
    | some a' => some (.or a' b)
    | none => match lazyStep b with
      | some b' => some (.or a b')
      | none => none
  -- Values
  | _ => none

/-- Multi-step lazy reduction with fuel. -/
def lazyReduce (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel + 1 => match lazyStep e with
    | some e' => lazyReduce fuel e'
    | none => e

/-! ## SAT formula encoding -/

/-- Convert a Bool to a structural boolean expression. -/
def mkBool : Bool → Expr
  | true => .T
  | false => .F

/-- 3-clause shared-variable CNF formula:
    (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂)
    SAT assignments: 010 and 101. -/
def cnf3shared (b0 b1 b2 : Bool) : Expr :=
  .and (.and (.or (mkBool b0) (mkBool b1))
             (.or (.not (mkBool b0)) (mkBool b2)))
       (.or (.not (mkBool b1)) (.not (mkBool b2)))

/-! ## Measurement helpers -/

def eagerT (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countT (eagerReduce fuel (cnf3shared b0 b1 b2))

def eagerF (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countF (eagerReduce fuel (cnf3shared b0 b1 b2))

def eagerSz (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  size (eagerReduce fuel (cnf3shared b0 b1 b2))

def lazyT (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countT (lazyReduce fuel (cnf3shared b0 b1 b2))

def lazyF (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countF (lazyReduce fuel (cnf3shared b0 b1 b2))

/-! ## Part 1: Convergence — both strategies correctly evaluate SAT -/

theorem eager_converge_sat_010 : eagerReduce 10 (cnf3shared false true false) = .T :=
  by native_decide
theorem eager_converge_sat_101 : eagerReduce 10 (cnf3shared true false true) = .T :=
  by native_decide
theorem eager_converge_unsat_000 : eagerReduce 10 (cnf3shared false false false) = .F :=
  by native_decide
theorem eager_converge_unsat_001 : eagerReduce 10 (cnf3shared false false true) = .F :=
  by native_decide
theorem eager_converge_unsat_011 : eagerReduce 10 (cnf3shared false true true) = .F :=
  by native_decide
theorem eager_converge_unsat_100 : eagerReduce 10 (cnf3shared true false false) = .F :=
  by native_decide
theorem eager_converge_unsat_110 : eagerReduce 10 (cnf3shared true true false) = .F :=
  by native_decide
theorem eager_converge_unsat_111 : eagerReduce 10 (cnf3shared true true true) = .F :=
  by native_decide

theorem lazy_converge_sat_010 : lazyReduce 10 (cnf3shared false true false) = .T :=
  by native_decide
theorem lazy_converge_sat_101 : lazyReduce 10 (cnf3shared true false true) = .T :=
  by native_decide
theorem lazy_converge_unsat_000 : lazyReduce 10 (cnf3shared false false false) = .F :=
  by native_decide
theorem lazy_converge_unsat_111 : lazyReduce 10 (cnf3shared true true true) = .F :=
  by native_decide

/-! ## Part 2: Eager evaluation data

  Eager countT at each fuel level:
  ```
  Fuel  000(U) 001(U) 010(S) 011(U) 100(U) 101(S) 110(U) 111(U)
  0     0      2      2      4      2      4      4      6
  1     0      2      2      4      2      4      3      5
  2     0      1      3      5      1      3      2      4
  3     0      0      3      4      1      3      2      4
  4     0      0      2      3      0      2      1      3
  5     0      0      1      2      0      3      0      2
  10    0      0      1      0      0      1      0      0
  ```

  Fuel 0-1: SAT/UNSAT collisions (001(U)=2 = 010(S)=2).
  Fuel 2: SAT={010:3, 101:3}. No UNSAT has value 3. SEPARATES.
  Fuel 3: SAT={010:3, 101:3}. No UNSAT has value 3. SEPARATES.
  Fuel 10: SAT={1,1}, UNSAT={0,...,0}. SEPARATES (converged).
-/

-- Fuel 0: countT = number of true literals in assignment
theorem eager_f0_T_000 : eagerT 0 false false false = 0 := by native_decide
theorem eager_f0_T_001 : eagerT 0 false false true = 2 := by native_decide
theorem eager_f0_T_010 : eagerT 0 false true false = 2 := by native_decide
theorem eager_f0_T_011 : eagerT 0 false true true = 4 := by native_decide
theorem eager_f0_T_100 : eagerT 0 true false false = 2 := by native_decide
theorem eager_f0_T_101 : eagerT 0 true false true = 4 := by native_decide
theorem eager_f0_T_110 : eagerT 0 true true false = 4 := by native_decide
theorem eager_f0_T_111 : eagerT 0 true true true = 6 := by native_decide

/-- Fuel 0 collision: 001(UNSAT) and 010(SAT) both have countT = 2. -/
theorem eager_f0_collision : eagerT 0 false false true = eagerT 0 false true false :=
  by native_decide

-- Fuel 2: separation emerges
theorem eager_f2_T_000 : eagerT 2 false false false = 0 := by native_decide
theorem eager_f2_T_001 : eagerT 2 false false true = 1 := by native_decide
theorem eager_f2_T_010 : eagerT 2 false true false = 3 := by native_decide
theorem eager_f2_T_011 : eagerT 2 false true true = 5 := by native_decide
theorem eager_f2_T_100 : eagerT 2 true false false = 1 := by native_decide
theorem eager_f2_T_101 : eagerT 2 true false true = 3 := by native_decide
theorem eager_f2_T_110 : eagerT 2 true true false = 2 := by native_decide
theorem eager_f2_T_111 : eagerT 2 true true true = 4 := by native_decide

/-- Eager fuel 2: SAT assignments both have countT = 3.
    No UNSAT assignment has countT = 3.
    {000:0, 001:1, 011:5, 100:1, 110:2, 111:4} — none equal 3.
    countT SEPARATES SAT from UNSAT. -/
theorem eager_f2_sat_value :
    eagerT 2 false true false = 3 ∧ eagerT 2 true false true = 3 :=
  ⟨by native_decide, by native_decide⟩

theorem eager_f2_separates :
    eagerT 2 false false false ≠ 3 ∧
    eagerT 2 false false true ≠ 3 ∧
    eagerT 2 false true true ≠ 3 ∧
    eagerT 2 true false false ≠ 3 ∧
    eagerT 2 true true false ≠ 3 ∧
    eagerT 2 true true true ≠ 3 :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

/-! ## Part 3: Lazy evaluation data

  Lazy countT at each fuel level:
  ```
  Fuel  000(U) 001(U) 010(S) 011(U) 100(U) 101(S) 110(U) 111(U)
  0     0      2      2      4      2      4      4      6
  1     0      2      2      4      2      4      3      5
  2     0      1      1      3      1      3      2      4
  3     0      0      2      4      0      2      1      3
  4     0      0      2      3      0      2      1      3
  5     0      0      1      2      0      1      0      2
  10    0      0      1      0      0      1      0      0
  ```

  Fuel 0-1: SAT/UNSAT collisions (same as eager).
  Fuel 2: 010(S)=1 = 001(U)=1. COLLISION. (SAT values differ: 010=1, 101=3.)
  Fuel 3: SAT={010:2, 101:2}. No UNSAT has value 2. SEPARATES.
  Fuel 5+: SEPARATES.
-/

-- Fuel 2: lazy still has a collision
theorem lazy_f2_T_010 : lazyT 2 false true false = 1 := by native_decide
theorem lazy_f2_T_001 : lazyT 2 false false true = 1 := by native_decide

/-- Lazy fuel 2: 010(SAT)=1 = 001(UNSAT)=1. Still confused. -/
theorem lazy_f2_collision : lazyT 2 false true false = lazyT 2 false false true :=
  by native_decide

-- Fuel 3: lazy separates
theorem lazy_f3_T_000 : lazyT 3 false false false = 0 := by native_decide
theorem lazy_f3_T_001 : lazyT 3 false false true = 0 := by native_decide
theorem lazy_f3_T_010 : lazyT 3 false true false = 2 := by native_decide
theorem lazy_f3_T_011 : lazyT 3 false true true = 4 := by native_decide
theorem lazy_f3_T_100 : lazyT 3 true false false = 0 := by native_decide
theorem lazy_f3_T_101 : lazyT 3 true false true = 2 := by native_decide
theorem lazy_f3_T_110 : lazyT 3 true true false = 1 := by native_decide
theorem lazy_f3_T_111 : lazyT 3 true true true = 3 := by native_decide

/-- Lazy fuel 3: SAT assignments both have countT = 2.
    No UNSAT assignment has countT = 2.
    {000:0, 001:0, 011:4, 100:0, 110:1, 111:3} — none equal 2.
    countT SEPARATES SAT from UNSAT. -/
theorem lazy_f3_sat_value :
    lazyT 3 false true false = 2 ∧ lazyT 3 true false true = 2 :=
  ⟨by native_decide, by native_decide⟩

theorem lazy_f3_separates :
    lazyT 3 false false false ≠ 2 ∧
    lazyT 3 false false true ≠ 2 ∧
    lazyT 3 false true true ≠ 2 ∧
    lazyT 3 true false false ≠ 2 ∧
    lazyT 3 true true false ≠ 2 ∧
    lazyT 3 true true true ≠ 2 :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

/-! ## Part 4: Framework comparison

  Three frameworks tested on the same formula:
    (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂)

  1. DynSemiring obs normalization:
     countF₀ = 92 for ALL 8 assignments at depth 5.
     TOTAL indistinguishability. No scalar separates.

  2. SK combinatory reduction:
     countK collides at EVERY fuel level 0-30.
     No scalar separates at any intermediate step.

  3. Boolean Expr ADT (this file):
     Eager: countT separates at fuel 2.
     Lazy: countT separates at fuel 3.
     SEPARATION ACHIEVED.

  The critical difference: ADT pattern matching ELIMINATES
  structure (terms shrink monotonically toward T or F),
  while SK reduction and Leibniz normalization CREATE
  structure (S-duplication, oplus tree expansion).

  Indistinguishability appears to require structural
  proliferation — a reduction mechanism that grows the
  term before (or instead of) shrinking it.
-/

end Expr
end BoolExpr
