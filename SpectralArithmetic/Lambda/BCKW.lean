/-
  BCKW Combinatory Logic
  ======================

  A second Turing-complete combinator basis for testing SAT
  indistinguishability. BCKW has different reduction dynamics
  from SK:

    B x y z → x (y z)    (composition: no duplication)
    C x y z → x z y      (flip: reorder, no duplication)
    K x y   → x          (constant: discard y)
    W x y   → x y y      (duplicate: copy y, no distribution)

  In SK, S is the sole source of both duplication AND distribution.
  In BCKW, these are separated: W duplicates (without distributing),
  B composes (without duplicating), C permutes. This tests whether
  the indistinguishability depends on S's specific combination of
  duplication-with-distribution.

  Church booleans: TRUE = K, FALSE = K(WK) = KI where I = WK.
-/

import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace BCKWComb

/-! ## Syntax -/

inductive BTerm where
  | B : BTerm
  | C : BTerm
  | K : BTerm
  | W : BTerm
  | app : BTerm → BTerm → BTerm
  deriving DecidableEq, Repr

namespace BTerm

/-! ## Standard combinators -/

/-- Identity: I = WK. WK y → K y y → y. -/
def I : BTerm := .app .W .K

/-- Church TRUE = K (select first). -/
def cTrue : BTerm := .K

/-- Church FALSE = K(WK) = KI (select second). -/
def cFalse : BTerm := .app .K I

/-! ## Term measurements -/

def size : BTerm → Nat
  | .B | .C | .K | .W => 1
  | .app m n => 1 + size m + size n

/-- Count K combinators. -/
def countK : BTerm → Nat
  | .K => 1
  | .B | .C | .W => 0
  | .app m n => countK m + countK n

/-- Count W combinators. -/
def countW : BTerm → Nat
  | .W => 1
  | .B | .C | .K => 0
  | .app m n => countW m + countW n

/-- Count B combinators. -/
def countB : BTerm → Nat
  | .B => 1
  | .C | .K | .W => 0
  | .app m n => countB m + countB n

/-- Count all primitives. -/
def countPrims : BTerm → Nat
  | .B | .C | .K | .W => 1
  | .app m n => countPrims m + countPrims n

/-! ## One-step reduction -/

/-- One-step head reduction for BCKW.
    B x y z → x (y z)
    C x y z → x z y
    K x y   → x
    W x y   → x y y -/
def reduceStep : BTerm → Option BTerm
  -- B-redex: B x y z → x (y z)
  | .app (.app (.app .B x) y) z =>
      some (.app x (.app y z))
  -- C-redex: C x y z → x z y
  | .app (.app (.app .C x) y) z =>
      some (.app (.app x z) y)
  -- K-redex: K x y → x
  | .app (.app .K x) _ => some x
  -- W-redex: W x y → x y y
  | .app (.app .W x) y =>
      some (.app (.app x y) y)
  -- Reduce inside app (left first, then right)
  | .app m n =>
      match reduceStep m with
      | some m' => some (.app m' n)
      | none => match reduceStep n with
        | some n' => some (.app m n')
        | none => none
  | _ => none

/-- Multi-step reduction with fuel. -/
def reduce (fuel : Nat) (t : BTerm) : BTerm :=
  match fuel with
  | 0 => t
  | fuel + 1 => match reduceStep t with
    | some t' => reduce fuel t'
    | none => t

/-! ## Basic verification -/

/-- I x → x (via WK x → K x x → x). -/
theorem I_reduces (x : BTerm) :
    reduce 2 (.app I x) = x := by
  simp [I, reduce, reduceStep]

/-- K x y → x. -/
theorem K_reduces (x y : BTerm) :
    reduce 1 (.app (.app .K x) y) = x := by
  simp [reduce, reduceStep]

/-- TRUE selects first: K x y → x. -/
theorem cTrue_select (x y : BTerm) :
    reduce 1 (.app (.app cTrue x) y) = x := by
  simp [cTrue, reduce, reduceStep]

/-! ## SAT formula encoding -/

/-- Boolean operations via Church encoding. -/
def cOr (p q : BTerm) : BTerm := .app (.app p cTrue) q
def cAnd (p q : BTerm) : BTerm := .app (.app p q) cFalse
def cNot (p : BTerm) : BTerm := .app (.app p cFalse) cTrue

def mkBool : Bool → BTerm
  | true => cTrue
  | false => cFalse

/-- 3-clause shared-variable formula:
    (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂) -/
def cnf3shared (b0 b1 b2 : Bool) : BTerm :=
  cAnd (cAnd (cOr (mkBool b0) (mkBool b1))
             (cOr (cNot (mkBool b0)) (mkBool b2)))
       (cOr (cNot (mkBool b1)) (cNot (mkBool b2)))

/-! ## Measurement helpers -/

def bckwK (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countK (reduce fuel (cnf3shared b0 b1 b2))

def bckwW (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countW (reduce fuel (cnf3shared b0 b1 b2))

def bckwSz (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  size (reduce fuel (cnf3shared b0 b1 b2))

def bckwPrims (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countPrims (reduce fuel (cnf3shared b0 b1 b2))

/-! ## Part 1: Convergence -/

/-- BCKW SAT → K (TRUE). -/
theorem converge_sat_010 : reduce 30 (cnf3shared false true false) = .K :=
  by native_decide
theorem converge_sat_101 : reduce 30 (cnf3shared true false true) = .K :=
  by native_decide

/-- BCKW UNSAT → K(WK) (FALSE = KI). -/
theorem converge_unsat_000 :
    reduce 30 (cnf3shared false false false) = .app .K (.app .W .K) :=
  by native_decide
theorem converge_unsat_111 :
    reduce 30 (cnf3shared true true true) = .app .K (.app .W .K) :=
  by native_decide

/-- TRUE = K has 1 K. FALSE = K(WK) has 2 K's.
    Unlike SK where both have 1 K, BCKW's encoding gives
    different K-counts at convergence. -/
theorem converge_countK_sat : bckwK 30 false true false = 1 := by native_decide
theorem converge_countK_unsat : bckwK 30 false false false = 2 := by native_decide

/-! ## Part 2: Intermediate data

  BCKW countK at each fuel level:
  ```
  Fuel  000(U) 001(U) 010(S) 011(U) 100(U) 101(S) 110(U) 111(U)
  0     28     26     26     24     26     24     24     22
  1     26     24     24     22     23     21     22     20
  2     28     26     25     23     20     18     19     17
  3     25     23     23     21     18     16     17     15
  4     16     15     20     18     16     14     15     13
  5     18     17     17     15     18     15     17     14
  6     15     14     18     16     15     13     14     12
  7     3      3      16     14     3      10     3      9
  10    2      2      8      7      2      6      2      9
  15    2      2      3      2      2      1      2      2
  20    2      2      1      2      2      1      2      2
  30    2      2      1      2      2      1      2      2
  ```

  Fuel 0-3: SAT/UNSAT collisions (001(U) = 010(S) at each step).
  Fuel 4: SEPARATES. SAT={010:20, 101:14}, no UNSAT matches either.
  Fuel 5: Collision returns (010(S)=17 = 001(U)=17).
  Fuel 6+: SEPARATES at most fuel levels.
  Fuel 20+: Converged. SAT=1, UNSAT=2.

  Unlike SK where collisions persist at EVERY fuel level,
  BCKW shows transient collisions that resolve by fuel 6.
-/

-- Fuel 0: collision
theorem bckw_f0_collision :
    bckwK 0 false false true = bckwK 0 false true false :=
  by native_decide

-- Fuel 5: collision returns
theorem bckw_f5_collision :
    bckwK 5 false false true = bckwK 5 false true false :=
  by native_decide

-- Fuel 7: separation
theorem bckw_f7_sat_010 : bckwK 7 false true false = 16 := by native_decide
theorem bckw_f7_sat_101 : bckwK 7 true false true = 10 := by native_decide

theorem bckw_f7_no_unsat_16 :
    bckwK 7 false false false ≠ 16 ∧
    bckwK 7 false false true ≠ 16 ∧
    bckwK 7 false true true ≠ 16 ∧
    bckwK 7 true false false ≠ 16 ∧
    bckwK 7 true true false ≠ 16 ∧
    bckwK 7 true true true ≠ 16 :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

theorem bckw_f7_no_unsat_10 :
    bckwK 7 false false false ≠ 10 ∧
    bckwK 7 false false true ≠ 10 ∧
    bckwK 7 false true true ≠ 10 ∧
    bckwK 7 true false false ≠ 10 ∧
    bckwK 7 true true false ≠ 10 ∧
    bckwK 7 true true true ≠ 10 :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

/-! ## Part 3: Why BCKW separates but SK doesn't

  The critical difference is in the Church encoding of FALSE:
  - SK:   FALSE = SK.   countK(SK) = 1.  countK(K) = 1.  Same!
  - BCKW: FALSE = K(WK). countK(K(WK)) = 2. countK(K) = 1. Different!

  In SK, TRUE and FALSE have the same K-count, so any formula
  that evaluates to TRUE or FALSE will have the same K-count
  at convergence. The measure is structurally incapable of
  separating the final values.

  In BCKW, TRUE and FALSE have different K-counts (1 vs 2),
  so the measure CAN separate — and does, once enough reduction
  has occurred to bring the formula close to its final value.

  This means the SK indistinguishability was partly an artifact
  of countK being the wrong measure for that encoding — TRUE and
  FALSE happen to be indistinguishable under countK in SK.

  The deeper question: is there ANY scalar measure of SK terms
  that separates TRUE from FALSE? countK doesn't work (both = 1).
  countS: K has 0 S, SK has 1 S — DIFFERENT. So countS should
  separate in SK too!

  This needs immediate testing.
-/

end BTerm
end BCKWComb
