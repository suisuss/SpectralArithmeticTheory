/-
  Polynomial Arithmetization
  ==========================

  Encode SAT formulas as integer arithmetic expressions and
  partially expand. This tests whether commutativity is the
  root cause of total indistinguishability.

  Encoding (standard arithmetization):
    x = 0 or 1         (boolean variable)
    NOT x   = 1 - x
    AND a b = a * b
    OR a b  = a + b - a * b

  Normalization: partial expansion via distribution and
  constant folding. Distribution creates structural
  proliferation: mul(a, add(b,c)) → add(mul(a,b), mul(a,c))
  duplicates subterm `a` — analogous to Leibniz and S-dup.

  Key properties:
  - Commutative (a*b = b*a, a+b = b+a)
  - Semantics-blind (distribution/folding are generic algebra)
  - Structural proliferation (distribution duplicates subterms)

  If total indistinguishability holds here, commutativity +
  structural proliferation is the mechanism. If separation
  occurs, commutativity alone is insufficient.
-/

import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PolyArith

/-! ## Syntax -/

/-- Integer arithmetic expressions. -/
inductive PExpr where
  | lit : Int → PExpr
  | add : PExpr → PExpr → PExpr
  | sub : PExpr → PExpr → PExpr
  | mul : PExpr → PExpr → PExpr
  deriving DecidableEq, Repr

namespace PExpr

/-! ## Measurements -/

/-- Count of lit nodes with value 1. -/
def count1 : PExpr → Nat
  | .lit 1 => 1
  | .lit _ => 0
  | .add a b => count1 a + count1 b
  | .sub a b => count1 a + count1 b
  | .mul a b => count1 a + count1 b

/-- Count of lit nodes with value 0. -/
def count0 : PExpr → Nat
  | .lit 0 => 1
  | .lit _ => 0
  | .add a b => count0 a + count0 b
  | .sub a b => count0 a + count0 b
  | .mul a b => count0 a + count0 b

/-- Count of all lit nodes. -/
def countLit : PExpr → Nat
  | .lit _ => 1
  | .add a b => countLit a + countLit b
  | .sub a b => countLit a + countLit b
  | .mul a b => countLit a + countLit b

/-- Total node count. -/
def size : PExpr → Nat
  | .lit _ => 1
  | .add a b => 1 + size a + size b
  | .sub a b => 1 + size a + size b
  | .mul a b => 1 + size a + size b

/-- Count of mul nodes. -/
def countMul : PExpr → Nat
  | .lit _ => 0
  | .add a b => countMul a + countMul b
  | .sub a b => countMul a + countMul b
  | .mul a b => 1 + countMul a + countMul b

/-- Count of add nodes. -/
def countAdd : PExpr → Nat
  | .lit _ => 0
  | .add a b => 1 + countAdd a + countAdd b
  | .sub a b => countAdd a + countAdd b
  | .mul a b => countAdd a + countAdd b

/-! ## Eager expansion (innermost-first)

  Reduces children first, then fires:
  1. Constant folding: lit a ⊕ lit b → lit (a ⊕ b)
  2. Identity/zero rules: 0*a→0, 1*a→a, 0+a→a, a-0→a
  3. Distribution: a*(b+c) → a*b + a*c  (structural proliferation)
-/

def eagerStep : PExpr → Option PExpr
  -- add: reduce children, then fold
  | .add a b =>
    match eagerStep a with
    | some a' => some (.add a' b)
    | none => match eagerStep b with
      | some b' => some (.add a b')
      | none => match a, b with
        | .lit x, .lit y => some (.lit (x + y))
        | .lit 0, _ => some b
        | _, .lit 0 => some a
        | _, _ => none
  -- sub: reduce children, then fold
  | .sub a b =>
    match eagerStep a with
    | some a' => some (.sub a' b)
    | none => match eagerStep b with
      | some b' => some (.sub a b')
      | none => match a, b with
        | .lit x, .lit y => some (.lit (x - y))
        | _, .lit 0 => some a
        | _, _ => none
  -- mul: reduce children, then fold or distribute
  | .mul a b =>
    match eagerStep a with
    | some a' => some (.mul a' b)
    | none => match eagerStep b with
      | some b' => some (.mul a b')
      | none => match a, b with
        | .lit x, .lit y => some (.lit (x * y))
        | .lit 0, _ => some (.lit 0)
        | _, .lit 0 => some (.lit 0)
        | .lit 1, _ => some b
        | _, .lit 1 => some a
        -- Distribution: a * (b + c) → a*b + a*c
        | _, .add p q => some (.add (.mul a p) (.mul a q))
        -- Distribution: (a + b) * c → a*c + b*c
        | .add p q, _ => some (.add (.mul p b) (.mul q b))
        -- Distribution over sub: a * (b - c) → a*b - a*c
        | _, .sub p q => some (.sub (.mul a p) (.mul a q))
        | .sub p q, _ => some (.sub (.mul p b) (.mul q b))
        | _, _ => none
  | _ => none

/-- Multi-step eager expansion with fuel. -/
def eagerExpand (fuel : Nat) (e : PExpr) : PExpr :=
  match fuel with
  | 0 => e
  | fuel + 1 => match eagerStep e with
    | some e' => eagerExpand fuel e'
    | none => e

/-! ## SAT formula encoding -/

def mkBool : Bool → PExpr
  | true => .lit 1
  | false => .lit 0

/-- NOT x = 1 - x -/
def pNot (x : PExpr) : PExpr := .sub (.lit 1) x

/-- AND a b = a * b -/
def pAnd (a b : PExpr) : PExpr := .mul a b

/-- OR a b = a + b - a * b -/
def pOr (a b : PExpr) : PExpr := .sub (.add a b) (.mul a b)

/-- 3-clause shared-variable formula:
    (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂) -/
def cnf3shared (b0 b1 b2 : Bool) : PExpr :=
  pAnd (pAnd (pOr (mkBool b0) (mkBool b1))
             (pOr (pNot (mkBool b0)) (mkBool b2)))
       (pOr (pNot (mkBool b1)) (pNot (mkBool b2)))

/-! ## Measurement helpers -/

def polyC1 (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  count1 (eagerExpand fuel (cnf3shared b0 b1 b2))

def polyC0 (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  count0 (eagerExpand fuel (cnf3shared b0 b1 b2))

def polySz (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  size (eagerExpand fuel (cnf3shared b0 b1 b2))

def polyMul (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countMul (eagerExpand fuel (cnf3shared b0 b1 b2))

def polyAdd (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countAdd (eagerExpand fuel (cnf3shared b0 b1 b2))

def polyLit (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countLit (eagerExpand fuel (cnf3shared b0 b1 b2))

/-! ## Part 1: Convergence -/

theorem converge_sat_010 : eagerExpand 50 (cnf3shared false true false) = .lit 1 :=
  by native_decide
theorem converge_sat_101 : eagerExpand 50 (cnf3shared true false true) = .lit 1 :=
  by native_decide
theorem converge_unsat_000 : eagerExpand 50 (cnf3shared false false false) = .lit 0 :=
  by native_decide
theorem converge_unsat_111 : eagerExpand 50 (cnf3shared true true true) = .lit 0 :=
  by native_decide

/-! ## Part 2: Structural measures are TOTALLY UNIFORM

  size, countMul, countAdd, countLit are identical across ALL 8
  assignments at every fuel level tested. The formula's tree
  structure is the same regardless of which booleans are substituted
  — only the leaf values (lit 0 vs lit 1) differ.
-/

-- Size uniform at fuel 0
theorem size_uniform_f0 :
    polySz 0 false false false = 35 ∧ polySz 0 false false true = 35 ∧
    polySz 0 false true false = 35 ∧ polySz 0 false true true = 35 ∧
    polySz 0 true false false = 35 ∧ polySz 0 true false true = 35 ∧
    polySz 0 true true false = 35 ∧ polySz 0 true true true = 35 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide, by native_decide⟩

-- Size uniform at fuel 5
theorem size_uniform_f5 :
    polySz 5 false false false = 25 ∧ polySz 5 false true false = 25 ∧
    polySz 5 true false true = 25 ∧ polySz 5 true true true = 25 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- Size uniform at fuel 10
theorem size_uniform_f10 :
    polySz 10 false false false = 15 ∧ polySz 10 false true false = 15 ∧
    polySz 10 true false true = 15 ∧ polySz 10 true true true = 15 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- countMul uniform at fuel 0
theorem mul_uniform_f0 :
    polyMul 0 false false false = 5 ∧ polyMul 0 false true false = 5 ∧
    polyMul 0 true false true = 5 ∧ polyMul 0 true true true = 5 :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-! ## Part 3: Value-dependent measures — count1 separates

  count1 (number of lit-1 nodes) depends on WHICH variables are
  true, not just how many. This goes beyond the DynSemiring's
  true-count dependence.

  count1 at each fuel level:
  ```
  Fuel  000(U) 001(U) 010(S) 011(U) 100(U) 101(S) 110(U) 111(U)
  0     6      10     10     14     10     14     14     18
  1     6      10     10     14     10     14     12     16
  5     6      8      9      11     7      11     9      13
  7     5      7      8      10     5      8      7      10
  9     4      6      7      9      4      7      6      9
  10    4      6      5      7      4      7      4      7
  15    1      1      2      1      1      2      1      1
  20    0      0      1      0      0      1      0      0
  ```

  Fuel 0: 001(U)=10 = 010(S)=10. Collision.
  Fuel 7: SAT={010:8, 101:8}. UNSAT={5,7,10,5,7,10}. No UNSAT=8.
    SEPARATES.
  Fuel 15+: SAT={2,2}, UNSAT={1,...,1}. SEPARATES.
-/

-- Fuel 0 collision
theorem poly_f0_collision :
    polyC1 0 false false true = polyC1 0 false true false :=
  by native_decide

-- Fuel 7 separation
theorem poly_f7_sat :
    polyC1 7 false true false = 8 ∧ polyC1 7 true false true = 8 :=
  ⟨by native_decide, by native_decide⟩

theorem poly_f7_separates :
    polyC1 7 false false false ≠ 8 ∧
    polyC1 7 false false true ≠ 8 ∧
    polyC1 7 false true true ≠ 8 ∧
    polyC1 7 true false false ≠ 8 ∧
    polyC1 7 true true false ≠ 8 ∧
    polyC1 7 true true true ≠ 8 :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

/-! ## Part 4: Analysis

  Polynomial arithmetization shows a SPLIT result:

  **Structural measures (size, countMul, countAdd, countLit)**:
  TOTALLY UNIFORM across all assignments at every fuel level.
  The tree shape is identical — only leaf values differ.
  This is trivially true: substituting 0 vs 1 at leaves doesn't
  change the tree structure, only the integer values.

  **Value-dependent measures (count1, count0)**:
  NOT uniform. count1 depends on which variables are true
  (not just how many), and SEPARATES SAT from UNSAT at fuel 7.

  This is fundamentally different from the DynSemiring, where
  even value-dependent measures (countF₀, countF₁) show
  indistinguishability. In the DynSemiring, the Leibniz rule
  creates new structure that entangles values with tree shape.
  In polynomial expansion, distribution also creates structure,
  but the leaf values propagate transparently — a lit-1 stays
  lit-1 regardless of what it's multiplied by.

  The polynomial result does NOT support the commutativity
  hypothesis. Polynomial arithmetic is commutative, yet count1
  separates. The DynSemiring's total indistinguishability must
  come from something more specific than commutativity alone —
  likely the interaction between obs normalization (which
  transforms f₀/f₁ generators via the Leibniz rule) and the
  commutative compose operation.
-/

end PExpr
end PolyArith
