/-
  Untyped Expression Rewriting
  ============================

  Strip the type system from the Expr ADT: represent T, F, not,
  and, or as opaque numeric tags in a generic untyped term algebra.
  Rewrite rules match on tag values, not on types.

  The question: does removing type distinctions (while keeping
  the same rewrite rules) restore indistinguishability, or does
  the truth-table structure of the rules suffice for separation?

  Symbol tags:
    0 = "true"    (leaf)
    1 = "false"   (leaf)
    2 = "not"     (unary: left child is argument, right ignored)
    3 = "and"     (binary)
    4 = "or"      (binary)
-/

import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace UntypedExpr

/-! ## Syntax: untyped tagged binary trees -/

/-- Untyped terms: tagged binary tree. Every node has a Nat tag
    and optionally left/right children. Leaves are nodes with
    tag 0 (true) or 1 (false) and dummy children. -/
inductive UTerm where
  | leaf : Nat → UTerm
  | node : Nat → UTerm → UTerm → UTerm
  deriving DecidableEq, Repr

namespace UTerm

/-! ## Constructors -/

def T : UTerm := .leaf 0
def F : UTerm := .leaf 1
def not' (e : UTerm) : UTerm := .node 2 e (.leaf 0)  -- right child is filler
def and' (a b : UTerm) : UTerm := .node 3 a b
def or' (a b : UTerm) : UTerm := .node 4 a b

/-! ## Measurements -/

/-- Count leaves with tag 0 ("true"). -/
def countTag0 : UTerm → Nat
  | .leaf 0 => 1
  | .leaf _ => 0
  | .node _ l r => countTag0 l + countTag0 r

/-- Count leaves with tag 1 ("false"). -/
def countTag1 : UTerm → Nat
  | .leaf 1 => 1
  | .leaf _ => 0
  | .node _ l r => countTag1 l + countTag1 r

/-- Total node count. -/
def size : UTerm → Nat
  | .leaf _ => 1
  | .node _ l r => 1 + size l + size r

/-! ## Eager rewriting (innermost-first) -/

/-- One step of eager reduction. Reduces children first, then fires head. -/
def eagerStep : UTerm → Option UTerm
  -- Unary: not
  | .node 2 l r =>
    match eagerStep l with
    | some l' => some (.node 2 l' r)
    | none => match l with
      | .leaf 0 => some (.leaf 1)    -- not true → false
      | .leaf 1 => some (.leaf 0)    -- not false → true
      | _ => none
  -- Binary: and
  | .node 3 l r =>
    match eagerStep l with
    | some l' => some (.node 3 l' r)
    | none => match eagerStep r with
      | some r' => some (.node 3 l r')
      | none => match l, r with
        | .leaf 0, .leaf 0 => some (.leaf 0)   -- and true true → true
        | .leaf 0, .leaf 1 => some (.leaf 1)   -- and true false → false
        | .leaf 1, _ => some (.leaf 1)          -- and false _ → false
        | _, _ => none
  -- Binary: or
  | .node 4 l r =>
    match eagerStep l with
    | some l' => some (.node 4 l' r)
    | none => match eagerStep r with
      | some r' => some (.node 4 l r')
      | none => match l, r with
        | .leaf 0, _ => some (.leaf 0)          -- or true _ → true
        | .leaf 1, .leaf 0 => some (.leaf 0)    -- or false true → true
        | .leaf 1, .leaf 1 => some (.leaf 1)    -- or false false → false
        | _, _ => none
  -- Unknown tag or leaf
  | _ => none

/-- Multi-step eager reduction with fuel. -/
def eagerReduce (fuel : Nat) (t : UTerm) : UTerm :=
  match fuel with
  | 0 => t
  | fuel + 1 => match eagerStep t with
    | some t' => eagerReduce fuel t'
    | none => t

/-! ## Lazy rewriting (outermost-first) -/

/-- One step of lazy reduction. Fires head first, then reduces children. -/
def lazyStep : UTerm → Option UTerm
  -- Unary: not
  | .node 2 l r =>
    match l with
    | .leaf 0 => some (.leaf 1)
    | .leaf 1 => some (.leaf 0)
    | _ => match lazyStep l with
      | some l' => some (.node 2 l' r)
      | none => none
  -- Binary: and (short-circuit on false)
  | .node 3 l r =>
    match l with
    | .leaf 1 => some (.leaf 1)          -- and false _ → false
    | .leaf 0 => some r                  -- and true b → b
    | _ => match lazyStep l with
      | some l' => some (.node 3 l' r)
      | none => match lazyStep r with
        | some r' => some (.node 3 l r')
        | none => none
  -- Binary: or (short-circuit on true)
  | .node 4 l r =>
    match l with
    | .leaf 0 => some (.leaf 0)          -- or true _ → true
    | .leaf 1 => some r                  -- or false b → b
    | _ => match lazyStep l with
      | some l' => some (.node 4 l' r)
      | none => match lazyStep r with
        | some r' => some (.node 4 l r')
        | none => none
  | _ => none

/-- Multi-step lazy reduction with fuel. -/
def lazyReduce (fuel : Nat) (t : UTerm) : UTerm :=
  match fuel with
  | 0 => t
  | fuel + 1 => match lazyStep t with
    | some t' => lazyReduce fuel t'
    | none => t

/-! ## SAT formula encoding -/

def mkBool : Bool → UTerm
  | true => T
  | false => F

/-- Same 3-clause formula:
    (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂) -/
def cnf3shared (b0 b1 b2 : Bool) : UTerm :=
  and' (and' (or' (mkBool b0) (mkBool b1))
             (or' (not' (mkBool b0)) (mkBool b2)))
       (or' (not' (mkBool b1)) (not' (mkBool b2)))

/-! ## Measurement helpers -/

def eagerTag0 (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countTag0 (eagerReduce fuel (cnf3shared b0 b1 b2))

def lazyTag0 (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  countTag0 (lazyReduce fuel (cnf3shared b0 b1 b2))

def eagerSz (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  size (eagerReduce fuel (cnf3shared b0 b1 b2))

def lazySz (fuel : Nat) (b0 b1 b2 : Bool) : Nat :=
  size (lazyReduce fuel (cnf3shared b0 b1 b2))

/-! ## Part 1: Convergence -/

theorem eager_converge_sat_010 : eagerReduce 10 (cnf3shared false true false) = .leaf 0 :=
  by native_decide
theorem eager_converge_sat_101 : eagerReduce 10 (cnf3shared true false true) = .leaf 0 :=
  by native_decide
theorem eager_converge_unsat_000 : eagerReduce 10 (cnf3shared false false false) = .leaf 1 :=
  by native_decide
theorem eager_converge_unsat_111 : eagerReduce 10 (cnf3shared true true true) = .leaf 1 :=
  by native_decide

theorem lazy_converge_sat_010 : lazyReduce 10 (cnf3shared false true false) = .leaf 0 :=
  by native_decide
theorem lazy_converge_unsat_000 : lazyReduce 10 (cnf3shared false false false) = .leaf 1 :=
  by native_decide

/-! ## Part 2: Eager evaluation data

  Untyped eager countTag0:
  ```
  Fuel  000(U) 001(U) 010(S) 011(U) 100(U) 101(S) 110(U) 111(U)
  0     3      5      5      7      5      7      7      9
  1     3      5      5      7      5      7      6      8
  2     3      5      5      7      3      5      4      6
  3     3      4      5      6      3      5      4      6
  4     2      3      4      5      2      4      3      5
  5     2      3      2      3      2      4      1      3
  10    0      0      1      0      0      1      0      0
  ```

  Fuel 0-2: 001(U)=5 = 010(S)=5. Collision.
  Fuel 3: SAT={010:5, 101:5}. No UNSAT=5. SEPARATES.
  Fuel 5: 010(S)=2 = 000(U)=2. Collision returns!
  Fuel 10: SAT={1,1}, UNSAT={0,...,0}. Converged, separates.

  Separation is TRANSIENT: appears at fuels 3-4, lost at fuel 5.
-/

-- Fuel 0 collision
theorem untyped_eager_f0_collision :
    eagerTag0 0 false false true = eagerTag0 0 false true false :=
  by native_decide

-- Fuel 3 separation
theorem untyped_eager_f3_sat :
    eagerTag0 3 false true false = 5 ∧ eagerTag0 3 true false true = 5 :=
  ⟨by native_decide, by native_decide⟩

theorem untyped_eager_f3_separates :
    eagerTag0 3 false false false ≠ 5 ∧
    eagerTag0 3 false false true ≠ 5 ∧
    eagerTag0 3 false true true ≠ 5 ∧
    eagerTag0 3 true false false ≠ 5 ∧
    eagerTag0 3 true true false ≠ 5 ∧
    eagerTag0 3 true true true ≠ 5 :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

-- Fuel 5: collision returns
theorem untyped_eager_f5_collision :
    eagerTag0 5 false false false = eagerTag0 5 false true false :=
  by native_decide

/-! ## Part 3: Lazy evaluation data

  Untyped lazy countTag0:
  ```
  Fuel  000(U) 001(U) 010(S) 011(U) 100(U) 101(S) 110(U) 111(U)
  0     3      5      5      7      5      7      7      9
  1     3      5      5      7      5      7      6      8
  2     2      3      4      6      4      6      5      7
  3     0      0      4      6      2      4      3      5
  4     0      0      4      5      2      4      3      5
  5     0      0      3      4      0      3      0      4
  10    0      0      1      0      0      1      0      0
  ```

  Fuel 2: 010(S)=4 = 100(U)=4. Collision.
  Fuel 3: SAT={010:4, 101:4}. No UNSAT=4. SEPARATES.
  Fuel 5: SAT={010:3, 101:3}. No UNSAT=3. Still separates.
-/

-- Fuel 2 collision
theorem untyped_lazy_f2_collision :
    lazyTag0 2 false true false = lazyTag0 2 true false false :=
  by native_decide

-- Fuel 3 separation
theorem untyped_lazy_f3_sat :
    lazyTag0 3 false true false = 4 ∧ lazyTag0 3 true false true = 4 :=
  ⟨by native_decide, by native_decide⟩

theorem untyped_lazy_f3_separates :
    lazyTag0 3 false false false ≠ 4 ∧
    lazyTag0 3 false false true ≠ 4 ∧
    lazyTag0 3 false true true ≠ 4 ∧
    lazyTag0 3 true false false ≠ 4 ∧
    lazyTag0 3 true true false ≠ 4 ∧
    lazyTag0 3 true true true ≠ 4 :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

/-! ## Part 4: Analysis

  Removing types did NOT restore indistinguishability.
  The untyped S-expression version separates just as the
  typed Expr version does.

  The separation comes from the REWRITE RULES, not the types.
  The rules `node 3 [leaf 1, _] → leaf 1` (and false _ → false)
  encode the boolean truth table regardless of whether the terms
  carry type information.

  This confirms: the critical distinction is between:
  - Semantics-aware rules (truth tables as rewrites) → separates
  - Semantics-blind rules (generic structural operations) → indistinguishable

  Both SK combinators and DynSemiring have rules that know nothing
  about booleans: K x y → x, S x y z → xz(yz), and the Leibniz
  product rule. These are generic structural transformations.

  The boolean Expr rules, whether typed or untyped, explicitly
  encode AND/OR/NOT truth tables. That semantic content is what
  enables separation.

  Note: the eager untyped version shows a TRANSIENT separation
  (fuel 3-4) that disappears at fuel 5. This is because the filler
  nodes in not' add extra tag-0 leaves that create accidental
  collisions. The typed version doesn't have this issue because
  not has exactly one child.
-/

end UTerm
end UntypedExpr
