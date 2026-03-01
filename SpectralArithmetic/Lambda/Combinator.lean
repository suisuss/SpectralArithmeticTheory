/-
  SK Combinatory Logic
  ====================

  A minimal, variable-free, first-order term algebra that is
  Turing-complete. SK combinatory logic is equivalent to untyped
  lambda calculus but avoids binding, substitution, and
  alpha-equivalence — making it structurally parallel to the
  DynSemiring Term algebra.

  S and K are the two primitive combinators:
  - K x y → x          (projection / resource discarding)
  - S x y z → x z (y z) (distribution / resource duplication)

  These correspond to the two fundamental operations that
  differentiate linear from full computation:
  - K is weakening (discard a resource)
  - S is contraction (duplicate a resource and distribute)
-/

import Mathlib.Tactic

namespace Combinator

/-! ## Syntax -/

/-- Terms in SK combinatory logic. -/
inductive CombTerm where
  | S : CombTerm
  | K : CombTerm
  | app : CombTerm → CombTerm → CombTerm
  deriving DecidableEq, Repr

namespace CombTerm

/-! ## Standard combinators -/

/-- The identity combinator I = SKK. -/
def I : CombTerm := .app (.app .S .K) .K

/-- Church encoding of true: K (projects to first argument). -/
def cTrue : CombTerm := .K

/-- Church encoding of false: SK (projects to second argument).
    More precisely, KI = K(SKK), but the standard encoding is SK. -/
def cFalse : CombTerm := .app .S .K

-- Boolean operations are defined via direct application
-- rather than combinator encodings, since our focus is
-- on the embedding structure, not combinator programming.

/-! ## Term size -/

/-- Number of nodes in a combinator term. -/
def size : CombTerm → Nat
  | .S => 1
  | .K => 1
  | .app m n => 1 + size m + size n

theorem size_pos (t : CombTerm) : size t ≥ 1 := by
  cases t <;> simp [size] <;> omega

/-! ## One-step reduction -/

/-- One-step head reduction of SK combinatory logic.
    - K x y → x         (K-reduction: discard y)
    - S x y z → xz(yz)  (S-reduction: duplicate z, distribute)
    - Otherwise, try reducing inside applications (left first). -/
def reduceStep : CombTerm → Option CombTerm
  -- K-redex: K x y → x
  | .app (.app .K x) _ => some x
  -- S-redex: S x y z → x z (y z)
  | .app (.app (.app .S x) y) z =>
      some (.app (.app x z) (.app y z))
  -- Reduce inside app (left first, then right)
  | .app m n =>
      match reduceStep m with
      | some m' => some (.app m' n)
      | none => match reduceStep n with
        | some n' => some (.app m n')
        | none => none
  -- Irreducible
  | _ => none

/-- A term is in normal form if no reduction applies. -/
def isNormal (t : CombTerm) : Bool := reduceStep t == none

/-- Multi-step reduction with fuel. -/
def reduce (fuel : Nat) (t : CombTerm) : CombTerm :=
  match fuel with
  | 0 => t
  | fuel + 1 => match reduceStep t with
    | some t' => reduce fuel t'
    | none => t

/-! ## S-reduction duplicates resources -/

/-- S-reduction result has size 3 + sx + sy + 2*sz.
    The duplicated sub-term z appears twice. -/
theorem S_red_size (x y z : CombTerm) :
    size (.app (.app x z) (.app y z)) =
    3 + size x + size y + 2 * size z := by
  simp [size]; omega

/-- S-reduction grows when z is compound (size ≥ 2).
    When z is a primitive (S or K), the duplication doesn't increase size
    because the S-node itself is removed (net: +sz - 1). -/
theorem S_red_grows_compound (x y z : CombTerm) (hz : size z ≥ 2) :
    size (.app (.app x z) (.app y z)) >
    size (.app (.app (.app .S x) y) z) := by
  simp [size]; omega

/-- K-reduction strictly decreases size (discards y). -/
theorem K_red_shrinks (x y : CombTerm) :
    size x < size (.app (.app .K x) y) := by
  simp [size]; omega

/-! ## Basic reduction examples -/

/-- I x → x (via SKK x → K x (K x) → x). -/
theorem I_reduces (x : CombTerm) :
    reduce 2 (.app I x) = x := by
  simp [I, reduce, reduceStep]

/-- K x y → x. -/
theorem K_reduces (x y : CombTerm) :
    reduceStep (.app (.app .K x) y) = some x := by
  rfl

/-- TRUE = K satisfies: TRUE x y →* x. -/
theorem cTrue_select (x y : CombTerm) :
    reduce 1 (.app (.app cTrue x) y) = x := by
  simp [cTrue, reduce, reduceStep]

end CombTerm

end Combinator
