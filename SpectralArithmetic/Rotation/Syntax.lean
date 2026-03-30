/-
  Rotation Calculus: Syntax
  =========================

  A minimal formal language for reasoning about computational complexity.
  Three term constructors, one rewrite rule, one constraint parameter.

  The language makes P vs NP visible as a structural property:
  - Verification = run the rotation rule on a given arrangement (linear)
  - Search = find an arrangement where every rotation step passes (NP)

  Design:
  - `ground` : the irreducible element, fixed point of observation
  - `pair`   : the only way to build structure (nesting = storage)
  - `observe`: marks a subterm for the next rewrite step
-/

import Mathlib.Tactic

namespace RotationCalculus

/-! ## Terms -/

/-- Terms in the rotation calculus.
    A term is either the irreducible ground state, a pair of terms,
    or an observation marker wrapping a term. -/
inductive Term where
  | ground : Term
  | pair : Term → Term → Term
  | observe : Term → Term
  deriving DecidableEq, Repr

namespace Term

/-! ## Structural measures -/

/-- The size of a term: number of `pair` constructors. -/
def size : Term → ℕ
  | .ground => 0
  | .pair a b => 1 + size a + size b
  | .observe t => size t

/-- The depth of a term: maximum nesting level. -/
def depth : Term → ℕ
  | .ground => 0
  | .pair a b => 1 + max (depth a) (depth b)
  | .observe t => depth t

/-- Total number of constructors (ground + pair + observe). -/
def constructorCount : Term → ℕ
  | .ground => 1
  | .pair a b => 1 + constructorCount a + constructorCount b
  | .observe t => 1 + constructorCount t

/-- Count of `pair` constructors under the outermost `observe`.
    This is the termination measure: it strictly decreases at each rewrite step. -/
def pairsUnderObserve : Term → ℕ
  | .observe t => t.size
  | _ => 0

/-! ## List notation -/

/-- Build a flat list term from a list of elements.
    `fromList [a, b, c] = pair(a, pair(b, pair(c, ground)))` -/
def fromList : List Term → Term
  | [] => .ground
  | t :: ts => .pair t (fromList ts)

/-- Extract elements from a flat list term. -/
def toList : Term → List Term
  | .pair a b => a :: toList b
  | _ => []

/-- The number of elements in a flat list term. -/
def listLength : Term → ℕ
  | .pair _ b => 1 + listLength b
  | _ => 0

/-! ## Well-formedness -/

/-- A term has no `observe` constructors. -/
def observeFree : Term → Prop
  | .ground => True
  | .pair a b => observeFree a ∧ observeFree b
  | .observe _ => False

/-- Boolean check for observeFree. -/
def observeFreeBool : Term → Bool
  | .ground => true
  | .pair a b => observeFreeBool a && observeFreeBool b
  | .observe _ => false

/-- observeFreeBool reflects observeFree. -/
theorem observeFreeBool_iff (t : Term) : observeFreeBool t = true ↔ observeFree t := by
  induction t with
  | ground => simp [observeFreeBool, observeFree]
  | pair a b ih_a ih_b =>
    simp [observeFreeBool, observeFree, Bool.and_eq_true]
    exact ⟨fun ⟨ha, hb⟩ => ⟨ih_a.mp ha, ih_b.mp hb⟩,
           fun ⟨ha, hb⟩ => ⟨ih_a.mpr ha, ih_b.mpr hb⟩⟩
  | observe _ => simp [observeFreeBool, observeFree]

/-- A term is a well-formed computation: `observe` wrapping an observe-free body. -/
def wellFormed : Term → Prop
  | .observe t => observeFree t
  | .ground => True
  | _ => False

/-- All leaves are `ground`. -/
def groundLeaves : Term → Prop
  | .ground => True
  | .pair a b => groundLeaves a ∧ groundLeaves b
  | .observe t => groundLeaves t

/-! ## Basic lemmas -/

@[simp]
theorem size_ground : size .ground = 0 := rfl

@[simp]
theorem size_pair (a b : Term) : size (.pair a b) = 1 + size a + size b := rfl

@[simp]
theorem size_observe (t : Term) : size (.observe t) = size t := rfl

@[simp]
theorem depth_ground : depth .ground = 0 := rfl

theorem fromList_toList_id {ts : List Term} (h : ∀ t ∈ ts, observeFree t) :
    toList (fromList ts) = ts := by
  induction ts with
  | nil => simp [fromList, toList]
  | cons t ts ih =>
    simp [fromList, toList]
    exact ih (fun t' ht' => h t' (List.mem_cons_of_mem t ht'))

theorem listLength_fromList (ts : List Term) :
    listLength (fromList ts) = ts.length := by
  induction ts with
  | nil => simp [fromList, listLength]
  | cons t ts ih => simp [fromList, listLength, ih]; omega

end Term

end RotationCalculus
