/-
  Spectral Arithmetic: ZF Test Suite (Path F)
  ============================================

  Tests ZF axioms against the process framework using sets-as-predicates.

  Architecture
  ------------

  The ZF interpretation has two layers:

  1. **Logic layer** (metatheoretic): Sets are predicates (State → Prop),
     membership is predicate application, boolean operations are propositional
     connectives. In Lean's type theory, this layer is built-in.

  2. **Arithmetic layer** (framework): The orbit, eigenvalue theorem,
     successor closure, and infiniteness come from the framework's axioms
     (A1-B5). The framework also implements boolean logic algebraically:
     {z, f₀} under compose/oplus/oneg forms a boolean algebra (Part 1).

  The gap between these layers is structural: in any type-theoretic
  formalization, the metatheory provides some logical strength. The
  axioms F1-F3 (Part 2) make explicit what the framework contributes
  beyond the metatheory.

  Dependency Table
  ----------------

  | ZF Axiom       | Framework axioms used                      | F axiom |
  |----------------|-------------------------------------------|---------|
  | Extensionality | — (metatheory: funext + propext)           | —       |
  | Empty Set      | — (metatheory: constant function)          | —       |
  | Pairing        | — (metatheory: equality predicate)         | —       |
  | Union          | — (metatheory: ∃ over predicates)          | F2      |
  | Power Set      | — (metatheory: function space)             | F2      |
  | Infinity       | A1-B5 (orbit, eigenvalue thm, char zero)  | F1      |
  | Separation     | — (metatheory: ∧ of predicates)           | —       |
  | Replacement    | — (metatheory: ∃ over domain)             | F3      |
  | Foundation     | — (metatheory: type stratification)       | —       |

  Key insight: 5 of 9 ZF axioms are metatheoretic (hold for ANY type
  State with no axioms). The framework's algebraic axioms contribute
  only to Infinity (ZF6). F1-F3 are trivially satisfied in Lean but
  would be non-trivial in a first-order metatheory — they correspond
  to ZF's Infinity, Power Set, and Replacement axioms.
-/

import SpectralArithmetic.Complete

namespace SpectralMonoid

/-! ## Part 1: Framework Boolean Algebra

The framework's algebraic operations implement boolean logic on the
two-element subset {z, f₀} ⊆ State:

  TRUE  = f₀  (multiplicative identity, ring 1)
  FALSE = z   (additive identity / multiplicative annihilator, ring 0)

This uses the ring convention (1 = true, 0 = false), NOT the eigenvalue
convention from the theory docs (which maps TRUE ↔ f₁, FALSE ↔ f₀).
The ring convention is correct algebraically:

  AND(a, b) = compose(a, b)        — A6: z annihilates; A2: f₀ is identity
  NOT(a)    = oplus(f₀, oneg(a))   — C2: ⊖ gives additive inverse
  OR(a, b)  = NOT(AND(NOT a, NOT b)) — De Morgan

These correspondences use axioms A2, A5, A6 (compose), B1 (oplus),
C2 (oneg). This establishes that the framework CAN express boolean
logic through its own algebraic operations — the logic layer is not
merely metatheoretic.

Note: The eigenvalue convention (TRUE = f₁) is used for COUNTING
(cardinality = eigenvalue of the product of membership indicators).
The ring convention (TRUE = f₀) is used for BOOLEAN ALGEBRA.
These serve different purposes and are both valid. -/

section BoolAlg

variable {State : Type*} [DynIntDomain State]

open DynSemiring DynIntDomain

/-! ### AND = compose on {z, f₀}

compose restricted to {z, f₀} acts as boolean AND because:
- z is the annihilator (A6): compose(z, x) = z  → FALSE AND x = FALSE
- f₀ is the identity (A2): compose(f₀, x) = x   → TRUE AND x = x -/

theorem band_ff : compose (z : State) z = z := compose_z z
theorem band_ft : compose (z : State) f₀ = z := compose_z f₀
theorem band_tf : compose (f₀ : State) z = z := compose_z_right f₀
theorem band_tt : compose (f₀ : State) f₀ = f₀ := compose_f₀ f₀

/-! ### NOT = oplus(f₀, oneg(·)) on {z, f₀}

NOT(z)  = f₀ ⊕ ⊖z = f₀ ⊕ z = f₀     (oneg_z, oplus_z_right)
NOT(f₀) = f₀ ⊕ ⊖f₀ = z               (oneg_cancel) -/

/-- Boolean NOT on State: a ↦ f₀ ⊕ ⊖a -/
def bnot (a : State) : State := oplus f₀ (oneg a)

theorem bnot_false : bnot (z : State) = f₀ := by
  unfold bnot; simp

theorem bnot_true : bnot (f₀ : State) = z :=
  oneg_cancel f₀

/-! ### NOT is an involution on {z, f₀} -/

theorem bnot_bnot_false : bnot (bnot (z : State)) = z := by
  unfold bnot; simp

theorem bnot_bnot_true : bnot (bnot (f₀ : State)) = f₀ := by
  unfold bnot; simp

/-! ### OR via De Morgan on {z, f₀}

OR(a, b) = NOT(AND(NOT(a), NOT(b))) -/

/-- Boolean OR on State via De Morgan: NOT(AND(NOT a, NOT b)) -/
def bor (a b : State) : State := bnot (compose (bnot a) (bnot b))

theorem bor_ff : bor (z : State) z = z := by
  unfold bor bnot; simp

theorem bor_ft : bor (z : State) f₀ = f₀ := by
  unfold bor bnot; simp

theorem bor_tf : bor (f₀ : State) z = f₀ := by
  unfold bor bnot; simp

theorem bor_tt : bor (f₀ : State) f₀ = f₀ := by
  unfold bor bnot; simp

/-! ### Summary

The truth tables are verified:

  | a  | b  | AND(a,b)     | NOT(a) | OR(a,b)  |
  |----|----|-----------   |--------|----------|
  | z  | z  | z  (= z)     | f₀     | z  (= z) |
  | z  | f₀ | z  (= z)     | f₀     | f₀       |
  | f₀ | z  | z  (= z)     | z      | f₀       |
  | f₀ | f₀ | f₀ (= f₀)   | z      | f₀       |

All proofs use only: A2, A5, A6 (compose), B1 (oplus), C2 (oneg),
and the non-degeneracy axiom f₀ ≠ z. No metatheoretic logic required
for the boolean operations themselves. -/

end BoolAlg

/-! ## Part 2: Path F Axioms (F1-F3)

These axioms lift the framework from PA-strength to ZF-strength.
They assert that certain infinite collections exist as completed objects.

In Lean's type theory (CIC), F1-F3 are trivially satisfied — Lean's
Prop universe and function types provide the required collections
automatically. In a first-order metatheory, these would be non-trivial
axioms carrying real content. We state them as a typeclass to:

  (a) Document the logical structure (which ZF axiom depends on which)
  (b) Maintain parity with the pen-and-paper theory (20 axioms total)
  (c) Enable future formalization in weaker metatheories

The trivial instance (Part 2b) demonstrates that Lean satisfies F1-F3
automatically — making the metatheoretic contribution explicit. -/

/-- Set-theoretic closure axioms. Extends the framework from PA to ZF strength.

    F1 corresponds to ZF's Axiom of Infinity.
    F2 corresponds to ZF's Power Set axiom.
    F3 corresponds to ZF's Replacement schema. -/
class DynZF (State : Type*) extends DynComplete State where
  /-- F1: The orbit {Sⁿ(f₀) : n ∈ ℕ} exists as a completed predicate.
      This is the step from potential infinity (generation rule S) to
      actual infinity (the completed set ℕ as a single object). -/
  orbitPred : State → Prop
  orbitPred_spec : ∀ s, orbitPred s ↔ isNat s

  /-- F2: For any predicate A on State, the collection of all
      sub-predicates exists as a higher-level predicate.
      This gives the power set of any set-as-predicate. -/
  subPredExists : ∀ (A : State → Prop),
    ∃ (P : (State → Prop) → Prop),
      ∀ S, P S ↔ (∀ x, S x → A x)

  /-- F3: For any function F and predicate A, the image predicate exists.
      This gives the replacement schema: images of sets are sets. -/
  imagePredExists : ∀ (F : State → State) (A : State → Prop),
    ∃ (B : State → Prop),
      ∀ y, B y ↔ (∃ x, A x ∧ F x = y)

/-! ### Trivial instance: Lean's type theory satisfies F1-F3 automatically.

This instance makes explicit that F1-F3 are metatheoretic in Lean.
The proofs are all `Iff.rfl` — the axioms are definitional. -/

instance instDynZF {State : Type*} [DynComplete State] : DynZF State where
  orbitPred := isNat
  orbitPred_spec := fun _ => Iff.rfl
  subPredExists := fun A =>
    ⟨fun S => ∀ x, S x → A x, fun _ => Iff.rfl⟩
  imagePredExists := fun F A =>
    ⟨fun y => ∃ x, A x ∧ F x = y, fun _ => Iff.rfl⟩

/-! ## Part 3: Set-Theoretic Definitions -/

section SetOps

variable {State : Type*}

/-- Empty set: the always-false predicate (ZF2) -/
def emptySet : State → Prop := fun _ => False

/-- Pairing: {a, b} (ZF3) -/
def pairSet (a b : State) : State → Prop := fun x => x = a ∨ x = b

/-- Binary union: A ∪ B -/
def unionSet (A B : State → Prop) : State → Prop := fun x => A x ∨ B x

/-- Intersection: A ∩ B -/
def interSet (A B : State → Prop) : State → Prop := fun x => A x ∧ B x

/-- Complement: Aᶜ -/
def complSet (A : State → Prop) : State → Prop := fun x => ¬ A x

/-- Separation: {x ∈ A : φ(x)} (ZF7) -/
def sepSet (A : State → Prop) (φ : State → Prop) : State → Prop :=
  fun x => A x ∧ φ x

/-- Image of a set under a function (ZF8) -/
def imageSet (F : State → State) (A : State → Prop) : State → Prop :=
  fun y => ∃ x, A x ∧ F x = y

/-- Subset relation -/
def subsetRel (A B : State → Prop) : Prop := ∀ x, A x → B x

/-- Power set: the collection of all subsets (ZF5) -/
def powerSetPred (A : State → Prop) : (State → Prop) → Prop :=
  fun S => subsetRel S A

/-- Big union of a family of sets (ZF4) -/
def bigUnionSet (F : (State → Prop) → Prop) : State → Prop :=
  fun x => ∃ S, F S ∧ S x

end SetOps

/-! ## Part 4: ZF Axiom Verification -/

namespace ZFTest

/-! ### 4a: Metatheoretic axioms

These hold for ANY type State with no algebraic structure.
They follow from Lean's type theory (funext, propext, function types,
existential quantification). In the framework's two-layer architecture,
these are provided by the logic layer. -/

section Metatheoretic

variable {State : Type*}

/-- **ZF1: Extensionality.** Two predicates (sets) are equal iff they agree
    on all inputs. Uses: funext + propext (metatheory). -/
theorem zf1_extensionality (A B : State → Prop)
    (h : ∀ x, A x ↔ B x) : A = B :=
  funext fun x => propext (h x)

/-- **ZF2: Empty Set.** The always-false predicate exists.
    Uses: constant function (metatheory). -/
theorem zf2_empty_set : ∃ A : State → Prop, ∀ x, ¬ A x :=
  ⟨emptySet, fun _ h => h⟩

/-- **ZF3: Pairing.** For any a, b, the set {a, b} exists.
    Uses: equality predicate + disjunction (metatheory). -/
theorem zf3_pairing (a b : State) :
    ∃ C : State → Prop, ∀ x, C x ↔ (x = a ∨ x = b) :=
  ⟨pairSet a b, fun _ => Iff.rfl⟩

/-- **ZF7: Separation.** For any set A and property φ, {x ∈ A : φ(x)} exists.
    Uses: conjunction of predicates (metatheory). -/
theorem zf7_separation (A : State → Prop) (φ : State → Prop) :
    ∃ B : State → Prop, ∀ x, B x ↔ (A x ∧ φ x) :=
  ⟨sepSet A φ, fun _ => Iff.rfl⟩

/-! ### ZF9: Foundation

Type stratification prevents self-membership. In Lean's type system,
`s : State` and `S : State → Prop` are different types. The expression
`s ∈ s` (applying a state to itself) is ill-typed. Foundation holds by
type-theoretic construction, not by axiom. -/

/-! ### ZF10: Choice

Independent — same status as in ZF. Neither provable nor refutable
from the algebraic axioms. Lean's `Classical.choice` provides it. -/

end Metatheoretic

/-! ### 4b: Framework-dependent axioms

These require the framework's algebraic structure and/or F1-F3. -/

section FrameworkDependent

variable {State : Type*} [DynZF State]

open DynSemiring

/-! #### ZF4: Union (infinite case requires F2) -/

omit [DynZF State] in
/-- **ZF4: Union.** For any family F of sets, the union ⋃F exists.
    Finite case: iterated OR (metatheory).
    Infinite case: existential quantification over predicate space (F2). -/
theorem zf4_union (F : (State → Prop) → Prop) :
    ∃ A : State → Prop, ∀ x, A x ↔ ∃ B, F B ∧ B x :=
  ⟨bigUnionSet F, fun _ => Iff.rfl⟩

/-! #### ZF5: Power Set (requires F2) -/

/-- **ZF5: Power Set.** For any set A, the power set P(A) exists.
    Uses F2 (predicate comprehension) for the infinite case. -/
theorem zf5_powerset (A : State → Prop) :
    ∃ B : (State → Prop) → Prop, ∀ C, B C ↔ subsetRel C A :=
  DynZF.subPredExists A

/-! #### ZF6: Infinity (requires F1 + algebraic structure) -/

/-- The natural number orbit predicate, obtained from F1. -/
def natSet : State → Prop := DynZF.orbitPred

/-- f₀ is in the natural number set. Uses: F1 + P1 (f₀ ∈ ℕ). -/
theorem natSet_f₀ : natSet (f₀ : State) :=
  (DynZF.orbitPred_spec f₀).mpr P1_zero_is_nat

/-- The orbit is closed under successor. Uses: F1 + P2 (closure under S). -/
theorem natSet_succ {s : State} (hs : natSet s) :
    natSet (succ s) :=
  (DynZF.orbitPred_spec _).mpr (P2_succ_closed s ((DynZF.orbitPred_spec s).mp hs))

/-- **ZF6: Axiom of Infinity.** The natural number orbit is an inductive set:
    it contains f₀ and is closed under successor.

    Uses: F1 (completed orbit), A1-B5 (eigenvalue theorem → infinite orbit),
    P1-P2 (orbit membership). This is the only ZF axiom that requires
    the framework's algebraic structure. -/
theorem zf6_infinity :
    ∃ A : State → Prop,
      A (f₀ : State) ∧ ∀ x, A x → A (succ x) :=
  ⟨natSet, natSet_f₀, fun _ => natSet_succ⟩

/-- The orbit is infinite. Uses: eigenvalue theorem + characteristic zero (B5).
    This is A8 derived as a theorem (Semiring.lean), not an axiom. -/
theorem natSet_infinite :
    ∀ n : ℕ, n ≥ 1 → iterS (State := State) n ≠ f₀ :=
  InfiniteOrbit.no_cycle

/-! #### ZF8: Replacement (requires F3) -/

/-- **ZF8: Replacement.** For any function F and set A, the image F[A] exists.
    Uses F3 (definable image closure). -/
theorem zf8_replacement (F : State → State) (A : State → Prop) :
    ∃ B : State → Prop, ∀ y, B y ↔ ∃ x, A x ∧ F x = y :=
  DynZF.imagePredExists F A

end FrameworkDependent

/-! ## Part 5: Derived Set-Theoretic Results -/

section Derived

variable {State : Type*}

/-- Binary union is a special case of big union -/
theorem binary_union_eq (A B : State → Prop) :
    bigUnionSet (fun S => S = A ∨ S = B) = unionSet A B := by
  funext x
  simp only [bigUnionSet, unionSet]
  exact propext ⟨
    fun ⟨S, hS, hx⟩ => hS.elim (fun h => Or.inl (h ▸ hx)) (fun h => Or.inr (h ▸ hx)),
    fun h => h.elim (fun hx => ⟨A, Or.inl rfl, hx⟩) (fun hx => ⟨B, Or.inr rfl, hx⟩)⟩

/-- Separation equals intersection with a property -/
theorem sep_eq_inter (A : State → Prop) (φ : State → Prop) :
    sepSet A φ = interSet A φ := rfl

/-- Empty set is a subset of everything -/
theorem empty_subset (A : State → Prop) : subsetRel (emptySet : State → Prop) A :=
  fun _ h => h.elim

/-- Every set is a subset of itself -/
theorem subset_refl' (A : State → Prop) : subsetRel A A :=
  fun _ h => h

/-- The empty set is in the power set of anything -/
theorem empty_in_powerset (A : State → Prop) :
    powerSetPred A (emptySet : State → Prop) :=
  empty_subset A

/-- Every set is in its own power set -/
theorem self_in_powerset (A : State → Prop) : powerSetPred A A :=
  subset_refl' A

/-- Separation produces a subset -/
theorem sep_subset (A : State → Prop) (φ : State → Prop) :
    subsetRel (sepSet A φ) A :=
  fun _ ⟨ha, _⟩ => ha

/-- Image of empty set is empty -/
theorem image_empty (F : State → State) :
    imageSet F (emptySet : State → Prop) = emptySet := by
  funext y
  exact propext ⟨fun ⟨_, h, _⟩ => h.elim, fun h => h.elim⟩

end Derived

/-! ## Part 6: Framework Boolean Set Operations

This section connects the algebraic boolean algebra (Part 1) to
set operations, showing that the framework's algebra can express
the set-theoretic operations used in the ZF interpretation.

The key point: Separation (ZF7) can be expressed as compose
(= algebraic AND) on boolean-valued predicates. This means
Separation depends on A2 (identity) and A6 (annihilator) —
framework axioms — not just metatheoretic conjunction.

Similarly, complement can be expressed via bnot (= oplus(f₀, oneg(·))),
depending on B1 (oplus) and C2 (oneg). -/

section AlgebraicSetOps

variable {State : Type*} [DynIntDomain State]

open DynSemiring DynIntDomain

/-- Algebraic separation: given boolean-valued predicates A, φ : State → State
    (returning z or f₀), their AND-composition is compose. -/
def algSep (A φ : State → State) : State → State :=
  fun x => compose (A x) (φ x)

/-- Algebraic complement: given a boolean-valued predicate A : State → State,
    its NOT is bnot. -/
def algCompl (A : State → State) : State → State :=
  fun x => bnot (A x)

/-- Algebraic union: given boolean-valued predicates A, B : State → State,
    their OR is bor. -/
def algUnion (A B : State → State) : State → State :=
  fun x => bor (A x) (B x)

/-- The algebraic empty set: constantly z. -/
def algEmpty : State → State := fun _ => z

/-- The algebraic empty set returns z (= FALSE) on everything.
    Uses: no axioms (definitional). -/
theorem algEmpty_spec (x : State) : algEmpty x = (z : State) := rfl

/-- Algebraic AND preserves the annihilator (FALSE).
    Uses: A6 (compose_z). -/
theorem algSep_false_left (φ : State → State) (x : State) :
    algSep (fun _ => z) φ x = z :=
  compose_z (φ x)

/-- Algebraic AND preserves the identity (TRUE).
    Uses: A2 (compose_f₀). -/
theorem algSep_true_left (φ : State → State) (x : State) :
    algSep (fun _ => f₀) φ x = φ x :=
  compose_f₀ (φ x)

end AlgebraicSetOps

end ZFTest

end SpectralMonoid
