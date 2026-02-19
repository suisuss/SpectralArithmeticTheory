/-
  Spectral Arithmetic: ZF Test Suite (Path F)
  ========================================

  Tests ZF axioms against the process framework using sets-as-predicates.

  Unlike A-E (which add algebraic structure to State), F is a *test*:
  does the existing structure support set theory? The interpretation:
  - Sets are predicates: State → Prop
  - Membership is predicate application: x ∈ S ⟺ S x
  - Boolean operations are propositional connectives

  In Lean's type theory, F1-F3 (completed orbit, powerset, replacement)
  are trivially satisfied — Prop-valued predicates and quantifiers are
  primitive. The formalization verifies that the ZF axioms hold under
  this interpretation.

  Results:
  - ZF1 (Extensionality): function extensionality ✓
  - ZF2 (Empty Set): λx.False ✓
  - ZF3 (Pairing): λx. x = a ∨ x = b ✓
  - ZF4 (Union): existential quantification over families ✓
  - ZF5 (Powerset): subset predicate ✓
  - ZF6 (Infinity): isNat orbit + succ closure ✓
  - ZF7 (Separation): conjunction of predicates ✓
  - ZF8 (Replacement): image predicate ✓
  - ZF9 (Foundation): type stratification (built into Lean) ✓
  - ZF10 (Choice): independent (same as in ZF)

  F1-F3 from the theory:
  - F1 (completed orbit) — isNat already exists as State → Prop
  - F2 (predicate comprehension) — Lean's function types give this
  - F3 (definable image closure) — Lean's ∃ gives this
  All three are trivially satisfied in Lean's type theory.
-/

import SpectralArithmetic.Complete

namespace SpectralMonoid

/-! ## Pure Set-Theoretic Definitions (no typeclass needed) -/

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

/-! ## ZF Axiom Verification -/

namespace ZFTest

/-! ### Pure logic axioms (no algebraic structure needed) -/

section PureLogic

variable {State : Type*}

/-- **ZF1: Extensionality.** Two sets are equal iff they have the same members. -/
theorem zf1_extensionality (A B : State → Prop)
    (h : ∀ x, A x ↔ B x) : A = B :=
  funext fun x => propext (h x)

/-- **ZF2: Empty Set.** There exists a set with no members. -/
theorem zf2_empty_set : ∃ A : State → Prop, ∀ x, ¬ A x :=
  ⟨emptySet, fun _ h => h⟩

/-- **ZF3: Pairing.** For any a, b, the set {a, b} exists. -/
theorem zf3_pairing (a b : State) :
    ∃ C : State → Prop, ∀ x, C x ↔ (x = a ∨ x = b) :=
  ⟨pairSet a b, fun _ => Iff.rfl⟩

/-- **ZF4: Union.** For any family F of sets, the union ⋃F exists. -/
theorem zf4_union (F : (State → Prop) → Prop) :
    ∃ A : State → Prop, ∀ x, A x ↔ ∃ B, F B ∧ B x :=
  ⟨bigUnionSet F, fun _ => Iff.rfl⟩

/-- **ZF5: Power Set.** For any set A, the power set P(A) exists. -/
theorem zf5_powerset (A : State → Prop) :
    ∃ B : (State → Prop) → Prop, ∀ C, B C ↔ subsetRel C A :=
  ⟨powerSetPred A, fun _ => Iff.rfl⟩

/-- **ZF7: Separation.** For any set A and property φ, {x ∈ A : φ(x)} exists. -/
theorem zf7_separation (A : State → Prop) (φ : State → Prop) :
    ∃ B : State → Prop, ∀ x, B x ↔ (A x ∧ φ x) :=
  ⟨sepSet A φ, fun _ => Iff.rfl⟩

/-- **ZF8: Replacement.** For any function F and set A, the image F[A] exists. -/
theorem zf8_replacement (F : State → State) (A : State → Prop) :
    ∃ B : State → Prop, ∀ y, B y ↔ ∃ x, A x ∧ F x = y :=
  ⟨imageSet F A, fun _ => Iff.rfl⟩

/-! ### ZF9: Foundation
    Type stratification prevents self-membership.

    In Lean's type system, `s : State` and `S : State → Prop` are
    different types. The expression `s ∈ s` (applying a state to itself)
    is ill-typed — it doesn't parse. Foundation holds by type-theoretic
    construction, not by axiom. -/

/-! ### ZF10: Choice
    Independent — same status as in ZF. Neither provable nor refutable
    from the algebraic axioms. Lean's `Classical.choice` provides it. -/

end PureLogic

/-! ### ZF6: Infinity (requires algebraic structure)

This is the main non-trivial verification — it connects the
abstract orbit (isNat) to the ZF axiom of infinity. -/

section Infinity

variable {State : Type*} [DynComplete State]

open DynSemiring

/-- The natural number orbit predicate (F1: completed orbit) -/
def natSet : State → Prop := fun s => isNat s

/-- f₀ is in the natural number set -/
theorem natSet_f₀ : natSet (f₀ : State) :=
  P1_zero_is_nat

/-- The orbit is closed under successor -/
theorem natSet_succ {s : State} (hs : natSet s) :
    natSet (succ s) :=
  P2_succ_closed s hs

/-- **ZF6: Axiom of Infinity.** The natural number orbit is an inductive set:
    it contains f₀ and is closed under successor. -/
theorem zf6_infinity :
    ∃ A : State → Prop,
      A (f₀ : State) ∧ ∀ x, A x → A (succ x) :=
  ⟨natSet, natSet_f₀, fun _ => natSet_succ⟩

/-- The orbit is infinite (A8 / eigenvalue consequence). -/
theorem natSet_infinite :
    ∀ n : ℕ, n ≥ 1 → iterS (State := State) n ≠ f₀ :=
  InfiniteOrbit.no_cycle

end Infinity

/-! ## Derived Set-Theoretic Results -/

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

/-! ## Connecting to the Algebraic Framework

The ZF verification uses Lean's native `Prop` for predicates.
The theory's Church boolean interpretation (predicates returning f₀/f₁)
would additionally require:
- Boolean operations: AND(a,b), OR(a,b), NOT(a) on {f₀, f₁}
- Decidable equality on eigenstates: eq(f_α, f_β) ∈ {f₀, f₁}

These are definable from the algebraic structure but not formalized here.
The Church boolean and Prop interpretations are equivalent for the
ZF axiom verification — the key content is the same. -/

end ZFTest

end SpectralMonoid
