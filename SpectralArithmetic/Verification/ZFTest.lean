/-
  Spectral Arithmetic: ZF Test Suite (Path F)
  ============================================

  Tests ZF axioms against the process framework using an abstract set universe.

  Architecture
  ------------

  The ZF interpretation has two layers:

  1. **Logic layer** (metatheoretic): Lean's CIC provides predicates,
     function types, propositional extensionality. These are always available.

  2. **Set-theoretic layer** (F-axioms): An abstract type `Ens` with a
     membership relation `mem : State → Ens → Prop`. The F-axioms assert
     that specific ensembles exist in `Ens`:
       F1 — the orbit ensemble (Infinity)
       F2 — separation (sub-ensembles)
       F3 — replacement (image ensembles)

  The key design: `Ens` is abstract, NOT `State → Prop`. This makes the
  F-axioms non-trivial — they carry genuine set-theoretic content that
  is NOT provided by CIC alone. Countermodels (Countermodels.lean)
  demonstrate this: restricting `Ens` to finite predicates falsifies F1,
  and restricting to sub-orbit predicates falsifies F3.

  The forward model (Model.lean) instantiates `Ens = State → Prop`,
  recovering the full predicate space. This is correct — the point is
  that OTHER models can restrict `Ens`.

  Dependency Table
  ----------------

  | ZF Axiom       | Source                                    |
  |----------------|-------------------------------------------|
  | Extensionality | ens_ext (from DynZF)                      |
  | Empty Set      | sepEns orbitEns False (derived from F2)    |
  | Pairing        | F1 + F2 + F3 (sep orbit, then image)      |
  | Union          | unionEns₂ (from DynZF, F5)                |
  | Power Set      | powerEns (from DynZF, F4)                 |
  | Infinity       | orbitEns + A1-B5 (eigenvalue thm)         |
  | Separation     | sepEns (from DynZF)                       |
  | Replacement    | imageEns (from DynZF)                     |
  | Foundation     | Type stratification (metatheory)          |
-/

import SpectralArithmetic.Core.Complete

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

/-! ## Part 2: Path F Axioms (F1-F3) with Abstract Set Universe

These axioms lift the framework from PA-strength to ZF-strength.
They introduce an abstract type `Ens` (the set universe) with a
membership relation `mem : State → Ens → Prop`, and assert that
specific ensembles exist.

Unlike the previous formulation where F1-F3 were trivially satisfied
in Lean's CIC (all proofs were `Iff.rfl`), the abstract `Ens` makes
these axioms carry genuine content:

- F1 is non-trivial: the orbit is infinite, so restricting Ens to
  finite predicates falsifies F1 (see Countermodels.lean).
- F2 (separation) is non-trivial: restricting Ens to a singleton
  (only isNat) falsifies F2 (see Countermodels.lean).
- F3 is non-trivial: restricting Ens to sub-orbit predicates
  falsifies F3 when the function maps outside the orbit.

The forward model (Model.lean) uses `Ens = State → Prop`, recovering
the full predicate space. -/

/-- Set-theoretic closure axioms with an abstract set universe.

    Ens is the type of "ensembles" (sets). It is abstract — not
    necessarily `State → Prop`. The F-axioms assert that specific
    ensembles exist, making them genuinely non-trivial.

    F1: The orbit ensemble exists (Infinity).
    F2: Separation — sub-ensembles exist.
    F3: Replacement — image ensembles exist.
    F4: Power ensemble — the family of sub-ensembles exists (Power Set).
    F5: Family union — the union of a family of ensembles exists (Union). -/
class DynZF (State : Type*) extends DynComplete State where
  /-- The abstract set universe -/
  Ens : Type*
  /-- Membership relation: s ∈ A -/
  mem : State → Ens → Prop
  /-- Extensionality: ensembles with the same members are equal -/
  ens_ext : ∀ A B : Ens, (∀ s, mem s A ↔ mem s B) → A = B
  /-- F1: The orbit {Sⁿ(f₀) : n ∈ ℕ} exists as an ensemble.
      This is the step from potential infinity (generation rule S) to
      actual infinity (the completed set ℕ as a single object). -/
  orbitEns : Ens
  orbitEns_spec : ∀ s, mem s orbitEns ↔ isNat s
  /-- F2: Separation — for any ensemble A and predicate φ, the
      sub-ensemble {s ∈ A : φ(s)} exists. -/
  sepEns : Ens → (State → Prop) → Ens
  sepEns_spec : ∀ A φ s, mem s (sepEns A φ) ↔ (mem s A ∧ φ s)
  /-- F3: Replacement — for any function F and ensemble A, the
      image ensemble F[A] exists. -/
  imageEns : (State → State) → Ens → Ens
  imageEns_spec : ∀ F A y, mem y (imageEns F A) ↔ (∃ x, mem x A ∧ F x = y)
  /-- Level-2 ensemble type: sets of ensembles (sets of sets) -/
  Ens₂ : Type*
  /-- Level-2 membership: A ∈₂ P means ensemble A is in the family P -/
  mem₂ : Ens → Ens₂ → Prop
  /-- Level-2 extensionality -/
  ens_ext₂ : ∀ P Q : Ens₂, (∀ A, mem₂ A P ↔ mem₂ A Q) → P = Q
  /-- F4: Power ensemble — for any ensemble A, the family of all
      sub-ensembles of A exists. (ZF5: Power Set) -/
  powerEns : Ens → Ens₂
  powerEns_spec : ∀ A B, mem₂ B (powerEns A) ↔ (∀ s, mem s B → mem s A)
  /-- F5: Family union — for any family of ensembles, their union
      exists as a single ensemble. (ZF4: Union) -/
  unionEns₂ : Ens₂ → Ens
  unionEns₂_spec : ∀ P s, mem s (unionEns₂ P) ↔ (∃ A, mem₂ A P ∧ mem s A)

/-! ## Part 3: Set-Theoretic Definitions

These operate on the abstract Ens type via the membership relation. -/

section SetOps

variable {State : Type*} [DynZF State]

open DynZF

/-- Empty ensemble, derived from F2: separate the orbit by False. -/
def emptyEns : @DynZF.Ens State _ := sepEns orbitEns (fun _ => False)

/-- The empty ensemble has no members. -/
theorem emptyEns_spec (s : State) : ¬mem s emptyEns := by
  intro h
  exact ((sepEns_spec orbitEns _ s).mp h).2

/-- Subset relation on ensembles -/
def ensSubset (A B : @DynZF.Ens State _) : Prop :=
  ∀ s, mem s A → mem s B

end SetOps

/-! We also keep the predicate-level definitions for derived results
    that don't depend on Ens (metatheoretic results). -/

section PredOps

variable {State : Type*}

/-- Empty set: the always-false predicate -/
def emptySet : State → Prop := fun _ => False

/-- Pairing: {a, b} -/
def pairSet (a b : State) : State → Prop := fun x => x = a ∨ x = b

/-- Binary union: A ∪ B -/
def unionSet (A B : State → Prop) : State → Prop := fun x => A x ∨ B x

/-- Intersection: A ∩ B -/
def interSet (A B : State → Prop) : State → Prop := fun x => A x ∧ B x

/-- Complement: Aᶜ -/
def complSet (A : State → Prop) : State → Prop := fun x => ¬ A x

/-- Separation: {x ∈ A : φ(x)} -/
def sepSet (A : State → Prop) (φ : State → Prop) : State → Prop :=
  fun x => A x ∧ φ x

/-- Image of a set under a function -/
def imageSet (F : State → State) (A : State → Prop) : State → Prop :=
  fun y => ∃ x, A x ∧ F x = y

/-- Subset relation on predicates -/
def subsetRel (A B : State → Prop) : Prop := ∀ x, A x → B x

/-- Power set: the collection of all subsets -/
def powerSetPred (A : State → Prop) : (State → Prop) → Prop :=
  fun S => subsetRel S A

/-- Big union of a family of sets -/
def bigUnionSet (F : (State → Prop) → Prop) : State → Prop :=
  fun x => ∃ S, F S ∧ S x

end PredOps

/-! ## Part 4: ZF Axiom Verification -/

namespace ZFTest

/-! ### 4a: ZF axioms from abstract DynZF

These are now genuine consequences of the F-axioms, not metatheoretic
tautologies. Each proof uses the abstract Ens type and its operations. -/

section FromDynZF

variable {State : Type*} [DynZF State]

open DynZF DynSemiring

/-- **ZF1: Extensionality.** Two ensembles with the same members are equal.
    Uses: ens_ext (from DynZF). -/
theorem zf1_extensionality (A B : @DynZF.Ens State _)
    (h : ∀ s, mem s A ↔ mem s B) : A = B :=
  ens_ext A B h

/-- **ZF2: Empty Set.** An ensemble with no members exists.
    Uses: sepEns (F2) on orbitEns with False predicate. -/
theorem zf2_empty_set :
    ∃ A : @DynZF.Ens State _, ∀ s, ¬mem s A :=
  ⟨emptyEns, emptyEns_spec⟩

/-- **ZF7: Separation.** For any ensemble A and predicate φ,
    the sub-ensemble {s ∈ A : φ(s)} exists.
    Uses: sepEns (from DynZF, F2). -/
theorem zf7_separation (A : @DynZF.Ens State _) (φ : State → Prop) :
    ∃ B : @DynZF.Ens State _, ∀ s, mem s B ↔ (mem s A ∧ φ s) :=
  ⟨sepEns A φ, fun s => sepEns_spec A φ s⟩

/-- **ZF8: Replacement.** For any function F and ensemble A,
    the image ensemble F[A] exists.
    Uses: imageEns (from DynZF, F3). -/
theorem zf8_replacement (F : State → State) (A : @DynZF.Ens State _) :
    ∃ B : @DynZF.Ens State _, ∀ y, mem y B ↔ (∃ x, mem x A ∧ F x = y) :=
  ⟨imageEns F A, fun y => imageEns_spec F A y⟩

/-! #### ZF6: Infinity (requires F1 + algebraic structure) -/

/-- The natural number orbit ensemble, obtained from F1. -/
def natEns : @DynZF.Ens State _ := orbitEns

/-- f₀ is in the natural number ensemble. Uses: F1 + P1. -/
theorem natEns_f₀ : mem (f₀ : State) natEns :=
  (orbitEns_spec f₀).mpr P1_zero_is_nat

/-- The orbit ensemble is closed under successor. Uses: F1 + P2. -/
theorem natEns_succ {s : State} (hs : mem s natEns) :
    mem (succ s) natEns :=
  (orbitEns_spec _).mpr (P2_succ_closed s ((orbitEns_spec s).mp hs))

/-- **ZF6: Axiom of Infinity.** The orbit ensemble is an inductive set:
    it contains f₀ and is closed under successor.

    Uses: F1 (orbit ensemble), A1-B5 (eigenvalue theorem → infinite orbit),
    P1-P2 (orbit membership). -/
theorem zf6_infinity :
    ∃ A : @DynZF.Ens State _,
      mem (f₀ : State) A ∧ ∀ x, mem x A → mem (succ x) A :=
  ⟨natEns, natEns_f₀, fun _ => natEns_succ⟩

/-- The orbit is infinite. Uses: eigenvalue theorem + characteristic zero (B5). -/
theorem natEns_infinite :
    ∀ n : ℕ, n ≥ 1 → iterS (State := State) n ≠ f₀ :=
  InfiniteOrbit.no_cycle

/-! #### ZF3: Pairing (from F1 + F2 + F3)

Pairing requires constructing {a, b} as an ensemble. Strategy:
1. Use sepEns on orbitEns to get singletons (separate by equality)
2. Use imageEns to map elements appropriately

For arbitrary a, b : State (not necessarily in the orbit), we
construct {a, b} via separation on the image of a two-element
orbit subset. -/

/-- **ZF3: Pairing.** For any a, b : State, the ensemble {a, b} exists.
    Uses: F1 (orbitEns), F2 (sepEns), F3 (imageEns). -/
theorem zf3_pairing (a b : State) :
    ∃ C : @DynZF.Ens State _, ∀ x, mem x C ↔ (x = a ∨ x = b) := by
  -- Map f₀ ↦ a, everything else ↦ b (using classical decidability)
  haveI : DecidableEq State := Classical.decEq State
  let F : State → State := fun s => if s = f₀ then a else b
  -- Get {f₀, f₁} via separation on orbit
  let twoEns := sepEns orbitEns (fun s => s = (f₀ : State) ∨ s = (f₁ : State))
  -- Take the image under F
  let pairE := imageEns F twoEns
  have hF_f₀ : F (f₀ : State) = a := by
    change (if (f₀ : State) = f₀ then a else b) = a
    rw [if_pos rfl]
  have hF_f₁ : F (f₁ : State) = b := by
    change (if (f₁ : State) = f₀ then a else b) = b
    rw [if_neg (Ne.symm f₀_ne_f₁)]
  exact ⟨pairE, fun x => by
    constructor
    · intro hx
      rw [show pairE = imageEns F twoEns from rfl] at hx
      obtain ⟨w, hw, rfl⟩ := (imageEns_spec F twoEns x).mp hx
      obtain ⟨_, hw'⟩ := (sepEns_spec orbitEns _ w).mp hw
      cases hw' with
      | inl h => left; subst h; exact hF_f₀
      | inr h => right; subst h; exact hF_f₁
    · intro hx
      rw [show pairE = imageEns F twoEns from rfl]
      apply (imageEns_spec F twoEns x).mpr
      cases hx with
      | inl h =>
        exact ⟨f₀, (sepEns_spec orbitEns _ f₀).mpr
          ⟨(orbitEns_spec f₀).mpr P1_zero_is_nat, Or.inl rfl⟩,
          by rw [hF_f₀, h]⟩
      | inr h =>
        exact ⟨f₁, (sepEns_spec orbitEns _ f₁).mpr
          ⟨(orbitEns_spec f₁).mpr ⟨1, by simp [iterS, succ, compose_f₀_right]⟩,
           Or.inr rfl⟩,
          by rw [hF_f₁, h]⟩⟩

/-! #### ZF9: Foundation

Type stratification prevents self-membership. In Lean's type system,
`s : State` and `A : Ens` are different types. The expression
`s ∈ s` (membership of a state in a state) is ill-typed. Foundation
holds by type-theoretic construction, not by axiom. -/

/-! #### ZF10: Choice

Independent — same status as in ZF. Neither provable nor refutable
from the algebraic axioms. Lean's `Classical.choice` provides it. -/

/-! #### ZF5: Power Set (from F4) -/

/-- **ZF5: Power Set.** For any ensemble A, the family of all
    sub-ensembles of A exists as a Level-2 ensemble.
    Uses: powerEns (from DynZF, F4). -/
theorem zf5_powerset (A : @DynZF.Ens State _) :
    ∃ P : @DynZF.Ens₂ State _, ∀ B, mem₂ B P ↔ ensSubset B A :=
  ⟨powerEns A, fun B => powerEns_spec A B⟩

/-! #### ZF4: Union (from F5) -/

/-- **ZF4: Union.** For any family of ensembles P, the union
    exists as a single ensemble.
    Uses: unionEns₂ (from DynZF, F5). -/
theorem zf4_union (P : @DynZF.Ens₂ State _) :
    ∃ A : @DynZF.Ens State _, ∀ s, mem s A ↔ (∃ B, mem₂ B P ∧ mem s B) :=
  ⟨unionEns₂ P, fun s => unionEns₂_spec P s⟩

end FromDynZF

/-! ### 4b: Metatheoretic results (using State → Prop directly)

These hold for ANY type State, using Lean's predicate space.
They don't use Ens and are kept for reference. ZF4 and ZF5
now have Ens-level proofs above (from F4, F5), but the
metatheoretic versions remain as a comparison point. -/

section Metatheoretic

variable {State : Type*}

/-- ZF4 (metatheoretic): Union over a family of predicates. -/
theorem zf4_union_meta (F : (State → Prop) → Prop) :
    ∃ A : State → Prop, ∀ x, A x ↔ ∃ B, F B ∧ B x :=
  ⟨bigUnionSet F, fun _ => Iff.rfl⟩

/-- ZF5 (metatheoretic): Power set as a predicate on predicates. -/
theorem zf5_powerset_meta (A : State → Prop) :
    ∃ B : (State → Prop) → Prop, ∀ C, B C ↔ subsetRel C A :=
  ⟨powerSetPred A, fun _ => Iff.rfl⟩

end Metatheoretic

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

/-! ### Derived results on abstract Ens -/

section DerivedEns

variable {State : Type*} [DynZF State]

open DynZF

/-- Empty ensemble is a sub-ensemble of everything -/
theorem emptyEns_subset (A : @DynZF.Ens State _) : ensSubset emptyEns A :=
  fun s h => absurd h (emptyEns_spec s)

/-- Separation produces a sub-ensemble -/
theorem sepEns_subset (A : @DynZF.Ens State _) (φ : State → Prop) :
    ensSubset (sepEns A φ) A :=
  fun s h => ((sepEns_spec A φ s).mp h).1

/-- Image of empty ensemble is empty -/
theorem imageEns_empty (F : State → State) :
    imageEns F emptyEns = (emptyEns : @DynZF.Ens State _) := by
  apply ens_ext
  intro s
  constructor
  · intro h
    obtain ⟨x, hx, _⟩ := (imageEns_spec F emptyEns s).mp h
    exact absurd hx (emptyEns_spec x)
  · intro h
    exact absurd h (emptyEns_spec s)

/-- The empty ensemble is in every power ensemble -/
theorem emptyEns_mem_powerEns (A : @DynZF.Ens State _) :
    mem₂ emptyEns (powerEns A) :=
  (powerEns_spec A emptyEns).mpr (fun s h => absurd h (emptyEns_spec s))

/-- Every ensemble is in its own power ensemble -/
theorem self_mem_powerEns (A : @DynZF.Ens State _) :
    mem₂ A (powerEns A) :=
  (powerEns_spec A A).mpr (fun _ h => h)

/-- Union of a power ensemble recovers the original -/
theorem unionEns₂_powerEns (A : @DynZF.Ens State _) :
    ∀ s, mem s (unionEns₂ (powerEns A)) ↔ mem s A := by
  intro s
  constructor
  · intro h
    obtain ⟨B, hB, hs⟩ := (unionEns₂_spec (powerEns A) s).mp h
    exact (powerEns_spec A B).mp hB s hs
  · intro h
    apply (unionEns₂_spec (powerEns A) s).mpr
    exact ⟨A, self_mem_powerEns A, h⟩

end DerivedEns

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
