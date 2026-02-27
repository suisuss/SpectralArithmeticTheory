/-
  Spectral Arithmetic: Countermodels for F-Axiom Separation
  ==========================================================

  This file proves that the F-axioms (F1, F3) in the abstract `Ens`
  formulation carry genuine content — they are NOT automatically
  satisfied by every model of DynComplete.

  We construct two countermodels using the forward model
  (State = AddMonoidAlgebra ℝ ℝ):

  **Countermodel A — F1 is non-trivial:**
  If Ens is restricted to *finite* predicates (predicates true on
  finitely many states), then F1 (the orbit ensemble) cannot exist
  because the orbit is infinite (from iterS_injective + char zero).

  **Countermodel B — F3 is non-trivial:**
  If Ens is restricted to *sub-orbit* predicates (predicates implying
  isNat), then F1 and F2 hold, but F3 fails: the function
  `realEigen π ∘ ·` maps orbit elements to non-orbit elements
  (since realEigen is injective and π ≠ n for any n : ℕ).
-/

import SpectralArithmetic.Verification.Model
import Mathlib.Analysis.Real.Pi.Irrational

namespace SpectralMonoid.Countermodels

open SpectralMonoid SpectralMonoid.Model

/-! ## Countermodel A: Finite Ens falsifies F1

The orbit of f₀ under successor is infinite (iterS is injective,
proved from eigenvalue theorem + char zero). Any finite predicate
can only capture finitely many elements. Therefore no finite
predicate satisfies the orbit spec. -/

/-- A predicate is "finite" if it is true on at most finitely many elements. -/
def FinitePred {α : Type*} (P : α → Prop) : Prop :=
  Set.Finite {x | P x}

/-- iterS on the model S = AddMonoidAlgebra ℝ ℝ is injective.
    This follows from the InfiniteOrbit instance (derived from char zero). -/
theorem model_iterS_injective :
    Function.Injective (iterS (State := S)) :=
  iterS_injective

/-- The orbit predicate isNat is infinite on the model. -/
theorem model_isNat_infinite : ¬FinitePred (isNat (State := S)) := by
  intro hfin
  -- The set {s | isNat s} contains the range of iterS
  have hrange : Set.range (iterS (State := S)) ⊆ {s | isNat s} :=
    fun s ⟨n, hn⟩ => ⟨n, hn.symm⟩
  -- The range of an injective function from ℕ is infinite
  have hinf : Set.Infinite (Set.range (iterS (State := S))) :=
    Set.infinite_range_of_injective model_iterS_injective
  -- But a subset of a finite set is finite — contradiction
  exact hinf (hfin.subset hrange)

/-- **Countermodel A:** No finite predicate satisfies the orbit spec.
    This shows F1 is non-trivial: DynComplete alone, with Ens restricted
    to finite predicates, cannot satisfy the orbit ensemble axiom. -/
theorem f1_not_finite :
    ¬∃ (P : S → Prop), FinitePred P ∧ (∀ s, P s ↔ isNat s) := by
  intro ⟨P, hfin, hspec⟩
  apply model_isNat_infinite
  unfold FinitePred
  convert hfin using 1
  ext s
  exact (hspec s).symm

/-! ## Countermodel B: Sub-orbit Ens falsifies F3

Define Ens = {P : S → Prop | ∀ s, P s → isNat s} — predicates
whose support lies within the orbit. F1 holds (the orbit is trivially
a sub-orbit predicate). F2 (separation) holds (intersection with φ
preserves sub-orbit membership). F3 fails: there exist functions
that map orbit elements outside the orbit. -/

/-- A predicate is "sub-orbit" if it only holds for natural states. -/
def SubOrbitPred (P : S → Prop) : Prop :=
  ∀ s, P s → isNat s

/-- The orbit predicate is sub-orbit. -/
theorem isNat_sub_orbit : SubOrbitPred (isNat (State := S)) :=
  fun _ h => h

/-- Separation preserves sub-orbit: if P is sub-orbit, so is P ∧ φ. -/
theorem sep_sub_orbit (P : S → Prop) (φ : S → Prop)
    (hP : SubOrbitPred P) : SubOrbitPred (fun s => P s ∧ φ s) :=
  fun _ ⟨hp, _⟩ => hP _ hp

/-- realEigen maps ℕ to the orbit: realEigen n = iterS n. -/
theorem realEigen_nat (n : ℕ) :
    DynComplete.realEigen (State := S) (n : ℝ) = iterS n := by
  induction n with
  | zero =>
    simp [iterS, DynComplete.realEigen_zero]
  | succ n ih =>
    -- realEigen (n+1) = compose(realEigen n, realEigen 1) by realEigen_add
    -- After ih: compose(iterS n, f₁) = compose(f₁, iterS n) by comm = iterS(n+1)
    -- realEigen (↑(n+1)) = compose(realEigen ↑n, realEigen 1) by add + cast
    -- = compose(iterS n, f₁) by ih + realEigen_one
    -- = compose(f₁, iterS n) by comm = succ(iterS n) = iterS(n+1)
    -- Goal: realEigen (↑n + 1) = iterS (n+1) = succ (iterS n) = compose f₁ (iterS n)
    simp only [Nat.cast_succ, ← DynComplete.realEigen_add,
        DynComplete.realEigen_one, ih]
    -- Goal: compose (iterS n) f₁ = iterS (n + 1)
    rw [compose_comm]; rfl

/-- realEigen of an irrational is NOT in the orbit.
    Key idea: if realEigen α = iterS n, then realEigen α = realEigen n,
    so α = n by injectivity. But α is irrational, contradiction. -/
theorem realEigen_irrational_not_nat (α : ℝ) (hirr : Irrational α) :
    ¬isNat (DynComplete.realEigen (State := S) α) := by
  intro ⟨n, hn⟩
  -- realEigen α = iterS n = realEigen n
  have h1 : DynComplete.realEigen (State := S) α = DynComplete.realEigen (n : ℝ) := by
    rw [hn, realEigen_nat]
  -- By injectivity, α = n
  have h2 : α = (n : ℝ) := DynComplete.realEigen_injective h1
  -- But α is irrational and n is rational — contradiction
  exact hirr ⟨n, h2.symm⟩

/-- The constant function mapping everything to realEigen π. -/
noncomputable def constPi : S → S := fun _ => DynComplete.realEigen (State := S) Real.pi

/-- π is irrational. -/
theorem pi_irrational : Irrational Real.pi := irrational_pi

/-- **Countermodel B:** The image of a sub-orbit predicate under constPi
    is NOT sub-orbit (when the source is nonempty).

    Specifically: the image of isNat under constPi contains realEigen π,
    which is not in the orbit. This shows F3 is non-trivial: restricting
    Ens to sub-orbit predicates breaks replacement. -/
theorem f3_not_sub_orbit :
    ¬SubOrbitPred (fun y => ∃ x, isNat (State := S) x ∧ constPi x = y) := by
  intro hsub
  -- The image contains constPi(f₀) = realEigen π
  have hmem : ∃ x, isNat (State := S) x ∧ constPi x = DynComplete.realEigen Real.pi :=
    ⟨f₀, P1_zero_is_nat, rfl⟩
  -- So realEigen π is in the orbit (by sub-orbit hypothesis)
  have hnat := hsub _ hmem
  -- But realEigen π is NOT in the orbit (π is irrational)
  exact realEigen_irrational_not_nat Real.pi pi_irrational hnat

end SpectralMonoid.Countermodels
