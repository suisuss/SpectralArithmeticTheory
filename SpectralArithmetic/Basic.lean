/-
  Spectral Arithmetic: Numbers as Eigenfunctions of Differentiation
  ==============================================================

  Lean 4 formalization of the process-based axioms A1-A8.

  Primitives:
  - State : Type (an uninterpreted type)
  - compose : State → State → State (how processes combine)
  - obs : State → State (what you read off — the abstract d/dx)

  The natural numbers emerge as the orbit of f₀ under successor S(s) = compose(f₁, s).
-/

import Mathlib.Tactic

/-! ## The Axiom System -/

/-- The Spectral Arithmetic axiom system: a commutative monoid (State, compose, f₀)
    with an observation operator obs, a generator f₁, and an annihilator z. -/
class SpectralMonoid (State : Type*) where
  /-- Binary composition of states -/
  compose : State → State → State
  /-- Observation operator (abstract d/dx) -/
  obs : State → State
  /-- Identity state (eigenvalue 0, the "static one") -/
  f₀ : State
  /-- Unit process (eigenvalue 1, the "dynamic one") -/
  f₁ : State
  /-- Annihilator (zero state) -/
  z : State

  /-- A1: Self-reproducing process — obs(f₁) = f₁ -/
  obs_f₁ : obs f₁ = f₁
  /-- A2: Identity — compose(f₀, s) = s -/
  compose_f₀ : ∀ s, compose f₀ s = s
  /-- A5a: Associativity -/
  compose_assoc : ∀ a b c, compose a (compose b c) = compose (compose a b) c
  /-- A5b: Commutativity -/
  compose_comm : ∀ a b, compose a b = compose b a
  /-- A6: Annihilator — compose(z, s) = z -/
  compose_z : ∀ s, compose z s = z
  /-- A7: Cancellation — compose(f₁, a) = compose(f₁, b) → a = b -/
  f₁_cancel : ∀ a b, compose f₁ a = compose f₁ b → a = b
  /-- Non-degeneracy: f₀ ≠ f₁ -/
  f₀_ne_f₁ : f₀ ≠ f₁
  /-- Non-degeneracy: f₀ ≠ z -/
  f₀_ne_z : f₀ ≠ z
  /-- Non-degeneracy: f₁ ≠ z -/
  f₁_ne_z : f₁ ≠ z

namespace SpectralMonoid

variable {State : Type*} [inst : SpectralMonoid State]

/-! ## Definitions -/

/-- A3: Successor — S(s) = compose(f₁, s) -/
def succ (s : State) : State := compose f₁ s

/-- Iterated successor: Sⁿ(f₀) -/
def iterS : ℕ → State
  | 0 => f₀
  | n + 1 => succ (iterS n)

/-- The natural numbers as the orbit of f₀ under S -/
def isNat (s : State) : Prop := ∃ n : ℕ, s = iterS n

/-! ## A8: Infinite orbit (stated using iterS) -/

/-- A8: The orbit of f₀ under S does not cycle back -/
class InfiniteOrbit (State : Type*) [SpectralMonoid State] where
  no_cycle : ∀ n : ℕ, n ≥ 1 → iterS (State := State) n ≠ f₀

/-! ## Basic Lemmas -/

/-- Right identity from commutativity + left identity -/
@[simp]
theorem compose_f₀_right (s : State) : compose s f₀ = s := by
  rw [compose_comm, compose_f₀]

/-- Right annihilation from commutativity + left annihilation -/
@[simp]
theorem compose_z_right (s : State) : compose s z = z := by
  rw [compose_comm, compose_z]

/-- succ(f₀) = f₁ — the first successor is the generator -/
theorem succ_f₀ : succ (f₀ : State) = f₁ := by
  simp [succ, compose_f₀_right]

/-- iterS 1 = f₁ -/
theorem iterS_one : iterS (State := State) 1 = f₁ := by
  simp [iterS, succ, compose_f₀_right]

/-- succ is injective (restating A7 in terms of succ) -/
theorem succ_injective : Function.Injective (succ : State → State) :=
  fun _ _ h => f₁_cancel _ _ h

/-- f₀ is not in the image of succ (requires InfiniteOrbit) -/
theorem f₀_not_successor [InfiniteOrbit State] (s : State) (hs : isNat s) :
    succ s ≠ f₀ := by
  obtain ⟨n, rfl⟩ := hs
  intro h
  have : iterS (State := State) (n + 1) = f₀ := h
  exact InfiniteOrbit.no_cycle (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) this

/-! ## Peano Axioms as Theorems -/

/-- P1: f₀ ∈ ℕ -/
theorem P1_zero_is_nat : isNat (f₀ : State) := ⟨0, rfl⟩

/-- P2: ℕ is closed under succ -/
theorem P2_succ_closed (s : State) (h : isNat s) : isNat (succ s) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, rfl⟩

/-- P3: f₀ is not a successor of any natural (requires InfiniteOrbit) -/
theorem P3_zero_not_succ [InfiniteOrbit State] (s : State) (hs : isNat s) :
    succ s ≠ (f₀ : State) :=
  f₀_not_successor s hs

/-- P4: succ is injective -/
theorem P4_succ_injective (a b : State) (h : succ a = succ b) : a = b :=
  succ_injective h

/-- P5: Induction — if a property holds for f₀ and is preserved by succ,
    then it holds for all naturals. -/
theorem P5_induction (P : State → Prop)
    (base : P f₀)
    (step : ∀ s, isNat s → P s → P (succ s))
    (s : State) (hs : isNat s) : P s := by
  obtain ⟨n, rfl⟩ := hs
  induction n with
  | zero => exact base
  | succ n ih => exact step _ ⟨n, rfl⟩ ih

/-! ## Arithmetic on the orbit -/

/-- compose on iterS gives iterS of the sum -/
theorem compose_iterS (m n : ℕ) :
    compose (iterS m) (iterS n) = iterS (State := State) (m + n) := by
  induction m with
  | zero => simp [iterS, compose_f₀]
  | succ m ih =>
    change compose (compose f₁ (iterS m)) (iterS n) = iterS (m + 1 + n)
    rw [← compose_assoc, ih]
    have : m + 1 + n = (m + n) + 1 := by omega
    rw [this]; rfl

/-- Successor distributes: succ(iterS n) = iterS (n+1) -/
theorem succ_iterS (n : ℕ) : succ (iterS n) = iterS (State := State) (n + 1) := rfl

/-- iterS is injective (requires InfiniteOrbit) -/
theorem iterS_injective [InfiniteOrbit State] : Function.Injective (iterS (State := State)) := by
  intro m n h
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n =>
      exfalso
      have : iterS (State := State) (n + 1) = f₀ := h.symm
      exact InfiniteOrbit.no_cycle (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) this
  | succ m ih =>
    cases n with
    | zero =>
      exfalso
      have : iterS (State := State) (m + 1) = f₀ := h
      exact InfiniteOrbit.no_cycle (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) this
    | succ n =>
      congr 1
      exact ih (f₁_cancel _ _ h)

end SpectralMonoid
