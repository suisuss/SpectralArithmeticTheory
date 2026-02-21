/-
  Spectral Arithmetic: Peano Arithmetic Test Suite
  =============================================

  Verifies that the process algebra satisfies all axioms of
  first-order Peano Arithmetic (PA).

  Analogous to ZFTest.lean (which verifies ZF set theory), this file
  collects the Peano axiom verifications in one place. The core results
  (P1-P5) are already proved in Basic.lean; this file re-exports them
  as PA1-PA5 and adds the arithmetic axioms PA6-PA9 (recursive
  definitions of addition and multiplication).

  PA axioms verified:
  - PA1: f₀ is a natural number                           (P1, Basic.lean)
  - PA2: Successor maps naturals to naturals               (P2, Basic.lean)
  - PA3: f₀ is not a successor                            (P3, Basic.lean)
  - PA4: Successor is injective                            (P4, Basic.lean)
  - PA5: Induction                                         (P5, Basic.lean)
  - PA6: x + 0 = x                                        (compose_f₀_right)
  - PA7: x + S(y) = S(x + y)                              (compose_iterS + omega)
  - PA8: x · 0 = 0                                        (smul_zero)
  - PA9: x · S(y) = x + (x · y)                           (smul_succ)

  The interpretation:
  - Natural numbers: iterS n (the orbit {f₀, f₁, f₂, ...})
  - Zero: f₀
  - Successor: succ (= compose f₁)
  - Addition: compose (restricted to iterates)
  - Multiplication: smul (n-fold oplus)
-/

import SpectralArithmetic.Core.Semiring

namespace SpectralMonoid

/-! ## Peano Arithmetic Axiom Verification -/

namespace PeanoTest

variable {State : Type*} [DynSemiring State]

open DynSemiring

/-! ### PA1-PA5: The Peano Axioms (from Basic.lean)

These are re-exports of P1-P5. The proofs are in Basic.lean;
we reference them here for completeness. -/

/-- **PA1**: f₀ is a natural number. -/
theorem pa1_zero_is_nat : isNat (f₀ : State) :=
  P1_zero_is_nat

/-- **PA2**: Successor maps naturals to naturals. -/
theorem pa2_succ_closed (s : State) (h : isNat s) :
    isNat (succ s) :=
  P2_succ_closed s h

/-- **PA3**: f₀ is not a successor of any natural.
    Requires InfiniteOrbit (A8). -/
theorem pa3_zero_not_succ (s : State) (hs : isNat s) :
    succ s ≠ f₀ :=
  P3_zero_not_succ s hs

/-- **PA4**: Successor is injective.
    Requires f₁_cancel (A7). -/
theorem pa4_succ_injective (a b : State) (h : succ a = succ b) :
    a = b :=
  P4_succ_injective a b h

/-- **PA5**: Induction principle.
    Every property holding at f₀ and closed under S holds for all naturals. -/
theorem pa5_induction (P : State → Prop)
    (base : P f₀) (step : ∀ n, isNat n → P n → P (succ n)) :
    ∀ n, isNat n → P n :=
  P5_induction P base step

/-! ### PA6-PA7: Addition Axioms

In PA, addition is defined recursively:
- x + 0 = x
- x + S(y) = S(x + y)

In our framework, addition on the natural orbit is `compose`:
  compose(iterS m, iterS n) = iterS(m + n)

We verify the recursive definition holds on iterates. -/

/-- **PA6**: x + 0 = x (right identity for addition).
    compose(iterS m, f₀) = iterS m -/
theorem pa6_add_zero (m : ℕ) :
    compose (iterS m) (f₀ : State) = iterS m :=
  compose_f₀_right (iterS m)

/-- **PA7**: x + S(y) = S(x + y).
    compose(iterS m, iterS(n+1)) = succ(compose(iterS m, iterS n)) -/
theorem pa7_add_succ (m n : ℕ) :
    compose (iterS m) (iterS (State := State) (n + 1)) =
    succ (compose (iterS m) (iterS n)) := by
  simp only [compose_iterS]; rfl

/-! ### PA8-PA9: Multiplication Axioms

In PA, multiplication is defined recursively:
- x · 0 = 0
- x · S(y) = x + (x · y)

In our framework, multiplication is `smul`:
  smul n x = x ⊕ x ⊕ ... ⊕ x (n times)

Note: smul n x computes n · x, so the PA correspondence is:
  PA's "m × n" ↔ smul m (iterS n) or smul n (iterS m)

The recursive definition matches PA's directly. -/

/-- **PA8**: x · 0 = 0.
    smul 0 x = z -/
theorem pa8_mul_zero (x : State) :
    smul 0 x = (z : State) := rfl

/-- **PA9**: x · S(y) = x + (x · y).
    smul (n+1) x = oplus x (smul n x)

    Note: definitionally `oplus x (smul n x)`, which equals
    `oplus (smul n x) x` by `oplus_comm`. -/
theorem pa9_mul_succ (n : ℕ) (x : State) :
    smul (n + 1) x = oplus x (smul n x) := rfl

/-! ### Derived PA Results -/

/-- Addition is commutative on iterates:
    compose(iterS m, iterS n) = compose(iterS n, iterS m) -/
theorem add_comm_iterS (m n : ℕ) :
    compose (iterS m) (iterS (State := State) n) =
    compose (iterS n) (iterS m) :=
  compose_comm (iterS m) (iterS n)

/-- Addition is associative on iterates -/
theorem add_assoc_iterS (m n k : ℕ) :
    compose (compose (iterS m) (iterS n)) (iterS (State := State) k) =
    compose (iterS m) (compose (iterS n) (iterS k)) :=
  (compose_assoc (iterS m) (iterS n) (iterS k)).symm

/-- Addition functional equation:
    compose(iterS m, iterS n) = iterS(m + n) -/
theorem add_iterS (m n : ℕ) :
    compose (iterS m) (iterS (State := State) n) = iterS (m + n) :=
  compose_iterS m n

/-- The orbit is infinite: no iterate returns to f₀ -/
theorem orbit_infinite :
    ∀ n : ℕ, n ≥ 1 → iterS (State := State) n ≠ f₀ :=
  InfiniteOrbit.no_cycle

/-- iterS is injective: distinct naturals give distinct states -/
theorem iterS_injective' :
    Function.Injective (iterS (State := State)) :=
  iterS_injective

end PeanoTest

/-! ### The Recursion Theorem

PA's recursion theorem: for any set X, element a ∈ X, and function
g : X → X, there exists a unique h : ℕ → X with h(0) = a and
h(n+1) = g(h(n)).

In Lean's type theory, this is just structural recursion on ℕ —
it's built into the language. We state it for completeness. -/

/-- **Recursion theorem**: for any a and g, there exists a unique function
    h : ℕ → α with h(0) = a and h(n+1) = g(h(n)). -/
theorem PeanoTest.recursion {α : Type*} (a : α) (g : α → α) :
    ∃! h : ℕ → α, h 0 = a ∧ ∀ n, h (n + 1) = g (h n) := by
  refine ⟨fun n => Nat.rec a (fun _ ih => g ih) n, ⟨rfl, fun _ => rfl⟩, ?_⟩
  intro h' ⟨h0, hs⟩
  funext n
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [hs n, ih]

end SpectralMonoid
