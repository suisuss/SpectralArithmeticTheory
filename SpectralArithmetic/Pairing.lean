/-
  Spectral Arithmetic: Pairing Lower Bounds
  ==========================================

  Proves fundamental limitations of pairing functions:
  - Theorem 3: Addition is not injective on pairs
  - Theorem 4: Injective pairings are super-linear (sorry)
  - Theorem 6: Injective encoding implies unique preimages
  - Theorem 7: Non-redundant base-2 addition has carry propagation
-/

import Mathlib.Tactic

/-! ## Theorem 3: Addition is not injective on pairs -/

/-- Addition is not an injective pairing function:
    3 + 5 = 4 + 4, but (3,5) ≠ (4,4). -/
theorem add_not_injective_on_pairs :
    ¬ (∀ a b c d : ℕ, a + b = c + d → a = c ∧ b = d) := by
  intro h
  have := h 3 5 4 4 (by omega)
  omega

/-! ## Theorem 4: Injective pairings are super-linear (sorry budget) -/

/-- If π : ℕ × ℕ → ℕ is injective, then for any c, there exists n
    with π(n, n) > c * n. (Super-linearity on the diagonal.) -/
theorem injective_pairing_superlinear (π : ℕ × ℕ → ℕ) (hπ : Function.Injective π)
    (c : ℕ) : ∃ n : ℕ, π (n, n) > c * n := by
  -- Pigeonhole: (n+1)² pairs in [0,n]² can't all map to [0, c·n]
  sorry

/-! ## Theorem 6: Injective encoding implies unique preimages -/

/-- An injective function has unique preimages (trivial from definition). -/
theorem injective_unique_preimage {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (a b : α) (h : f a = f b) : a = b :=
  hf h

/-! ## Theorem 7: Non-redundant addition has carry -/

/-- In base 2, the sum (2^k - 1) + 1 = 2^k.
    For k ≥ 1, neither input has a nonzero bit at position k,
    but the output does. This witnesses carry propagation from bit 0 to bit k. -/
theorem carry_propagation_witness (k : ℕ) (hk : k ≥ 1) :
    -- The sum equals 2^k
    2 ^ k - 1 + 1 = 2 ^ k
    -- Input 1 has no bit at position k
    ∧ (2 ^ k - 1) / 2 ^ k = 0
    -- Input 2 has no bit at position k
    ∧ 1 / 2 ^ k = 0
    -- Output has a bit at position k
    ∧ 2 ^ k / 2 ^ k = 1 := by
  have hpow : 2 ^ k ≥ 1 := Nat.one_le_two_pow
  refine ⟨by omega, ?_, ?_, ?_⟩
  · exact Nat.div_eq_of_lt (by omega)
  · have : 1 < 2 ^ k := Nat.one_lt_two_pow_iff.mpr (by omega)
    exact Nat.div_eq_of_lt (by omega)
  · exact Nat.div_self (by omega)
