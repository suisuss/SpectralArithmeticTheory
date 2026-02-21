/-
  Spectral Arithmetic: Pairing Lower Bounds and Carry Propagation
  ===============================================================

  The encoding obstruction shows that intensionalization (naming/encoding)
  and extensionalization (unfolding/execution) don't commute. These theorems
  establish the mechanism for WHY, in executable encodings:

  - Theorem 3: Addition is not injective on pairs — so encoding structured
    terms (which have parts) cannot use addition as its pairing function.
    The encoding must be super-additive.
  - Theorem 4: Injective pairings are unbounded — the encoding of
    extensionalized forms (which contain oplus, i.e., addition) grows
    without bound relative to the intensional forms.
  - Theorem 6: Injective encoding implies unique preimages — uniqueness
    of naming is required for self-encoding (Gödel decoding).
  - Theorem 7: Non-redundant base-2 addition has carry propagation —
    the concrete mechanism by which addition introduces non-locality,
    forcing external state (registers) in executable encodings.
-/

import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

/-! ## Theorem 3: Addition is not injective on pairs -/

/-- Addition is not an injective pairing function:
    3 + 5 = 4 + 4, but (3,5) ≠ (4,4). -/
theorem add_not_injective_on_pairs :
    ¬ (∀ a b c d : ℕ, a + b = c + d → a = c ∧ b = d) := by
  intro h
  have := h 3 5 4 4 (by omega)
  omega

/-! ## Theorem 4: Injective pairings are unbounded -/

/-- The diagonal map n ↦ (n, n) is injective. -/
theorem diag_injective : Function.Injective (fun n : ℕ => (n, n)) :=
  fun _ _ h => (Prod.mk.inj h).1

/-- **Theorem 4:** An injective pairing is unbounded on the diagonal.
    For any B, there exists n with π(n, n) > B.

    Note: the stronger claim "π(n,n) ≥ n for all n" is FALSE for
    non-monotone injective functions (e.g. transpositions). -/
theorem injective_pairing_unbounded (π : ℕ × ℕ → ℕ) (hπ : Function.Injective π)
    (B : ℕ) : ∃ n : ℕ, π (n, n) > B := by
  -- The B+2 pairs (0,0),(1,1),...,(B+1,B+1) have B+2 distinct images.
  -- If all images were ≤ B, that's B+2 distinct values in {0,...,B} (only B+1 slots).
  -- Contradiction by pigeonhole.
  by_contra h
  push_neg at h
  -- h : ∀ n, π(n, n) ≤ B
  -- Define g : Fin (B+2) → Fin (B+1) by g(k) = π(k, k)
  have hg : ∀ k : Fin (B + 2), π (↑k, ↑k) < B + 1 := fun k => by
    have := h k.val; omega
  let g : Fin (B + 2) → Fin (B + 1) := fun k => ⟨π (↑k, ↑k), hg k⟩
  have hg_inj : Function.Injective g := by
    intro a b hab
    simp only [g, Fin.mk.injEq] at hab
    have hab' : (a.val, a.val) = (b.val, b.val) := hπ hab
    exact Fin.ext (Prod.mk.inj hab').1
  exact absurd (Fintype.card_le_of_injective g hg_inj) (by simp)

/-! ## Theorem 6: Injective encoding implies unique preimages -/

/-- An injective function has unique preimages (trivial from definition). -/
theorem injective_unique_preimage {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (a b : α) (h : f a = f b) : a = b :=
  hf h

/-! ## Theorem 7: Non-redundant addition has carry

    Carry propagation is the MECHANISM by which the intension/extension
    gap forces external state in executable encodings. The Leibniz rule
    extensionalizes into a sum (oplus), and computing that sum on a
    positional representation requires carry — non-local state that
    the encoding cannot absorb.

    We prove carry exists in base 2, then generalize to any base b ≥ 2. -/

/-- In base 2, the sum (2^k - 1) + 1 = 2^k.
    For k ≥ 1, neither input has a nonzero bit at position k,
    but the output does. This witnesses carry propagation from bit 0 to bit k. -/
theorem carry_propagation_witness (k : ℕ) (hk : k ≥ 1) :
    2 ^ k - 1 + 1 = 2 ^ k
    ∧ (2 ^ k - 1) / 2 ^ k = 0
    ∧ 1 / 2 ^ k = 0
    ∧ 2 ^ k / 2 ^ k = 1 := by
  have hpow : 2 ^ k ≥ 1 := Nat.one_le_two_pow
  refine ⟨by omega, ?_, ?_, ?_⟩
  · exact Nat.div_eq_of_lt (by omega)
  · have : 1 < 2 ^ k := Nat.one_lt_two_pow_iff.mpr (by omega)
    exact Nat.div_eq_of_lt (by omega)
  · exact Nat.div_self (by omega)

/-- **General carry propagation (any base b ≥ 2):**
    In base b, adding (b^k - 1) + 1 = b^k.
    Neither input has a nonzero digit at position k (both are < b^k),
    but the output is exactly b^k (digit 1 at position k).
    Carry propagates from position 0 to position k.

    This shows carry is not an artifact of binary — it occurs in
    ANY non-redundant positional representation with base ≥ 2. -/
theorem carry_propagation_general (b k : ℕ) (hb : b ≥ 2) (hk : k ≥ 1) :
    b ^ k - 1 + 1 = b ^ k
    ∧ (b ^ k - 1) / b ^ k = 0
    ∧ 1 / b ^ k = 0
    ∧ b ^ k / b ^ k = 1 := by
  have hpow : b ^ k ≥ 1 := Nat.one_le_pow k b (by omega)
  have hpow_gt : b ^ k > 1 := by
    calc b ^ k ≥ 2 ^ k := Nat.pow_le_pow_left (by omega) k
    _ ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hk
    _ = 2 := by ring
    _ > 1 := by omega
  refine ⟨by omega, ?_, ?_, ?_⟩
  · exact Nat.div_eq_of_lt (by omega)
  · exact Nat.div_eq_of_lt (by omega)
  · exact Nat.div_self (by omega)
