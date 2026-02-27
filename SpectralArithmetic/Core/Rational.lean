/-
  Spectral Arithmetic: ℚ Extension (Path D)
  ======================================

  Extends C1-C3 with D1-D2. Main results:
  - Generalized cancellation: any non-zero element is cancellable
  - Torsion-freeness: n · x = z → x = z (for n ≥ 1)
  - Key factoring: n · x = compose(n · f₀, x)
  - smul distributes over oplus and oneg
  - obs(f_{1/q}) = qdiv q (f_{1/q})  (eigenvalue 1/q)
-/

import SpectralArithmetic.Core.IntegralDomain

namespace SpectralMonoid

/-! ## Generalized cancellation and torsion-freeness (from C1-C3) -/

namespace DynIntDomain

variable {State : Type*} [DynIntDomain State]

open DynSemiring

/-- **Generalized cancellation**: any non-zero element is cancellable. -/
theorem cancel_of_ne_z {c a b : State} (hc : c ≠ z)
    (h : compose c a = compose c b) : a = b := by
  have h1 : oplus (compose c a) (oneg (compose c b)) = z := by
    rw [h, oneg_cancel]
  rw [← compose_oneg_right, ← compose_distrib] at h1
  cases no_zero_divisors c (oplus a (oneg b)) h1 with
  | inl hc' => exact absurd hc' hc
  | inr hab =>
    exact oplus_cancel_right (oneg b) a b
      (by rw [hab]; exact (oneg_cancel b).symm)

/-- Key factoring: n · x = compose(n · f₀, x) -/
theorem smul_eq_compose_smul_f₀ (n : ℕ) (x : State) :
    smul n x = compose (smul n (f₀ : State)) x := by
  induction n with
  | zero =>
    change (z : State) = compose z x
    rw [compose_z]
  | succ n ih =>
    change oplus x (smul n x) =
      compose (oplus f₀ (smul n f₀)) x
    rw [ih, compose_distrib_right, compose_f₀]

/-- smul distributes over oplus: n · (a ⊕ b) = n · a ⊕ n · b -/
theorem smul_oplus (n : ℕ) (a b : State) :
    smul n (oplus a b) = oplus (smul n a) (smul n b) := by
  rw [smul_eq_compose_smul_f₀ n (oplus a b),
      compose_distrib,
      ← smul_eq_compose_smul_f₀ n a,
      ← smul_eq_compose_smul_f₀ n b]

/-- smul distributes over oneg: n · (⊖a) = ⊖(n · a) -/
theorem smul_oneg (n : ℕ) (a : State) :
    smul n (oneg a) = oneg (smul n a) := by
  rw [smul_eq_compose_smul_f₀ n (oneg a),
      compose_oneg_right,
      ← smul_eq_compose_smul_f₀ n a]

/-- **Torsion-freeness**: n · x = z → x = z (for n ≥ 1). -/
theorem torsion_free {n : ℕ} (hn : n ≥ 1) {x : State}
    (h : smul n x = z) : x = z := by
  rw [smul_eq_compose_smul_f₀] at h
  cases no_zero_divisors (smul n f₀) x h with
  | inl h_nf₀ => exact absurd h_nf₀ (char_zero' n hn)
  | inr hx => exact hx

/-- Uniqueness of ⊕-division: n · y₁ = a and n · y₂ = a → y₁ = y₂ -/
theorem smul_cancel {n : ℕ} (hn : n ≥ 1) {y₁ y₂ : State}
    (h : smul n y₁ = smul n y₂) : y₁ = y₂ := by
  have : smul n (oplus y₁ (oneg y₂)) = z := by
    rw [smul_oplus, smul_oneg, h, oneg_cancel]
  exact oplus_cancel_right (oneg y₂) y₁ y₂
    (by rw [torsion_free hn this]
        exact (oneg_cancel y₂).symm)

end DynIntDomain

/-! ## Path D: ℚ Extension Axioms -/

/-- The rational extension: adds q-th roots and unique divisibility. -/
class DynRational (State : Type*) extends DynIntDomain State where
  /-- D1: q-th root of f₁ exists -/
  root : ℕ → State
  root_spec : ∀ q : ℕ, q ≥ 1 →
    DynIntDomain.cpow (root q) q = f₁
  /-- D2: Unique divisibility — ∀ n ≥ 1, ∀ a, ∃ x, n · x = a -/
  qdiv : ℕ → State → State
  qdiv_spec : ∀ n : ℕ, n ≥ 1 → ∀ a : State,
    DynSemiring.smul n (qdiv n a) = a

namespace DynRational

variable {State : Type*} [DynRational State]

open DynSemiring DynIntDomain

/-! ## qdiv properties -/

/-- qdiv is right-inverse to smul -/
@[simp] theorem smul_qdiv (n : ℕ) (hn : n ≥ 1) (a : State) :
    smul n (qdiv n a) = a := qdiv_spec n hn a

/-- Uniqueness: if smul n y = a, then y = qdiv n a -/
theorem qdiv_unique {n : ℕ} (hn : n ≥ 1) {y a : State}
    (h : smul n y = a) : y = qdiv n a := by
  have h2 := qdiv_spec n hn a
  exact smul_cancel hn (by rw [h, h2])

/-- qdiv of z is z -/
@[simp] theorem qdiv_z (n : ℕ) (hn : n ≥ 1) :
    qdiv n (z : State) = z := by
  symm
  exact qdiv_unique hn
    (by rw [smul_eq_compose_smul_f₀]; exact compose_z_right _)

/-! ## Root properties -/

/-- root 1 = f₁ -/
theorem root_one : root (State := State) 1 = f₁ := by
  have h := root_spec (State := State) 1 (le_refl 1)
  rw [cpow_one] at h; exact h

/-- root q ≠ z for q ≥ 1 -/
theorem root_ne_z {q : ℕ} (hq : q ≥ 1) :
    root (State := State) q ≠ z := by
  intro h
  have := root_spec (State := State) q hq
  have cpow_z : cpow (z : State) q = z := by
    cases q with
    | zero => omega
    | succ n =>
      change compose z (cpow z n) = z
      exact compose_z _
  rw [h, cpow_z] at this
  exact f₁_ne_z this.symm

/-- cpow (root q) k ≠ z for any k, when q ≥ 1 -/
theorem cpow_root_ne_z {q : ℕ} (hq : q ≥ 1) (k : ℕ) :
    cpow (root (State := State) q) k ≠ z := by
  intro h
  cases k with
  | zero =>
    change (f₀ : State) = z at h
    exact f₀_ne_z h
  | succ k =>
    change compose (root q) (cpow (root q) k) = z at h
    cases no_zero_divisors (root q) (cpow (root q) k) h with
    | inl h => exact root_ne_z hq h
    | inr h => exact cpow_root_ne_z hq k h

/-! ## Scalar-compose commutation -/

/-- compose distributes through qdiv -/
theorem compose_qdiv (a : State) {n : ℕ} (hn : n ≥ 1)
    (b : State) :
    compose a (qdiv n b) = qdiv n (compose a b) := by
  apply qdiv_unique hn
  rw [← compose_smul, smul_qdiv n hn]

/-! ## The Eigenvalue 1/q Theorem -/

/-- **Eigenvalue 1/q**: obs(root q) = qdiv q (root q).
    The q-th root of f₁ has eigenvalue 1/q. -/
theorem obs_root {q : ℕ} (hq : q ≥ 1) :
    obs (root (State := State) q) =
    qdiv q (root (State := State) q) := by
  cases q with
  | zero => omega
  | succ n =>
    -- Power rule: obs(g^{n+1}) = (n+1) · g^n · obs(g)
    have hspec := root_spec (State := State) (n + 1) hq
    have hpr := power_rule (root (State := State) (n + 1)) n
    -- obs(root^{n+1}) = obs(f₁) = f₁
    rw [hspec, obs_f₁] at hpr
    -- Factor smul out of compose
    rw [← compose_smul] at hpr
    -- f₁ = compose(root^n, smul (n+1) (obs root))
    -- Also f₁ = compose(root^n, root)
    have f₁_eq : (f₁ : State) =
        compose (cpow (root (State := State) (n + 1)) n)
                (root (State := State) (n + 1)) := by
      rw [← hspec, cpow_succ, compose_comm]
    rw [f₁_eq] at hpr
    -- Cancel cpow root^n (≠ z)
    have hne := cpow_root_ne_z (State := State) hq n
    have key := cancel_of_ne_z hne hpr
    -- key : root (n+1) = smul (n+1) (obs (root (n+1)))
    exact qdiv_unique hq key.symm

end DynRational

end SpectralMonoid
