/-
  Spectral Arithmetic: Semiring Structure (Path B)
  =============================================

  Extends A1-A6 with B1-B5. Main results:
  - Eigenvalue theorem: obs(fₙ) = n · fₙ
  - A8 (infinite orbit) is a THEOREM, not an axiom
-/

import SpectralArithmetic.Core.Basic

namespace SpectralMonoid

/-! ## n-fold sum, parameterized (defined before class to use in axiom) -/

/-- n-fold additive self-sum, parameterized by the addition and zero. -/
def nfoldSum (add : α → α → α) (zero : α) : ℕ → α → α
  | 0, _ => zero
  | k + 1, x => add x (nfoldSum add zero k x)

/-! ## Path B: Semiring Axioms -/

/-- The semiring extension: adds ⊕ and structural axioms for obs. -/
class DynSemiring (State : Type*) extends SpectralMonoid State where
  oplus : State → State → State
  oplus_assoc : ∀ a b c, oplus a (oplus b c) = oplus (oplus a b) c
  oplus_comm : ∀ a b, oplus a b = oplus b a
  oplus_z : ∀ a, oplus z a = a
  compose_distrib : ∀ a b c, compose a (oplus b c) = oplus (compose a b) (compose a c)
  obs_f₀ : obs f₀ = z
  leibniz : ∀ a b, obs (compose a b) = oplus (compose (obs a) b) (compose a (obs b))
  obs_oplus : ∀ a b, obs (oplus a b) = oplus (obs a) (obs b)
  char_zero : ∀ n : ℕ, n ≥ 1 → nfoldSum oplus z n f₀ ≠ z

namespace DynSemiring

variable {State : Type*} [DynSemiring State]

/-- n · x using the instance's oplus and z -/
@[reducible] def smul (n : ℕ) (x : State) : State := nfoldSum oplus z n x

@[simp] theorem smul_zero (x : State) : smul 0 x = (z : State) := rfl
@[simp] theorem smul_succ (n : ℕ) (x : State) :
    smul (n + 1) x = oplus x (smul n x) := rfl

@[simp] theorem oplus_z_left (a : State) : oplus z a = a := oplus_z a
@[simp] theorem oplus_z_right (a : State) : oplus a z = a := by
  rw [oplus_comm, oplus_z]

@[simp] theorem smul_one (x : State) : smul 1 x = x := oplus_z_right x

/-- B5 restated with smul -/
theorem char_zero' (n : ℕ) (hn : n ≥ 1) : smul n (f₀ : State) ≠ z :=
  char_zero n hn

/-! ## smul interaction lemmas -/

theorem compose_distrib_right (a b c : State) :
    compose (oplus a b) c = oplus (compose a c) (compose b c) := by
  rw [compose_comm, compose_distrib, compose_comm c a, compose_comm c b]

theorem compose_smul (a : State) (n : ℕ) (x : State) :
    compose a (smul n x) = smul n (compose a x) := by
  induction n with
  | zero => simp [smul, nfoldSum, compose_z_right]
  | succ n ih => simp only [smul, nfoldSum]; rw [compose_distrib, ih]

theorem smul_add (m n : ℕ) (x : State) :
    smul (m + n) x = oplus (smul m x) (smul n x) := by
  induction m with
  | zero => simp [smul, nfoldSum]
  | succ m ih =>
    simp only [Nat.succ_add, smul, nfoldSum]
    change oplus x (smul (m + n) x) = oplus (oplus x (smul m x)) (smul n x)
    rw [ih, oplus_assoc]

/-! ## obs(z) = z -/

@[simp] theorem obs_z : obs (z : State) = z := by
  have h := leibniz (z : State) z
  rw [compose_z, compose_z, compose_z_right, oplus_z] at h
  exact h

/-! ## The Eigenvalue Theorem -/

/-- **Eigenvalue Theorem**: obs(iterS n) = n · iterS n -/
theorem eigenvalue (n : ℕ) :
    obs (iterS n) = smul n (iterS (State := State) n) := by
  induction n with
  | zero => simp [iterS, obs_f₀, smul, nfoldSum]
  | succ n ih =>
    simp only [iterS, succ]
    rw [leibniz, obs_f₁, ih, compose_smul]
    -- Goal: oplus (compose f₁ (iterS n)) (smul n (compose f₁ (iterS n)))
    --     = smul (n + 1) (compose f₁ (iterS n))
    -- This is definitionally smul_succ
    rfl

/-! ## A8 as a Theorem -/

/-- **A8 is a theorem**: The orbit does not cycle. -/
theorem infinite_orbit (n : ℕ) (hn : n ≥ 1) :
    iterS (State := State) n ≠ f₀ := by
  intro h
  have eigen := eigenvalue (State := State) n
  rw [h, obs_f₀] at eigen
  exact char_zero' n hn eigen.symm

/-- Path B gives us InfiniteOrbit for free -/
instance infiniteOrbit : InfiniteOrbit State where
  no_cycle := infinite_orbit

end DynSemiring

end SpectralMonoid
