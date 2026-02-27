/-
  Spectral Arithmetic: Integral Domain (Path C)
  ==========================================

  Extends A1-A6 + B1-B5 with C1-C3. Main results:
  - A7 (cancellation) is a THEOREM, not an axiom
  - Ring properties: ⊖(a · b) = a · (⊖b) = (⊖a) · b
  - obs(f₁⁻¹) = ⊖f₁⁻¹  (eigenvalue -1)
  - Eigenvalue theorem extends to negative integers
  - Power rule: obs(g^{n+1}) = (n+1) · g^n · obs(g)
-/

import SpectralArithmetic.Core.Semiring

namespace SpectralMonoid

/-! ## Path C: Integral Domain Axioms -/

/-- The integral domain extension: adds compose-inverse, ⊕-inverses, no zero divisors. -/
class DynIntDomain (State : Type*) extends DynSemiring State where
  /-- C1: Compose-inverse of f₁ -/
  f₁_inv : State
  f₁_inv_spec : compose f₁ f₁_inv = f₀
  /-- C2: ⊕-inverses exist -/
  oneg : State → State
  oneg_spec : ∀ s, oplus s (oneg s) = z
  /-- C3: No zero divisors -/
  no_zero_divisors : ∀ a b, compose a b = z → a = z ∨ b = z

namespace DynIntDomain

variable {State : Type*} [DynIntDomain State]

open DynSemiring

/-! ## Basic ⊕-inverse lemmas -/

@[simp] theorem oneg_cancel (s : State) : oplus s (oneg s) = z := oneg_spec s

theorem oneg_cancel_left (s : State) : oplus (oneg s) s = z := by
  rw [oplus_comm]; exact oneg_cancel s

/-- ⊕-inverse is unique -/
theorem oneg_unique (a b : State) (h : oplus a b = z) : b = oneg a := by
  have h2 := congr_arg (oplus (oneg a)) h
  -- h2 : oplus (oneg a) (oplus a b) = oplus (oneg a) z
  rw [oplus_assoc, oneg_cancel_left, oplus_z_left, oplus_z_right] at h2
  exact h2

@[simp] theorem oneg_z : oneg (z : State) = z := by
  symm; exact oneg_unique z z (oplus_z_left z)

@[simp] theorem oneg_oneg (s : State) : oneg (oneg s) = s := by
  symm; exact oneg_unique (oneg s) s (oneg_cancel_left s)

@[simp] theorem oneg_oplus (a b : State) :
    oneg (oplus a b) = oplus (oneg a) (oneg b) := by
  symm; apply oneg_unique
  -- goal: oplus (oplus a b) (oplus (oneg a) (oneg b)) = z
  calc oplus (oplus a b) (oplus (oneg a) (oneg b))
      _ = oplus a (oplus b (oplus (oneg a) (oneg b))) := by rw [← oplus_assoc]
      _ = oplus a (oplus (oplus b (oneg a)) (oneg b)) := by rw [oplus_assoc b]
      _ = oplus a (oplus (oplus (oneg a) b) (oneg b)) := by rw [oplus_comm b (oneg a)]
      _ = oplus a (oplus (oneg a) (oplus b (oneg b))) := by rw [← oplus_assoc (oneg a)]
      _ = oplus a (oplus (oneg a) z) := by rw [oneg_cancel]
      _ = oplus a (oneg a) := by rw [oplus_z_right]
      _ = z := oneg_cancel a

/-! ## ⊕-cancellation -/

theorem oplus_cancel_left (a b c : State) (h : oplus a b = oplus a c) : b = c := by
  have h2 := congr_arg (oplus (oneg a)) h
  rw [oplus_assoc, oneg_cancel_left, oplus_z_left,
      oplus_assoc, oneg_cancel_left, oplus_z_left] at h2
  exact h2

theorem oplus_cancel_right (a b c : State) (h : oplus b a = oplus c a) : b = c :=
  oplus_cancel_left a b c (by rwa [oplus_comm a, oplus_comm a])

/-! ## Ring properties: compose interacts with oneg -/

/-- ⊖(a · b) = a · (⊖b) -/
theorem compose_oneg_right (a b : State) :
    compose a (oneg b) = oneg (compose a b) := by
  apply oneg_unique
  rw [← compose_distrib, oneg_cancel, compose_z_right]

/-- ⊖(a · b) = (⊖a) · b -/
theorem compose_oneg_left (a b : State) :
    compose (oneg a) b = oneg (compose a b) := by
  rw [compose_comm, compose_oneg_right, compose_comm]

/-- (⊖a) · (⊖b) = a · b -/
theorem compose_oneg_oneg (a b : State) :
    compose (oneg a) (oneg b) = compose a b := by
  rw [compose_oneg_left, compose_oneg_right, oneg_oneg]

/-! ## f₁⁻¹ properties -/

theorem f₁_inv_compose : compose (f₁_inv : State) f₁ = f₀ := by
  rw [compose_comm]; exact f₁_inv_spec

@[simp] theorem compose_f₁_f₁_inv (s : State) :
    compose f₁ (compose f₁_inv s) = s := by
  rw [compose_assoc, f₁_inv_spec, compose_f₀]

@[simp] theorem compose_f₁_inv_f₁ (s : State) :
    compose f₁_inv (compose f₁ s) = s := by
  rw [compose_assoc, f₁_inv_compose, compose_f₀]

/-- f₁⁻¹ ≠ z -/
theorem f₁_inv_ne_z : (f₁_inv : State) ≠ z := by
  intro h
  have := f₁_inv_spec (State := State)
  rw [h, compose_z_right] at this
  exact f₀_ne_z this.symm

/-! ## A7 (Cancellation) as a Theorem -/

/-- **A7 is now a theorem**: compose(f₁, a) = compose(f₁, b) → a = b.
    Proof uses integral domain structure (C2 + C3). -/
theorem f₁_cancel' (a b : State) (h : compose f₁ a = compose f₁ b) : a = b := by
  have h1 : oplus (compose f₁ a) (oneg (compose f₁ b)) = z := by
    rw [h, oneg_cancel]
  rw [← compose_oneg_right, ← compose_distrib] at h1
  cases no_zero_divisors f₁ (oplus a (oneg b)) h1 with
  | inl h_f₁ => exact absurd h_f₁ f₁_ne_z
  | inr h_ab =>
    exact oplus_cancel_right (oneg b) a b
      (by rw [h_ab]; exact (oneg_cancel b).symm)

/-! ## f₁⁻¹ and inverse successor -/

/-- Inverse successor: S⁻¹(s) = compose(f₁⁻¹, s) -/
def pred (s : State) : State := compose f₁_inv s

/-- Negative iterates: f₋ₙ = (f₁⁻¹)ⁿ · f₀ -/
def iterS_neg : ℕ → State
  | 0 => f₀
  | n + 1 => pred (iterS_neg n)

/-- S(S⁻¹(s)) = s -/
theorem succ_pred (s : State) : succ (pred s) = s := by
  unfold succ pred; exact compose_f₁_f₁_inv s

/-- S⁻¹(S(s)) = s -/
theorem pred_succ (s : State) : pred (succ s) = s := by
  unfold pred succ; exact compose_f₁_inv_f₁ s

/-! ## obs(f₁⁻¹) = ⊖f₁⁻¹ -/

/-- **obs(f₁⁻¹) = ⊖f₁⁻¹** — the inverse generator has eigenvalue -1 -/
theorem obs_f₁_inv : obs (f₁_inv : State) = oneg f₁_inv := by
  -- From Leibniz on compose(f₁, f₁⁻¹) = f₀:
  have h := leibniz (f₁ : State) f₁_inv
  rw [f₁_inv_spec, obs_f₀, obs_f₁, f₁_inv_spec] at h
  -- h : z = oplus f₀ (compose f₁ (obs f₁_inv))
  -- So compose(f₁, obs(f₁⁻¹)) = ⊖f₀
  have h2 : compose f₁ (obs (f₁_inv : State)) = oneg (f₀ : State) := by
    apply oneg_unique (f₀ : State)
    exact h.symm
  -- Apply f₁⁻¹ to both sides: obs(f₁⁻¹) = compose(f₁⁻¹, ⊖f₀)
  have h3 := congr_arg (compose f₁_inv) h2
  rw [compose_f₁_inv_f₁, compose_oneg_right, compose_f₀_right] at h3
  exact h3

/-! ## Eigenvalue Theorem for Negative Integers -/

/-- obs applied to negative iterates via Leibniz -/
theorem obs_iterS_neg_succ (n : ℕ) :
    obs (iterS_neg (State := State) (n + 1)) =
    oplus (oneg (iterS_neg (n + 1))) (compose f₁_inv (obs (iterS_neg n))) := by
  -- iterS_neg (n+1) = pred (iterS_neg n) = compose f₁_inv (iterS_neg n)
  change obs (compose f₁_inv (iterS_neg n)) =
    oplus (oneg (compose f₁_inv (iterS_neg n))) (compose f₁_inv (obs (iterS_neg n)))
  rw [leibniz, obs_f₁_inv, compose_oneg_left]

/-- **Eigenvalue theorem for negative integers**: obs(f₋ₙ) = ⊖(n · f₋ₙ)
    i.e., obs(f₋ₙ) = (-n) · f₋ₙ -/
theorem eigenvalue_neg (n : ℕ) :
    obs (iterS_neg (State := State) n) = oneg (smul n (iterS_neg n)) := by
  induction n with
  | zero =>
    change obs (f₀ : State) = oneg (z : State)
    rw [obs_f₀, oneg_z]
  | succ n ih =>
    rw [obs_iterS_neg_succ, ih, compose_oneg_right, compose_smul]
    change oplus (oneg (iterS_neg (n + 1)))
      (oneg (smul n (iterS_neg (n + 1)))) = _
    rw [← oneg_oplus, ← smul_succ]

/-! ## The Power Rule -/

/-- Compose-power: gⁿ = compose(g, g, ..., g) [n times], g⁰ = f₀ -/
def cpow (g : State) : ℕ → State
  | 0 => f₀
  | n + 1 => compose g (cpow g n)

@[simp] theorem cpow_zero (g : State) : cpow g 0 = (f₀ : State) := rfl
@[simp] theorem cpow_one (g : State) : cpow g 1 = g := compose_f₀_right g
theorem cpow_succ (g : State) (n : ℕ) :
    cpow g (n + 1) = compose g (cpow g n) := rfl

theorem cpow_add (g : State) (m n : ℕ) :
    cpow g (m + n) = compose (cpow g m) (cpow g n) := by
  induction m with
  | zero => simp [cpow, compose_f₀]
  | succ m ih =>
    simp only [Nat.succ_add, cpow_succ]
    rw [ih, compose_assoc]

/-- iterS n = cpow f₁ n -/
theorem iterS_eq_cpow (n : ℕ) :
    iterS (State := State) n = cpow f₁ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterS, succ, cpow_succ, ih]

/-- **Power Rule**: obs(g^{n+1}) = (n+1) · g^n · obs(g) -/
theorem power_rule (g : State) (n : ℕ) :
    obs (cpow g (n + 1)) =
    smul (n + 1) (compose (cpow g n) (obs g)) := by
  induction n with
  | zero =>
    -- obs(g¹) = obs(g) = 1 · g⁰ · obs(g) = 1 · compose(f₀, obs g) = obs g
    change obs (compose g f₀) = oplus (compose f₀ (obs g)) z
    rw [compose_f₀_right, compose_f₀, oplus_z_right]
  | succ n ih =>
    -- obs(g^{n+2}) = obs(compose(g, g^{n+1}))
    rw [cpow_succ g (n + 1), leibniz, ih, compose_smul]
    rw [compose_comm (obs g) (cpow g (n + 1))]
    have step : compose g (compose (cpow g n) (obs g)) =
                compose (cpow g (n + 1)) (obs g) := by
      rw [cpow_succ, compose_assoc]
    rw [step]
    -- oplus x (smul (n+1) x) = smul (n+2) x  — definitional
    rfl

end DynIntDomain

end SpectralMonoid
