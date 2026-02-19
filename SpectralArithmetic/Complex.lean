/-
  Spectral Arithmetic: ℂ Extension (Path G)
  ======================================

  Extends E1 with G1 (algebraic closure via imaginary unit).

  Unlike E1 (topological — completeness), G1 is algebraic: it adjoins
  a state j with j² = ⊖f₀, making the scalar field ℂ = ℝ[j]/(j²+1).

  The formalization axiomatizes:
  - j : State with j² = ⊖f₀ (the imaginary unit / quarter-turn operator)
  - csmul : ℂ → State → State (complex scalar multiplication)
  - complexEigen : ℂ → State (complex eigenstates)
  - The eigenvalue theorem for ℂ: obs(f_w) = w · f_w

  Key derived results:
  - j⁴ = f₀ (quarter-turn periodicity)
  - j³ = ⊖j (three-quarter turn)
  - Complex scalars form ℂ = ℝ[j]/(j²+1)
-/

import SpectralArithmetic.Complete
import Mathlib.Data.Complex.Basic

namespace SpectralMonoid

/-! ## Path G: Complex Extension -/

/-- The complex extension: adds imaginary unit j and G1 (algebraic closure).

G1 is a single algebraic axiom: there exists a state j whose compose-square
is ⊖f₀ (the additive inverse of the multiplicative identity). This makes
j the quarter-turn operator: j⁰ = f₀, j¹ = j, j² = ⊖f₀, j³ = ⊖j, j⁴ = f₀.

The axioms package the consequences of complexification:
- j with j² = ⊖f₀ and j commuting with everything
- csmul extends rsmul to complex scalars
- complexEigen extends realEigen to complex eigenvalues
- The eigenvalue theorem extends to ℂ -/
class DynComplex (State : Type*) extends DynComplete State where
  /-- G1: Imaginary unit — the quarter-turn operator -/
  j : State
  /-- j² = ⊖f₀ (squaring gives reversal) -/
  j_sq : compose j j = oneg f₀
  /-- j commutes with all states under compose -/
  j_comm : ∀ s : State, compose j s = compose s j
  /-- j is not the annihilator -/
  j_ne_z : j ≠ z
  /-- j is not the identity -/
  j_ne_f₀ : j ≠ f₀

  /-- Complex scalar multiplication: w · x for w ∈ ℂ -/
  csmul : ℂ → State → State
  /-- csmul extends rsmul on reals -/
  csmul_real : ∀ (α : ℝ) (x : State),
    csmul (α : ℂ) x = rsmul α x
  /-- csmul of I acts as compose with j -/
  csmul_I : ∀ (x : State),
    csmul Complex.I x = compose j x
  /-- csmul is linear in the scalar -/
  csmul_add : ∀ (w v : ℂ) (x : State),
    csmul (w + v) x = oplus (csmul w x) (csmul v x)
  /-- csmul distributes over oplus -/
  csmul_oplus : ∀ (w : ℂ) (a b : State),
    csmul w (oplus a b) = oplus (csmul w a) (csmul w b)
  /-- csmul interacts with compose -/
  csmul_compose : ∀ (w : ℂ) (a b : State),
    compose a (csmul w b) = csmul w (compose a b)
  /-- csmul zero -/
  csmul_zero_left : ∀ (x : State), csmul 0 x = z
  /-- csmul one -/
  csmul_one : ∀ (x : State), csmul 1 x = x

  /-- Complex eigenstates: w ↦ f_w -/
  complexEigen : ℂ → State
  /-- complexEigen extends realEigen on reals -/
  complexEigen_real : ∀ (α : ℝ),
    complexEigen (α : ℂ) = realEigen α
  /-- Functional equation: compose(f_w, f_v) = f_{w+v} -/
  complexEigen_add : ∀ (w v : ℂ),
    compose (complexEigen w) (complexEigen v) = complexEigen (w + v)
  /-- complexEigen is injective -/
  complexEigen_injective : Function.Injective complexEigen

  /-- **Eigenvalue theorem for ℂ**: obs(f_w) = w · f_w -/
  eigenvalue_complex : ∀ w : ℂ,
    obs (complexEigen w) = csmul w (complexEigen w)

namespace DynComplex

variable {State : Type*} [DynComplex State]

open DynSemiring DynIntDomain DynRational DynComplete

/-! ## Quarter-turn periodicity -/

/-- j³ = ⊖j (three-quarter turn) -/
theorem j_cubed :
    compose (compose j j) (j : State) = oneg j := by
  rw [j_sq, compose_oneg_left, compose_f₀]

/-- j⁴ = f₀ (full turn returns to identity) -/
theorem j_fourth :
    compose (compose j j) (compose j (j : State)) = f₀ := by
  rw [j_sq, compose_oneg_oneg, compose_f₀_right]

/-- j ≠ f₁ (j is not the generator).
    Proof: if j = f₁, then j⁴ = iterS 4 = f₀, contradicting InfiniteOrbit. -/
theorem j_ne_f₁ : (j : State) ≠ f₁ := by
  intro h
  -- j⁴ = f₀ (quarter-turn periodicity)
  have h1 := j_fourth (State := State)
  -- Substitute j = f₁
  rw [h] at h1
  -- compose f₁ f₁ = iterS 2
  have h2 : compose (f₁ : State) f₁ = iterS 2 := by
    have : iterS (State := State) 1 = f₁ := iterS_one
    calc compose f₁ f₁ = succ f₁ := rfl
      _ = succ (iterS 1) := by rw [this]
      _ = iterS 2 := rfl
  rw [h2, compose_iterS] at h1
  -- h1 : iterS 4 = f₀
  exact InfiniteOrbit.no_cycle 4 (by omega) h1

/-- oneg f₀ ≠ f₀ (reversal is not identity) -/
theorem oneg_f₀_ne_f₀ : oneg (f₀ : State) ≠ f₀ := by
  intro h
  -- If ⊖f₀ = f₀, then f₀ ⊕ f₀ = z (from ⊖ spec: f₀ ⊕ ⊖f₀ = z)
  -- But f₀ ⊕ f₀ = smul 2 f₀ (by definition of smul)
  -- smul 2 f₀ = z → f₀ = z (by torsion_free) → contradiction with f₀_ne_z
  have h1 : oplus f₀ (f₀ : State) = z := by
    have := oneg_spec (State := State) f₀
    rw [h] at this; exact this
  have h2 : smul 2 (f₀ : State) = z := by
    change oplus f₀ (oplus f₀ z) = z
    rw [oplus_comm (f₀ : State) z, oplus_z]; exact h1
  exact f₀_ne_z (torsion_free (State := State) (by omega : (2 : ℕ) ≥ 1) h2)

/-- j ≠ ⊖f₀ (quarter turn ≠ half turn) -/
theorem j_ne_oneg_f₀ : (j : State) ≠ oneg f₀ := by
  intro h
  -- If j = ⊖f₀, then j² = compose(⊖f₀, ⊖f₀) = compose(f₀, f₀) = f₀
  -- But j² = ⊖f₀ by G1. So ⊖f₀ = f₀, contradicting oneg_f₀_ne_f₀.
  -- j² = ⊖f₀ by G1
  -- j = ⊖f₀ by hypothesis, so j² = compose(⊖f₀, ⊖f₀) = f₀
  -- But j² = ⊖f₀, so ⊖f₀ = f₀, contradicting oneg_f₀_ne_f₀
  have h1 := j_sq (State := State)
  -- h1 : compose j j = oneg f₀
  rw [h] at h1
  -- h1 : compose (oneg f₀) (oneg f₀) = oneg f₀
  rw [compose_oneg_oneg, compose_f₀_right] at h1
  -- h1 : f₀ = oneg f₀
  exact oneg_f₀_ne_f₀ (State := State) h1.symm

/-! ## Basic properties of complexEigen -/

/-- complexEigen(0) = f₀ -/
@[simp] theorem complexEigen_zero :
    complexEigen (State := State) 0 = f₀ := by
  have : (0 : ℂ) = ((0 : ℝ) : ℂ) := by norm_num
  rw [this, complexEigen_real, realEigen_zero]

/-- complexEigen(1) = f₁ -/
@[simp] theorem complexEigen_one :
    complexEigen (State := State) 1 = f₁ := by
  have : (1 : ℂ) = ((1 : ℝ) : ℂ) := by norm_num
  rw [this, complexEigen_real, realEigen_one]

/-- complexEigen w ≠ z for any w -/
theorem complexEigen_ne_z (w : ℂ) :
    complexEigen (State := State) w ≠ z := by
  intro h
  have h1 : complexEigen (State := State) (w + (-w)) = z := by
    rw [← complexEigen_add, h, compose_z]
  rw [add_neg_cancel] at h1
  rw [complexEigen_zero] at h1
  exact f₀_ne_z h1

/-- obs(f₀) = z via the complex eigenvalue theorem -/
theorem eigenvalue_complex_zero :
    obs (complexEigen (State := State) 0) = z := by
  rw [eigenvalue_complex, csmul_zero_left]

/-- obs(f₁) = f₁ via the complex eigenvalue theorem -/
theorem eigenvalue_complex_one :
    obs (complexEigen (State := State) 1) = f₁ := by
  rw [eigenvalue_complex, csmul_one, complexEigen_one]

/-! ## Complex conjugate eigenstates -/

/-- compose is the group operation on complex eigenvalues -/
theorem complexEigen_sub (w v : ℂ) :
    compose (complexEigen w) (complexEigen (State := State) (-v)) =
    complexEigen (w + (-v)) := complexEigen_add w (-v)

end DynComplex

end SpectralMonoid
