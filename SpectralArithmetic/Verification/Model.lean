/-
  Spectral Arithmetic: Forward Model (ZF → Framework)
  ====================================================

  Constructs an explicit model of all 20 axioms (A1–F3) inside ZF,
  completing the forward direction of the equiconsistency proof
  Con(ZF) ↔ Con(A1–F3).

  The model:
    State       = AddMonoidAlgebra ℝ ℝ  (finitely-supported functions ℝ → ℝ
                  with convolution multiplication)
    compose     = ring multiplication (· * ·)
    oplus       = ring addition (· + ·)
    obs         = eigenvalue-weighting: Σ aᵢ δ_{αᵢ} ↦ Σ αᵢ·aᵢ δ_{αᵢ}
    f₀          = 1  (= single 0 1)
    f₁          = single 1 1
    z           = 0

  The backward direction (Framework → ZF) is formalized in ZFTest.lean.
  Together they give: Con(ZF) ↔ Con(A1–F3).
-/

import SpectralArithmetic.Verification.ZFTest
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

namespace SpectralMonoid.Model

open Finsupp SpectralMonoid

abbrev S := AddMonoidAlgebra ℝ ℝ

-- Bridge: Finsupp.induction_linear introduces variables with type ℝ →₀ ℝ
-- rather than S = AddMonoidAlgebra ℝ ℝ.  The Mul/Ring instances live on
-- AddMonoidAlgebra, so we expose them at the ℝ →₀ ℝ level to make
-- ring lemmas (add_mul, mul_add, ring, …) available during induction.
private noncomputable instance : CommRing (ℝ →₀ ℝ) := inferInstanceAs (CommRing S)
private noncomputable instance : Module ℝ (ℝ →₀ ℝ) := inferInstanceAs (Module ℝ S)

/-! ## Primitive Definitions -/

noncomputable def modelObs (c : S) : S :=
  c.sum fun α a => (Finsupp.single α (α * a) : S)

/-! ## Helper Lemmas -/

@[simp] theorem modelObs_zero : modelObs (0 : S) = 0 := Finsupp.sum_zero_index

theorem modelObs_single (α a : ℝ) :
    modelObs (Finsupp.single α a : S) = (Finsupp.single α (α * a) : S) :=
  Finsupp.sum_single_index (by simp [mul_zero, Finsupp.single_zero])

theorem modelObs_add (f g : S) :
    modelObs (f + g) = modelObs f + modelObs g :=
  Finsupp.sum_add_index'
    (fun α => by simp [mul_zero])
    (fun α b₁ b₂ => by rw [mul_add, Finsupp.single_add])

theorem nfoldSum_eq_nsmul (n : ℕ) (x : S) :
    nfoldSum (· + ·) 0 n x = n • x := by
  induction n with
  | zero => simp [nfoldSum]
  | succ n ih => simp only [nfoldSum]; rw [ih, succ_nsmul']

theorem nsmul_single (n : ℕ) (a b : ℝ) :
    n • (Finsupp.single a b : S) = (Finsupp.single a (n • b) : S) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul', ih, ← Finsupp.single_add, succ_nsmul']

theorem mapRange_mul_left_eq_smul (α : ℝ) (x : S) :
    Finsupp.mapRange (α * ·) (by simp) x = α • x := by
  ext a; simp [Finsupp.mapRange_apply, smul_eq_mul]

/-! ## Leibniz rule (derivation property of modelObs) -/

private theorem leibniz_proof (a b : S) :
    modelObs (a * b) = modelObs a * b + a * modelObs b := by
  induction a using Finsupp.induction_linear with
  | zero => simp [modelObs_zero]
  | add f g hf hg =>
    rw [add_mul, modelObs_add, hf, hg, modelObs_add]; ring
  | single α r =>
    induction b using Finsupp.induction_linear with
    | zero => simp [modelObs_zero, mul_zero]
    | add f g hf hg =>
      rw [mul_add, modelObs_add, hf, hg, modelObs_add, mul_add, mul_add]; ring
    | single β s =>
      rw [AddMonoidAlgebra.single_mul_single, modelObs_single, modelObs_single,
          modelObs_single, AddMonoidAlgebra.single_mul_single,
          AddMonoidAlgebra.single_mul_single, ← Finsupp.single_add]
      congr 1; ring

/-! ## SpectralMonoid Instance -/

noncomputable instance modelSpectralMonoid : SpectralMonoid S where
  compose := (· * ·)
  obs := modelObs
  f₀ := 1
  f₁ := Finsupp.single 1 1
  z := 0
  obs_f₁ := by
    rw [modelObs_single, one_mul]
  compose_f₀ := one_mul
  compose_assoc := fun a b c => (mul_assoc a b c).symm
  compose_comm := mul_comm
  compose_z := zero_mul
  f₁_cancel := fun _ _ h =>
    mul_left_cancel₀ (Finsupp.single_ne_zero.mpr (one_ne_zero (α := ℝ))) h
  f₀_ne_f₁ := by
    rw [AddMonoidAlgebra.one_def]
    exact fun h => absurd (Finsupp.single_left_injective (one_ne_zero (α := ℝ)) h)
      (by norm_num : (0 : ℝ) ≠ 1)
  f₀_ne_z := one_ne_zero
  f₁_ne_z := Finsupp.single_ne_zero.mpr (one_ne_zero (α := ℝ))

/-! ## DynSemiring Instance -/

noncomputable instance modelDynSemiring : DynSemiring S where
  toSpectralMonoid := modelSpectralMonoid
  oplus := (· + ·)
  oplus_assoc := fun a b c => (add_assoc a b c).symm
  oplus_comm := add_comm
  oplus_z := zero_add
  compose_distrib := mul_add
  obs_f₀ := by
    change modelObs (1 : S) = 0
    rw [AddMonoidAlgebra.one_def, modelObs_single, zero_mul, Finsupp.single_zero]
  leibniz := leibniz_proof
  char_zero := by
    intro n hn
    change nfoldSum (· + ·) 0 n (1 : S) ≠ 0
    rw [nfoldSum_eq_nsmul, AddMonoidAlgebra.one_def, nsmul_single]
    exact Finsupp.single_ne_zero.mpr (by
      rw [nsmul_eq_mul, mul_one]
      exact Nat.cast_ne_zero.mpr (by omega))

/-! ## Bridge lemma: DynSemiring.smul = ℕ-smul -/

private theorem dynsmul_eq_nsmul (n : ℕ) (x : S) : DynSemiring.smul n x = n • x := by
  change nfoldSum (· + ·) 0 n x = n • x
  exact nfoldSum_eq_nsmul n x

/-! ## DynIntDomain Instance -/

noncomputable instance modelDynIntDomain : DynIntDomain S where
  toDynSemiring := modelDynSemiring
  f₁_inv := Finsupp.single (-1) 1
  f₁_inv_spec :=
    (AddMonoidAlgebra.single_mul_single (1:ℝ) (-1:ℝ) 1 1).trans
      (by norm_num; exact AddMonoidAlgebra.one_def.symm)
  oneg := Neg.neg
  oneg_spec := fun s => add_neg_cancel s
  no_zero_divisors := fun _ _ h => mul_eq_zero.mp h

-- Bridge: DynIntDomain at ℝ →₀ ℝ level (needed for cpow elaboration)
private noncomputable instance : DynIntDomain (ℝ →₀ ℝ) := modelDynIntDomain

-- Bridge: compose unfolds to * but rw/simp can't see through the chain.
-- This lemma lets us convert explicitly.
private theorem compose_eq_mul (a b : S) : compose a b = a * b := rfl

/-! ## cpow helper -/

/-- cpow on single-coefficient elements: (δ_r)^n = δ_{n·r}.
    Proof: compose = ring multiplication, so cpow g n = g^n.
    Then (single r 1)^n = single (n*r) 1 by single_mul_single. -/
theorem cpow_single_one (r : ℝ) (n : ℕ) :
    DynIntDomain.cpow (Finsupp.single r (1 : ℝ) : S) n =
    (Finsupp.single (↑n * r) 1 : S) := by
  induction n with
  | zero =>
    simp only [DynIntDomain.cpow_zero, Nat.cast_zero, zero_mul]
    rfl
  | succ n ih =>
    rw [DynIntDomain.cpow_succ, ih, compose_eq_mul,
        AddMonoidAlgebra.single_mul_single, mul_one]
    congr 1; push_cast; ring

/-! ## DynRational Instance -/

noncomputable instance modelDynRational : DynRational S where
  toDynIntDomain := modelDynIntDomain
  root := fun q => Finsupp.single (1 / (q : ℝ)) 1
  root_spec := by
    intro q hq
    rw [cpow_single_one]; congr 1; field_simp
  qdiv := fun n a => Finsupp.mapRange ((↑n : ℝ)⁻¹ * ·) (by simp) a
  qdiv_spec := by
    intro n hn a
    rw [dynsmul_eq_nsmul, mapRange_mul_left_eq_smul, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega)), one_smul]

/-! ## DynComplete Instance -/

noncomputable instance modelDynComplete : DynComplete S where
  toDynRational := modelDynRational
  ratEigen := fun r => Finsupp.single (r : ℝ) 1
  ratEigen_zero := by
    change (Finsupp.single ((0 : ℚ) : ℝ) 1 : S) = (1 : S)
    simp [AddMonoidAlgebra.one_def]
  ratEigen_one := by
    change (Finsupp.single ((1 : ℚ) : ℝ) 1 : S) = (Finsupp.single 1 1 : S)
    simp
  ratEigen_add := by
    intro r s
    exact (AddMonoidAlgebra.single_mul_single (r:ℝ) (s:ℝ) 1 1).trans
      (by simp [mul_one, Rat.cast_add])
  ratEigen_injective := fun _ _ h =>
    Rat.cast_injective (Finsupp.single_left_injective (one_ne_zero (α := ℝ)) h)
  realEigen := fun α => Finsupp.single α 1
  realEigen_rat := fun _ => rfl
  realEigen_add := by
    intro α β
    exact (AddMonoidAlgebra.single_mul_single α β 1 1).trans (by simp [mul_one])
  realEigen_injective := fun _ _ h =>
    Finsupp.single_left_injective (one_ne_zero (α := ℝ)) h
  rsmul := fun α x => α • x
  rsmul_nat := by
    intro n x
    rw [dynsmul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rsmul_inv_nat := by
    intro n hn x
    change (1 / (↑n : ℝ)) • x = Finsupp.mapRange ((↑n : ℝ)⁻¹ * ·) _ x
    rw [one_div, mapRange_mul_left_eq_smul]
  rsmul_add := fun α β x => add_smul α β x
  rsmul_oplus := fun α a b => smul_add α a b
  rsmul_compose := by
    intro α a b
    change a * (α • b) = α • (a * b)
    exact mul_smul_comm α a b
  rsmul_zero_left := fun x => zero_smul ℝ x
  rsmul_one := fun x => one_smul ℝ x
  eigenvalue_real := by
    intro α
    change modelObs (Finsupp.single α 1 : S) = α • (Finsupp.single α 1 : S)
    rw [modelObs_single, ← mapRange_mul_left_eq_smul, Finsupp.mapRange_single]

/-! ## DynZF Instance (explicit)

The forward model uses `Ens = S → Prop` — the full predicate space.
This is correct: CIC provides the complete predicate space, so
`Iff.rfl` proofs are valid here. The point of the abstract `Ens`
is that OTHER models can restrict it (see Countermodels.lean). -/

noncomputable instance modelDynZF : DynZF S where
  toDynComplete := modelDynComplete
  Ens := S → Prop
  mem := fun s A => A s
  ens_ext := fun _ _ h => funext fun s => propext (h s)
  orbitEns := isNat
  orbitEns_spec := fun _ => Iff.rfl
  sepEns := fun A φ => fun s => A s ∧ φ s
  sepEns_spec := fun _ _ _ => Iff.rfl
  imageEns := fun F A => fun y => ∃ x, A x ∧ F x = y
  imageEns_spec := fun _ _ _ => Iff.rfl
  Ens₂ := (S → Prop) → Prop
  mem₂ := fun A P => P A
  ens_ext₂ := fun _ _ h => funext fun A => propext (h A)
  powerEns := fun A => fun B => ∀ s, B s → A s
  powerEns_spec := fun _ _ => Iff.rfl
  unionEns₂ := fun P => fun s => ∃ A, P A ∧ A s
  unionEns₂_spec := fun _ _ => Iff.rfl

end SpectralMonoid.Model
