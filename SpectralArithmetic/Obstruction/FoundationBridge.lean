/-
  Foundation Bridge (Issues #35, #40, #55, #68)
  ==============================================

  First contact between this project's abstract incompleteness
  development and the FormalizedFormalLogic Foundation library
  (pinned at 066bfa6, the last v4.28-line revision), which proves
  Godel-Rosser incompleteness for arithmetic theories from real
  representability machinery.

  Two results:

  1. A NEGATIVE result about our own abstraction, found by attempting
     instantiation: `Incompleteness.DiagonalTheory` is DEGENERATE.
     Its diag field demands fixed points for ARBITRARY sentence
     transformers P : Sentence -> Sentence, not just formula-definable
     ones — and no theory with both a provable and an unprovable
     sentence satisfies that (take P s := if provable s then f else t;
     both diag directions then contradict). Real theories satisfy the
     diagonal lemma only for formulas. So the DiagonalTheory route to
     incompleteness (Incompleteness.lean Parts 2-8) is vacuous for
     every nontrivial theory; `Diagonal.GodelSystem`, whose
     compose_diag is formula-based, is the correct abstraction.
     This is the same genus of finding as the three inconsistent
     axioms repaired on 2026-06-10, caught the same way: by testing
     the abstraction against something real.

  2. A POSITIVE instantiation: our `FormalTheory` abstraction
     instantiated with Foundation's actual Peano Arithmetic.
     `paTheory.consistent` and an undecidable sentence for PA are
     obtained from Foundation's Godel-Rosser theorem — the first
     point of contact between the framework and a real arithmetic
     theory with genuine Godel coding.

  Axiom transparency: Foundation's PA-level instances currently rest
  on two axioms of its own (`ISigma1_delta1Definable`,
  `PA_delta1Definable` in Foundation.FirstOrder.Incompleteness.Examples,
  marked TODO upstream — Delta_1-definability of the theories'
  axiom sets). `#print axioms` on Part 2's theorems shows them.
  They are bookkeeping facts of a different caliber than the
  representability content, but the paper must report them.

  Next step (separate change): weaken `Diagonal.GodelSystem`'s
  compose_diag_prov to the self-application instance (the only one
  the diagonal lemma uses) and instantiate it from Foundation's
  `fixedpoint`/`diagonal`, discharging PAGodelSystem's two axioms.
-/

import SpectralArithmetic.Obstruction.TheoryInterfaces
import SpectralArithmetic.Obstruction.ForcedLossCore
import SpectralArithmetic.Obstruction.Diagonal
import Foundation.FirstOrder.Incompleteness.GödelRosser
import Foundation.FirstOrder.Incompleteness.Examples

set_option linter.style.setOption false
set_option linter.flexible false

namespace FoundationBridge

/-! ## Part 1: DiagonalTheory Is Degenerate -/

/-- **DEGENERACY OF DiagonalTheory:** no `DiagonalTheory` has both a
    provable and an unprovable sentence. The arbitrary-transformer
    diagonal is too strong for any nontrivial provability predicate. -/
theorem diagonalTheory_degenerate {S : Type*}
    (T : Incompleteness.DiagonalTheory S)
    {t f : S} (ht : T.provable t) (hf : ¬T.provable f) : False := by
  classical
  set P : S → S := fun s => if T.provable s then f else t with hP
  by_cases hd : T.provable (T.diag P)
  · have h1 := T.diag_mp P hd
    have hPd : P (T.diag P) = f := by rw [hP]; exact if_pos hd
    rw [hPd] at h1
    exact hf h1
  · have hPd : P (T.diag P) = t := by rw [hP]; exact if_neg hd
    exact hd (T.diag_mpr P (by rw [hPd]; exact ht))

/-- Contrapositive packaging: every `DiagonalTheory` is trivial —
    either everything is provable or nothing is. -/
theorem diagonalTheory_trivial {S : Type*}
    (T : Incompleteness.DiagonalTheory S) :
    (∀ s, T.provable s) ∨ (∀ s, ¬T.provable s) := by
  classical
  by_cases h : ∃ t, T.provable t
  · obtain ⟨t, ht⟩ := h
    left
    intro s
    by_contra hf
    exact diagonalTheory_degenerate T ht hf
  · right
    intro s hs
    exact h ⟨s, hs⟩

/-! ## Part 2: PA via Foundation -/

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Our `FormalTheory` abstraction, instantiated with Foundation's
    Peano Arithmetic: real first-order sentences, real provability. -/
def paTheory : Incompleteness.FormalTheory (Sentence ℒₒᵣ) where
  provable σ := 𝗣𝗔 ⊢ σ
  neg σ := ∼σ

/-- PA is consistent in our abstraction's sense, by soundness over
    the standard model: a provable-and-refutable sentence would be
    both true and false in ℕ. -/
theorem paTheory_consistent : paTheory.consistent := by
  intro σ h
  have h1 : ℕ ⊧ₘ σ := consequence_iff.mp (sound! h.1) ℕ inferInstance
  have h2 : ℕ ⊧ₘ (∼σ) := consequence_iff.mp (sound! h.2) ℕ inferInstance
  simp [models_iff] at h1 h2
  exact h2 h1

/-- **PA IS INCOMPLETE, INSTANTIATED:** an undecidable sentence for
    Foundation's PA, in our abstraction's vocabulary. From the
    Godel-Rosser theorem. -/
theorem paTheory_incomplete : ∃ σ, paTheory.undecidable σ := by
  have h : Entailment.Incomplete (𝗣𝗔 : Theory ℒₒᵣ) :=
    incomplete' 𝗣𝗔
  obtain ⟨σ, h1, h2⟩ := h.indep
  exact ⟨σ, h1, h2⟩

/-! ## Part 3: The GodelSystem Instance for Real PA

    Milestone 2: `Diagonal.GodelSystem` — the abstraction from which
    our diagonal lemma and incompleteness theorems are PROVED —
    instantiated with Foundation's Peano Arithmetic. Coding is
    Foundation's Godel quote (= `Encodable.encode` over ℕ, with a
    genuine decode); `compose_diag` is Foundation's `diag`; the
    representability field is discharged by the fixed-point theorem
    of arithmetic (`diagonal`). With this instance, our
    `diagonal_lemma` runs on real PA. -/

open Entailment in
/-- Our GodelSystem, instantiated with Foundation's PA. -/
noncomputable def paGodelSystemF : Diagonal.GodelSystem (Sentence ℒₒᵣ) where
  provable σ := 𝗣𝗔 ⊢ σ
  neg σ := ∼σ
  Formula := Semisentence ℒₒᵣ 1
  subst φ n := φ/[(n : Semiterm ℒₒᵣ Empty 0)]
  scode σ := ⌜σ⌝
  fcode φ := ⌜φ⌝
  decode n := (Encodable.decode n).getD ⊤
  decode_fcode φ := by
    simp [Sentence.quote_eq_encode]
  diagN n := ⌜(((Encodable.decode n).getD ⊤ : Semisentence ℒₒᵣ 1))/[(n : Semiterm ℒₒᵣ Empty 0)]⌝
  diagN_spec _ := rfl
  compose_diag β := diag β
  compose_diag_prov β := by
    have hdec : ((Encodable.decode ((⌜diag β⌝ : ℕ))).getD ⊤ : Semisentence ℒₒᵣ 1) = diag β := by
      simp [Sentence.quote_eq_encode]
    have hd := diagonal (T := 𝗣𝗔) β
    constructor
    · intro h
      have h' : 𝗣𝗔 ⊢ fixedpoint β := by simpa [fixedpoint] using h
      have h2 := K!_left hd ⨀! h'
      simpa [hdec, fixedpoint] using h2
    · intro h
      have h2 : 𝗣𝗔 ⊢ β/[(⌜fixedpoint β⌝ : Semiterm ℒₒᵣ Empty 0)] := by
        simpa [hdec, fixedpoint] using h
      have h' := K!_right hd ⨀! h2
      simpa [fixedpoint] using h'
  compose_diag_neg β := by
    have hdec : ((Encodable.decode ((⌜diag β⌝ : ℕ))).getD ⊤ : Semisentence ℒₒᵣ 1) = diag β := by
      simp [Sentence.quote_eq_encode]
    have hd := ENN!_of_E! (diagonal (T := 𝗣𝗔) β)
    constructor
    · intro h
      have h' : 𝗣𝗔 ⊢ ∼(fixedpoint β) := by simpa [fixedpoint] using h
      have h2 := K!_left hd ⨀! h'
      simpa [hdec, fixedpoint] using h2
    · intro h
      have h2 : 𝗣𝗔 ⊢ ∼(β/[(⌜fixedpoint β⌝ : Semiterm ℒₒᵣ Empty 0)]) := by
        simpa [hdec, fixedpoint] using h
      have h' := K!_right hd ⨀! h2
      simpa [fixedpoint] using h'

/-- **THE DIAGONAL LEMMA RUNS ON REAL PA:** for every formula β with
    one free variable, the Godel construction over Foundation's PA is
    a provability fixed point of β. Our abstract diagonal_lemma,
    instantiated. -/
theorem pa_diagonal_lemma (β : Semisentence ℒₒᵣ 1) :
    (𝗣𝗔 ⊢ Diagonal.GodelSystem.godelConstruction paGodelSystemF β) ↔
    (𝗣𝗔 ⊢ β/[((⌜Diagonal.GodelSystem.godelConstruction paGodelSystemF β⌝ : ℕ) :
        Semiterm ℒₒᵣ Empty 0)]) :=
  Diagonal.GodelSystem.diagonal_lemma paGodelSystemF β

/-! ## Part 4: Forced Loss on Real PA Terms (#68)

    The real-PA instance of ForcedLossCore's MeaningPreserving: the
    one-step unfolding of PA's own recursion for multiplication,
    S(a) * b = a * b + b — written in ℒₒᵣ, where S(a) is a + 1 — is
    a meaning-preserving moving rewrite on closed terms under the
    standard-model valuation. Preservation is succ-mul arithmetic;
    movement is root-symbol discrimination (mul vs add). This
    replaces the weakest informal link of Universal.lean Part 10
    ("PA's own evaluation rules already do this") with a
    machine-checked instance on genuine syntax: real PA term
    semantics has forced loss, its valuation is not injective, and
    no injective Godel coding of closed PA terms factors through
    ℕ-evaluation. -/

open UniversalObstruction.ForcedLoss

/-- Closed terms of the language of arithmetic. -/
abbrev PAClosedTerm : Type := Semiterm ℒₒᵣ Empty 0

/-- Standard-model evaluation of closed PA terms. -/
def valNat (t : PAClosedTerm) : ℕ :=
  Semiterm.val (standardModel ℕ) ![] Empty.elim t

/-- The closed term 0. -/
def paZero : PAClosedTerm := Semiterm.func Language.ORing.Func.zero ![]

/-- The redex (a + 1) * b: the left side of PA's multiplication
    recursion, with successor written as + 1 in ℒₒᵣ. -/
def sMulRedex (a b : PAClosedTerm) : PAClosedTerm :=
  Semiterm.func Language.ORing.Func.mul
    ![Semiterm.func Language.ORing.Func.add ![a, Semiterm.func Language.ORing.Func.one ![]], b]

/-- The contractum a * b + b: the right side of the recursion. -/
def sMulContract (a b : PAClosedTerm) : PAClosedTerm :=
  Semiterm.func Language.ORing.Func.add ![Semiterm.func Language.ORing.Func.mul ![a, b], b]

@[simp] lemma valNat_sMulRedex (a b : PAClosedTerm) :
    valNat (sMulRedex a b) = (valNat a + 1) * valNat b := by
  simp [valNat, sMulRedex, standardModel]

@[simp] lemma valNat_sMulContract (a b : PAClosedTerm) :
    valNat (sMulContract a b) = valNat a * valNat b + valNat b := by
  simp [valNat, sMulContract, standardModel]

/-- Preservation: PA's recursion step is invisible to the standard
    valuation. -/
lemma valNat_sMulContract_eq (a b : PAClosedTerm) :
    valNat (sMulContract a b) = valNat (sMulRedex a b) := by
  rw [valNat_sMulContract, valNat_sMulRedex, Nat.add_mul, Nat.one_mul]

/-- Movement: the contractum is add-rooted, the redex mul-rooted —
    root-symbol discrimination on genuine ℒₒᵣ syntax. -/
lemma sMulContract_ne_sMulRedex (x y a b : PAClosedTerm) :
    sMulContract x y ≠ sMulRedex a b := by
  simp [sMulContract, sMulRedex]

open Classical in
/-- One root step of PA's multiplication recursion: contract the
    redex (a + 1) * b wherever the whole term has that shape; leave
    every other term unchanged. -/
noncomputable def sMulStep (t : PAClosedTerm) : PAClosedTerm :=
  if h : ∃ p : PAClosedTerm × PAClosedTerm, t = sMulRedex p.1 p.2 then
    sMulContract h.choose.1 h.choose.2
  else t

/-- **REAL PA HAS A MEANING-PRESERVING REWRITE:** the recursion step
    is invisible to standard-model evaluation — ForcedLossCore's
    MeaningPreserving, instantiated on genuine PA syntax. -/
theorem sMulStep_meaningPreserving : MeaningPreserving valNat sMulStep := by
  intro t
  unfold sMulStep
  split
  · next h => rw [valNat_sMulContract_eq, ← h.choose_spec]
  · rfl

/-- **AND IT MOVES:** on every redex the step changes the term. -/
theorem sMulStep_moves (a b : PAClosedTerm) :
    sMulStep (sMulRedex a b) ≠ sMulRedex a b := by
  unfold sMulStep
  rw [dif_pos ⟨(a, b), rfl⟩]
  exact sMulContract_ne_sMulRedex _ _ a b

/-- **FORCED LOSS ON REAL PA:** the standard-model semantics of
    genuine PA syntax identifies distinct closed terms —
    loss_of_move at the recursion redex. -/
theorem pa_semanticLoss : SemanticLoss valNat :=
  sMulStep_meaningPreserving.loss_of_move (sMulStep_moves paZero paZero)

/-- The standard valuation of closed PA terms is not injective. -/
theorem valNat_not_injective : ¬ Function.Injective valNat := fun hinj =>
  sMulStep_moves paZero paZero (hinj (sMulStep_meaningPreserving _))

/-- **NO INJECTIVE GODEL CODING IS EXTENSIONAL FOR ℕ-EVALUATION:**
    no injective map on closed PA terms factors through the standard
    valuation — the encoding obstruction calibrated against real
    syntax. -/
theorem pa_no_injective_extensional {O : Type*} (ε : PAClosedTerm → O)
    (hε : Function.Injective ε) :
    ¬ ∃ oS : ℕ → O, ∀ t, ε t = oS (valNat t) := by
  rintro ⟨oS, hfac⟩
  obtain ⟨t₁, t₂, hne, heq⟩ := pa_semanticLoss
  exact hne (hε (by rw [hfac t₁, hfac t₂, heq]))

end FoundationBridge
