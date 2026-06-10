/-
  Foundation Bridge (Issues #35, #40, #55)
  =========================================

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
import SpectralArithmetic.Obstruction.Diagonal
import Foundation.FirstOrder.Incompleteness.GödelRosser
import Foundation.FirstOrder.Incompleteness.Examples

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
set_option maxHeartbeats 800000 in
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

end FoundationBridge
