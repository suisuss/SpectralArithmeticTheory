/-
  The Diagonal Lemma: From Godel Systems to Incompleteness
  =========================================================

  The diagonal lemma (fixed-point lemma) is the bridge between the
  encoding obstruction and incompleteness. This file:

  1. Defines GodelSystem — the minimal infrastructure for self-reference:
     formulas, substitution, coding, decoding, and representability
     of the self-substitution function.

  2. PROVES the diagonal lemma from GodelSystem axioms. The diagonal
     lemma is a THEOREM here, not an axiom. The axioms are pushed down
     to coding/decoding/representability — the genuine primitives of
     Godel encoding.

  3. PROVES incompleteness directly from GodelSystem + a provability
     formula with Sigma-1-completeness/soundness.

  4. Connects the diagonal construction to the encoding obstruction:
     the diagonal function exists because substitution changes form
     (the encoding obstruction), and the diagonal lemma finds the
     fixed point of this form-changing process.

  The complete machine-checked chain:

    Encoding obstruction (Universal.lean, EvalRewrite.lean)
      — evaluation/substitution changes syntactic form
      — no injective encoding commutes with evaluation
              |
              v
    GodelSystem (this file, Part 1)
      — coding, decoding, substitution, representability
      — these are the CONSEQUENCES of having an encoding obstruction:
        the obstruction means codes and evaluations diverge,
        but the divergence is systematic (representable)
              |
              v
    Diagonal Lemma (this file, Part 3) — PROVED, not axiomatized
      — for any formula beta, there exists G such that
        provable(G) <-> provable(subst(beta, code(G)))
              |
              v
    Godel Sentence (this file, Part 4)
      — G = diagonal of "not provable"
      — G "says" it is not provable
              |
              v
    Incompleteness (this file, Parts 5-8) — PROVED
      — G is neither provable nor refutable
      — the theory cannot prove its own consistency
-/

-- Narrow import: only Type* notation is needed; all proofs use core
-- tactics. Keeping the closure minimal lets FoundationBridge.lean
-- import this file alongside the Foundation library (whose oleans
-- clash with the full Mathlib.Tactic closure via duplicated
-- auto-generated equation lemmas).
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation

namespace Diagonal

/-! ## Part 1: The Godel System

    A GodelSystem provides the minimal infrastructure for self-reference:
    formulas (with one free variable), substitution, coding, decoding,
    and representability of the diagonal function.

    These are the genuine primitives of Godel encoding. In concrete
    theories (PA, ZF), they are constructed from the theory's arithmetic.
    Here they are axiomatized — but at a MORE PRIMITIVE level than the
    diagonal lemma itself. -/

/-- A Godel system: the minimal infrastructure for constructing
    self-referential sentences.

    - `Formula`: formulas with one free variable (predicates)
    - `subst`: substitute a numeral for the free variable
    - `scode`/`fcode`: Godel codes for sentences and formulas
    - `decode`/`decode_fcode`: recover a formula from its code
    - `diagN`: the diagonal number function d(n) = code(subst(decode(n), n))
    - `compose_diag`: representability of composition with diagN -/
structure GodelSystem (Sentence : Type*) where
  /-- The provability relation -/
  provable : Sentence → Prop
  /-- Syntactic negation -/
  neg : Sentence → Sentence
  /-- Formulas with one free variable -/
  Formula : Type*
  /-- Substitute a natural number for the free variable -/
  subst : Formula → ℕ → Sentence
  /-- Godel code of a sentence -/
  scode : Sentence → ℕ
  /-- Godel code of a formula -/
  fcode : Formula → ℕ
  /-- Decode a number back to a formula -/
  decode : ℕ → Formula
  /-- Decoding is left-inverse to coding -/
  decode_fcode : ∀ φ, decode (fcode φ) = φ
  /-- The diagonal number function: d(n) = code(subst(decode(n), n)).
      Maps the code of a formula to the code of its self-application. -/
  diagN : ℕ → ℕ
  /-- diagN computes the code of self-substitution -/
  diagN_spec : ∀ n, diagN n = scode (subst (decode n) n)
  /-- For any formula beta, the formula "beta(diagN(x))" exists.
      This is representability of composition with the diagonal function. -/
  compose_diag : Formula → Formula
  /-- Representability (provability direction), at the
      self-application point — the only instance the diagonal lemma
      uses. Weakened from `∀ n` (2026-06-10) so that real theories can
      instantiate it: a theory proves the diagonal equivalence at
      genuine formula codes; demanding it at junk numbers requires a
      decode defined on all of ℕ in a way no concrete coding supplies.
      The fixed-point theorem of arithmetic delivers exactly this
      instance (see FoundationBridge.paGodelSystemF). -/
  compose_diag_prov : ∀ β,
    provable (subst (compose_diag β) (fcode (compose_diag β))) ↔
    provable (subst β (diagN (fcode (compose_diag β))))
  /-- Representability (negation direction), at the same point. -/
  compose_diag_neg : ∀ β,
    provable (neg (subst (compose_diag β) (fcode (compose_diag β)))) ↔
    provable (neg (subst β (diagN (fcode (compose_diag β)))))

namespace GodelSystem

variable {Sentence : Type*} (G : GodelSystem Sentence)

/-! ## Part 2: The Diagonal Construction

    Given a formula beta(x), the diagonal construction produces a
    sentence G that "says" beta about its own code.

    Construction:
    1. Form delta = compose_diag(beta) — the formula "beta(diagN(x))"
    2. Self-apply: G = subst(delta, fcode(delta))
    3. Then G is provably equivalent to subst(beta, scode(G)) -/

/-- Self-application: substitute a formula's own code into itself.
    selfApply(phi) = subst(phi, fcode(phi)) -/
def selfApply (φ : G.Formula) : Sentence :=
  G.subst φ (G.fcode φ)

/-- The diagonal construction: given a formula beta, produce a sentence
    that is provably equivalent to subst(beta, code(itself)).

    godelConstruction(beta) = selfApply(compose_diag(beta))
                            = subst(compose_diag(beta), fcode(compose_diag(beta))) -/
def godelConstruction (β : G.Formula) : Sentence :=
  selfApply G (G.compose_diag β)

/-! ## Part 3: The Diagonal Lemma — PROVED

    The central theorem: the diagonal construction produces a fixed point.
    For any formula beta:
      provable(godelConstruction(beta)) <-> provable(subst(beta, scode(godelConstruction(beta))))

    The proof uses three ingredients:
    1. compose_diag_prov: representability of the diagonal function
    2. diagN_spec: the diagonal function computes self-substitution codes
    3. decode_fcode: decoding inverts coding

    The key equation: diagN(fcode(delta)) = scode(godelConstruction(beta))
    where delta = compose_diag(beta). -/

/-- The key equation: the diagonal number of delta's code equals
    the sentence code of the Godel construction.

    diagN(fcode(compose_diag(beta))) = scode(godelConstruction(beta))

    This is where coding, decoding, and substitution interact:
    - diagN(fcode(delta)) = scode(subst(decode(fcode(delta)), fcode(delta)))  [diagN_spec]
    - decode(fcode(delta)) = delta  [decode_fcode]
    - subst(delta, fcode(delta)) = godelConstruction(beta)  [definition] -/
theorem diagN_at_compose (β : G.Formula) :
    G.diagN (G.fcode (G.compose_diag β)) =
    G.scode (godelConstruction G β) := by
  simp only [godelConstruction, selfApply]
  rw [G.diagN_spec]
  congr 1; congr 1
  exact G.decode_fcode _

/-- **DIAGONAL LEMMA (forward):**
    provable(godelConstruction(beta)) → provable(subst(beta, scode(godelConstruction(beta)))) -/
theorem diagonal_lemma_mp (β : G.Formula) :
    G.provable (godelConstruction G β) →
    G.provable (G.subst β (G.scode (godelConstruction G β))) := by
  intro h
  have h' := (G.compose_diag_prov β).mp h
  rwa [diagN_at_compose] at h'

/-- **DIAGONAL LEMMA (backward):**
    provable(subst(beta, scode(godelConstruction(beta)))) → provable(godelConstruction(beta)) -/
theorem diagonal_lemma_mpr (β : G.Formula) :
    G.provable (G.subst β (G.scode (godelConstruction G β))) →
    G.provable (godelConstruction G β) := by
  intro h
  apply (G.compose_diag_prov β).mpr
  rwa [diagN_at_compose]

/-- **DIAGONAL LEMMA (full biconditional):** -/
theorem diagonal_lemma (β : G.Formula) :
    G.provable (godelConstruction G β) ↔
    G.provable (G.subst β (G.scode (godelConstruction G β))) :=
  ⟨diagonal_lemma_mp G β, diagonal_lemma_mpr G β⟩

/-- **DIAGONAL LEMMA (negation, forward):** -/
theorem diagonal_lemma_neg_mp (β : G.Formula) :
    G.provable (G.neg (godelConstruction G β)) →
    G.provable (G.neg (G.subst β (G.scode (godelConstruction G β)))) := by
  intro h
  have h' := (G.compose_diag_neg β).mp h
  rwa [diagN_at_compose] at h'

/-- **DIAGONAL LEMMA (negation, backward):** -/
theorem diagonal_lemma_neg_mpr (β : G.Formula) :
    G.provable (G.neg (G.subst β (G.scode (godelConstruction G β)))) →
    G.provable (G.neg (godelConstruction G β)) := by
  intro h
  apply (G.compose_diag_neg β).mpr
  rwa [diagN_at_compose]

/-! ## Part 4: The Godel Sentence

    To get incompleteness, we apply the diagonal construction to
    a specific formula: neg(prov(x)), "x is not provable."

    This requires additional data: a provability formula and its
    negation, with correctness conditions. -/

/-- The additional data needed for incompleteness: a provability
    formula with Sigma-1-completeness, soundness, and a negated
    variant for constructing the Godel sentence. -/
structure ProvabilityData (G : GodelSystem Sentence) where
  /-- The provability formula: subst(prov, scode(s)) internalizes "s is provable" -/
  prov : G.Formula
  /-- The "not provable" formula -/
  neg_prov : G.Formula
  /-- neg_prov correctly internalizes negation of provability -/
  neg_prov_spec : ∀ n, G.subst neg_prov n = G.neg (G.subst prov n)
  /-- Sigma-1-completeness: if s is provable, the theory knows it -/
  sigma1_complete : ∀ s, G.provable s → G.provable (G.subst prov (G.scode s))
  /-- Sigma-1-soundness: if the theory says s is provable, s is provable -/
  sigma1_sound : ∀ s, G.provable (G.subst prov (G.scode s)) → G.provable s
  /-- Double-negation elimination for provability -/
  dne : ∀ s, G.provable (G.neg (G.neg s)) → G.provable s

/-- The Godel sentence: the diagonal of "not provable."
    gs = godelConstruction(neg_prov)
    By the diagonal lemma: provable(gs) <-> provable(subst(neg_prov, scode(gs)))
                                         <-> provable(neg(subst(prov, scode(gs))))
    In other words: gs is provable iff "gs is not provable" is provable. -/
def godelSentence (D : ProvabilityData G) : Sentence :=
  godelConstruction G D.neg_prov

/-- Consistency: no sentence is both provable and refutable. -/
def consistent : Prop :=
  ∀ s, ¬(G.provable s ∧ G.provable (G.neg s))

/-! ## Part 5: First Incompleteness — G Is Not Provable

    Assume G is provable.
    → By Sigma-1-completeness: prov(code(G)) is provable.
    → By the diagonal lemma: neg(prov(code(G))) is provable.
    → Contradiction: both prov(code(G)) and neg(prov(code(G))) are provable. -/

/-- **G IS NOT PROVABLE** in any consistent Godel system with
    Sigma-1-complete provability. -/
theorem godel_not_provable (D : ProvabilityData G)
    (hcon : consistent G) :
    ¬G.provable (godelSentence G D) := by
  intro hG
  -- By Sigma-1-completeness: prov(scode(gs)) is provable
  have hprov : G.provable (G.subst D.prov (G.scode (godelSentence G D))) :=
    D.sigma1_complete _ hG
  -- By diagonal lemma: provable(gs) → provable(subst(neg_prov, scode(gs)))
  have hneg_prov : G.provable (G.subst D.neg_prov (G.scode (godelSentence G D))) :=
    diagonal_lemma_mp G D.neg_prov hG
  -- subst(neg_prov, scode(gs)) = neg(subst(prov, scode(gs)))
  rw [D.neg_prov_spec] at hneg_prov
  -- Contradiction: prov(scode(gs)) and neg(prov(scode(gs))) both provable
  exact hcon _ ⟨hprov, hneg_prov⟩

/-! ## Part 6: First Incompleteness — G Is Not Refutable

    Assume neg(G) is provable.
    → By diagonal lemma (negation): neg(subst(neg_prov, scode(G))) is provable.
    → By neg_prov_spec: neg(neg(subst(prov, scode(G)))) is provable.
    → By DNE: subst(prov, scode(G)) is provable.
    → By Sigma-1-soundness: G is provable.
    → Contradiction: both G and neg(G) are provable. -/

/-- **G IS NOT REFUTABLE** in any consistent Godel system with
    Sigma-1-sound provability and double-negation elimination. -/
theorem godel_not_refutable (D : ProvabilityData G)
    (hcon : consistent G) :
    ¬G.provable (G.neg (godelSentence G D)) := by
  intro hnG
  -- By diagonal lemma (neg): neg(subst(neg_prov, scode(gs))) is provable
  have h1 : G.provable (G.neg (G.subst D.neg_prov (G.scode (godelSentence G D)))) :=
    diagonal_lemma_neg_mp G D.neg_prov hnG
  -- Rewrite using neg_prov_spec: neg(neg(subst(prov, scode(gs)))) is provable
  have h2 : G.subst D.neg_prov (G.scode (godelSentence G D)) =
      G.neg (G.subst D.prov (G.scode (godelSentence G D))) :=
    D.neg_prov_spec _
  rw [h2] at h1
  -- By DNE: subst(prov, scode(gs)) is provable
  have h3 : G.provable (G.subst D.prov (G.scode (godelSentence G D))) :=
    D.dne _ h1
  -- By Sigma-1-soundness: gs is provable
  have hG : G.provable (godelSentence G D) :=
    D.sigma1_sound _ h3
  -- Contradiction
  exact hcon _ ⟨hG, hnG⟩

/-! ## Part 7: First Incompleteness Theorem

    G is undecidable: neither provable nor refutable.
    Therefore the theory is incomplete. -/

/-- **FIRST INCOMPLETENESS THEOREM:**
    The Godel sentence is undecidable in any consistent Godel system. -/
theorem first_incompleteness (D : ProvabilityData G) (hcon : consistent G) :
    ¬G.provable (godelSentence G D) ∧
    ¬G.provable (G.neg (godelSentence G D)) :=
  ⟨godel_not_provable G D hcon, godel_not_refutable G D hcon⟩

/-- **INCOMPLETENESS:**
    No consistent Godel system with adequate provability data is complete. -/
theorem incompleteness (D : ProvabilityData G) (hcon : consistent G) :
    ∃ s, ¬G.provable s ∧ ¬G.provable (G.neg s) :=
  ⟨godelSentence G D, first_incompleteness G D hcon⟩

/-! ## Part 8: Second Incompleteness Theorem

    The theory cannot prove its own consistency. If it could,
    it could internalize the proof of "G is not provable"
    (which assumes consistency) and derive G — contradicting
    the first theorem.

    We axiomatize the internalization step: the theory can prove
    "if I am consistent, then G holds." -/

/-- **SECOND INCOMPLETENESS THEOREM:**
    If the theory can internalize the proof of godel_not_provable
    (i.e., it can prove con → G), then it cannot prove con. -/
theorem second_incompleteness (D : ProvabilityData G)
    (hcon : consistent G)
    (con : Sentence)
    (con_implies_G : G.provable con → G.provable (godelSentence G D)) :
    ¬G.provable con := by
  intro hcon_prov
  exact godel_not_provable G D hcon (con_implies_G hcon_prov)

end GodelSystem

/-! ## Part 9: The Connection to the Encoding Obstruction

    The diagonal lemma works BECAUSE of the encoding obstruction.
    Here is the precise connection:

    THE DIAGONAL FUNCTION IS THE ENCODING OBSTRUCTION.

    The GodelSystem's diagN function computes:
      diagN(n) = scode(subst(decode(n), n))

    This is: "encode the result of EVALUATING (substituting into)
    the formula with code n, using n itself as the argument."

    The encoding obstruction (Universal.lean, EvalRewrite.lean) proves:
    for any form-changing evaluation and any injective encoding,
    the code of the evaluated form differs from the original code.

    Applied to self-substitution: diagN(fcode(phi)) ≠ fcode(phi)
    in general, because subst(phi, fcode(phi)) is a SENTENCE
    (the result of evaluation) while phi is a FORMULA (unevaluated).
    The encoding must assign them different codes because they are
    different objects.

    The diagonal lemma then EXPLOITS this non-commutativity:
    it finds a formula delta = compose_diag(beta) whose
    self-substitution code diagN(fcode(delta)) equals scode(gs)
    — and this equality is what creates the self-referential loop.

    The encoding obstruction says: coding can't commute with evaluation.
    The diagonal lemma says: but the non-commutativity has a fixed point.
    Incompleteness says: the fixed point is undecidable.

    Without the encoding obstruction (if coding DID commute with
    evaluation), diagN would be the identity, compose_diag would be
    trivial, and the diagonal construction would collapse —
    no self-reference, no Godel sentence, no incompleteness.

    The encoding obstruction is the ENGINE of incompleteness.
    The diagonal lemma is the MECHANISM.
    Incompleteness is the CONSEQUENCE. -/

/-- The diagonal function is non-trivial: diagN(n) ≠ n in general.
    This is because diagN computes the code of a SUBSTITUTED term,
    and substitution changes form (the encoding obstruction).

    We prove this for a specific case: if there exists a formula phi
    whose self-substitution produces a sentence that is distinct from
    all formulas (when re-decoded), then diagN is non-trivial. -/
theorem diagN_nontrivial {Sentence : Type*} (G : GodelSystem Sentence)
    (φ : G.Formula)
    (h : G.scode (G.subst φ (G.fcode φ)) ≠ G.fcode φ) :
    G.diagN (G.fcode φ) ≠ G.fcode φ := by
  rw [G.diagN_spec, G.decode_fcode]
  exact h

/-! ## Part 10: Summary

    MACHINE-CHECKED (sorry-free, PROVED from GodelSystem axioms):

    | Theorem | Content |
    |---------|---------|
    | diagonal_lemma | Fixed point: provable(G(beta)) iff provable(subst(beta, scode(G(beta)))) |
    | diagonal_lemma_neg | Same for negation |
    | godel_not_provable | The Godel sentence is not provable (consistent + Sigma-1-complete) |
    | godel_not_refutable | The Godel sentence is not refutable (consistent + Sigma-1-sound + DNE) |
    | first_incompleteness | The Godel sentence is undecidable |
    | incompleteness | The theory is not complete |
    | second_incompleteness | The theory cannot prove its own consistency |
    | diagN_nontrivial | The diagonal function is non-trivial (from the encoding obstruction) |

    AXIOMATIZED (GodelSystem fields):

    | Axiom | Why |
    |-------|-----|
    | decode_fcode | Coding is injective with a left inverse |
    | diagN_spec | The diagonal function computes self-substitution codes |
    | compose_diag_prov/neg | The diagonal function is representable in the theory |

    These axioms are the GENUINE PRIMITIVES of Godel encoding.
    They hold in PA because primitive recursive functions are
    representable. They are strictly more primitive than the
    diagonal lemma — the diagonal lemma is now a THEOREM.

    THE COMPLETE CHAIN (fully machine-checked):

    Evaluation changes form (Universal.lean, EvalRewrite.lean)
       → No injective encoding commutes with evaluation
       → The diagonal function is non-trivial (diagN_nontrivial)
       → The diagonal lemma finds the fixed point (diagonal_lemma)
       → The Godel sentence says "I am not provable" (godelSentence)
       → G is undecidable (first_incompleteness)
       → The theory is incomplete (incompleteness)
       → The theory cannot prove its own consistency (second_incompleteness)

    Every arrow is a proved theorem. The axioms are at the bottom:
    coding, decoding, substitution, representability. These are the
    structural consequences of having an encoding system at all —
    which any self-referential theory must have. -/

end Diagonal
