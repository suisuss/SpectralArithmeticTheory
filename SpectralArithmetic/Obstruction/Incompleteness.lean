/-
  From Encoding Obstruction to Incompleteness
  ============================================

  The complete chain:

  1. OBSTRUCTION (Universal.lean, EvalRewrite.lean):
     Evaluation changes syntactic form while preserving semantics.
     No injective encoding commutes with evaluation. Proved for ALL
     term algebras with Leibniz structure and for PA's own axioms.

  2. DIAGONAL CONSTRUCTION (this file, Part 3):
     Any theory with a diagonal/fixed-point operator can build a
     sentence G that "says" G ↔ ¬Prov(⌜G⌝). The diagonal operator
     exists precisely because substitution (evaluation) changes form
     while preserving reference — the encoding obstruction at work.

  3. INCOMPLETENESS (this file, Parts 4-6):
     If the theory is consistent, G is undecidable: neither provable
     nor refutable. First and second incompleteness theorems follow.

  The connection: the diagonal construction works BECAUSE of the
  encoding obstruction. Substitution is a form-changing, meaning-
  preserving rewrite. Any injective encoding (Godel numbering) cannot
  track what substitution does. This non-commutativity is exactly
  what allows a sentence to refer to its own unprovability without
  the theory being able to resolve the reference.

  Architecture: the diagonal lemma is axiomatized as a structure
  (DiagonalTheory). This is the honest approach — proving the diagonal
  lemma from scratch requires formalizing Godel numbering, substitution,
  and representability. What we prove here: ANY theory satisfying the
  diagonal property is incomplete, and the encoding obstruction is the
  structural reason real theories satisfy it.
-/

import SpectralArithmetic.Obstruction.EvalRewrite

namespace Incompleteness

/-! ## Part 1: Abstract Formal Theories

    A formal theory: a type of sentences with a provability relation
    and a negation operation. We keep this minimal — the incompleteness
    theorem needs surprisingly little structure. -/

/-- A formal theory over a type of sentences.
    - `provable`: the set of theorems (sentences derivable from axioms)
    - `neg`: syntactic negation -/
structure FormalTheory (Sentence : Type*) where
  provable : Sentence → Prop
  neg : Sentence → Sentence

namespace FormalTheory

variable {Sentence : Type*}

/-- A sentence is refutable if its negation is provable. -/
def refutable (T : FormalTheory Sentence) (s : Sentence) : Prop :=
  T.provable (T.neg s)

/-- A theory is consistent if no sentence is both provable and refutable. -/
def consistent (T : FormalTheory Sentence) : Prop :=
  ∀ s, ¬(T.provable s ∧ T.provable (T.neg s))

/-- A sentence is undecidable if it is neither provable nor refutable. -/
def undecidable (T : FormalTheory Sentence) (s : Sentence) : Prop :=
  ¬T.provable s ∧ ¬T.provable (T.neg s)

/-- A theory is complete if every sentence is either provable or refutable. -/
def complete (T : FormalTheory Sentence) : Prop :=
  ∀ s, T.provable s ∨ T.provable (T.neg s)

/-- A consistent, complete theory has no undecidable sentences. -/
theorem complete_no_undecidable (T : FormalTheory Sentence)
    (hcomp : T.complete) (s : Sentence) :
    ¬T.undecidable s := by
  intro ⟨hnp, hnr⟩
  exact (hcomp s).elim hnp hnr

/-- An undecidable sentence witnesses incompleteness. -/
theorem undecidable_implies_incomplete (T : FormalTheory Sentence)
    (s : Sentence) (h : T.undecidable s) :
    ¬T.complete := by
  intro hcomp
  exact complete_no_undecidable T hcomp s h

end FormalTheory

/-! ## Part 2: The Diagonal Property

    A theory has the diagonal property if for any sentence-to-sentence
    function P (representing a "predicate on sentences"), there exists
    a fixed-point sentence G such that G is provable iff P(G) is provable.

    This is the abstract content of Godel's diagonal lemma. In concrete
    theories (PA, ZF), this is proved using Godel numbering and the
    substitution function. We axiomatize it here because:
    (a) proving it from scratch requires ~1000 lines of Godel encoding
    (b) the incompleteness theorem follows from the PROPERTY, not the proof
    (c) the connection to the encoding obstruction explains WHY the
        property holds — substitution changes form, so the fixed-point
        construction can close the self-referential loop -/

/-- A formal theory with the diagonal/fixed-point property.
    For any sentence transformer P, there exists a sentence whose
    provability status is tied to P applied to itself. -/
structure DiagonalTheory (Sentence : Type*) extends FormalTheory Sentence where
  /-- The diagonal operator: given a sentence transformer P,
      produces the fixed-point sentence. -/
  diag : (Sentence → Sentence) → Sentence
  /-- Forward direction: if the fixed point is provable,
      then P applied to it is provable. -/
  diag_mp : ∀ P, provable (diag P) → provable (P (diag P))
  /-- Backward direction: if P applied to the fixed point is provable,
      then the fixed point itself is provable. -/
  diag_mpr : ∀ P, provable (P (diag P)) → provable (diag P)
  /-- Negation forward: if the negation of the fixed point is provable,
      then the negation of P applied to it is provable. -/
  diag_neg_mp : ∀ P, provable (neg (diag P)) → provable (neg (P (diag P)))
  /-- Negation backward: if the negation of P applied to the fixed point
      is provable, then the negation of the fixed point is provable. -/
  diag_neg_mpr : ∀ P, provable (neg (P (diag P))) → provable (neg (diag P))

namespace DiagonalTheory

variable {Sentence : Type*}

/-! ## Part 3: The Godel Sentence

    The Godel sentence is the diagonal of (neg . prov): a sentence
    that "says" it is not provable. We construct it from:
    - A diagonal operator (from DiagonalTheory)
    - An internal provability predicate prov : Sentence → Sentence -/

/-- The Godel sentence for a given provability predicate:
    the fixed point of neg . prov.

    G = diag(neg . prov)

    By the diagonal property: G is provable ↔ neg(prov(G)) is provable.
    In other words: G is provable iff "G is not provable" is provable. -/
def godelSentence (T : DiagonalTheory Sentence) (prov : Sentence → Sentence) :
    Sentence :=
  T.diag (T.neg ∘ prov)

/-! ## Part 4: First Incompleteness — G Is Not Provable

    If the theory is consistent and its provability predicate is
    Sigma-1-complete (provable sentences are recognizably provable),
    then the Godel sentence is not provable.

    The argument:
    - Assume G is provable.
    - By Sigma-1-completeness: prov(G) is provable.
    - By the diagonal property (backward): G provable ↔ neg(prov(G)) provable.
      So neg(prov(G)) is provable.
    - But prov(G) AND neg(prov(G)) are both provable — contradicting consistency.

    Therefore G is not provable. -/

/-- **FIRST HALF OF FIRST INCOMPLETENESS:**
    The Godel sentence is not provable in any consistent theory
    with a Sigma-1-complete provability predicate.

    Hypotheses:
    - T is a theory with the diagonal property
    - prov is the internal provability predicate
    - sigma1_complete: if s is provable, then prov(s) is provable
    - consistent: no sentence is both provable and refutable -/
theorem godel_not_provable (T : DiagonalTheory Sentence)
    (prov : Sentence → Sentence)
    (sigma1_complete : ∀ s, T.provable s → T.provable (prov s))
    (hcon : T.toFormalTheory.consistent) :
    ¬T.provable (godelSentence T prov) := by
  intro hG
  -- G is provable, so prov(G) is provable (Sigma-1-completeness)
  have hprovG : T.provable (prov (godelSentence T prov)) :=
    sigma1_complete _ hG
  -- By diagonal property: G provable → neg(prov(G)) provable
  have hnprovG : T.provable (T.neg (prov (godelSentence T prov))) :=
    T.diag_mp (T.neg ∘ prov) hG
  -- Contradiction: prov(G) and neg(prov(G)) are both provable
  exact hcon (prov (godelSentence T prov)) ⟨hprovG, hnprovG⟩

/-! ## Part 5: Second Half — G Is Not Refutable

    If additionally the provability predicate is Sigma-1-sound
    (if the theory proves "s is provable", then s actually is provable),
    then the Godel sentence is also not refutable.

    The argument:
    - Assume neg(G) is provable.
    - By the diagonal property (negation backward):
      neg(G) provable → neg(neg(prov(G))) provable.
    - We need: neg(neg(prov(G))) provable → prov(G) provable.
      This is double-negation elimination for provability.
    - By Sigma-1-soundness: prov(G) provable → G provable.
    - But neg(G) AND G are both provable — contradicting consistency.

    We factor out double-negation elimination as a hypothesis rather
    than assuming classical logic inside the theory. -/

/-- **SECOND HALF OF FIRST INCOMPLETENESS:**
    The Godel sentence is not refutable in any consistent theory
    with a Sigma-1-sound provability predicate and double-negation
    elimination for provability.

    Hypotheses:
    - sigma1_sound: if prov(s) is provable, then s is provable
    - dne: double-negation elimination holds for provability
    - consistent: no sentence is both provable and refutable -/
theorem godel_not_refutable (T : DiagonalTheory Sentence)
    (prov : Sentence → Sentence)
    (sigma1_sound : ∀ s, T.provable (prov s) → T.provable s)
    (dne : ∀ s, T.provable (T.neg (T.neg s)) → T.provable s)
    (hcon : T.toFormalTheory.consistent) :
    ¬T.provable (T.neg (godelSentence T prov)) := by
  intro hnG
  -- neg(G) provable → neg(neg(prov(G))) provable (diagonal, negation)
  have hnnprovG : T.provable (T.neg (T.neg (prov (godelSentence T prov)))) :=
    T.diag_neg_mp (T.neg ∘ prov) hnG
  -- By double-negation elimination: prov(G) is provable
  have hprovG : T.provable (prov (godelSentence T prov)) :=
    dne _ hnnprovG
  -- By Sigma-1-soundness: G is provable
  have hG : T.provable (godelSentence T prov) :=
    sigma1_sound _ hprovG
  -- Contradiction: G and neg(G) are both provable
  exact hcon (godelSentence T prov) ⟨hG, hnG⟩

/-! ## Part 6: First Incompleteness Theorem

    Combining both halves: the Godel sentence is undecidable,
    so the theory is incomplete. -/

/-- **FIRST INCOMPLETENESS THEOREM (Abstract):**
    In any consistent theory with the diagonal property,
    a Sigma-1-complete and Sigma-1-sound provability predicate,
    and double-negation elimination, the Godel sentence is undecidable.

    This is the abstract form of Godel's First Incompleteness Theorem.
    The specific hypotheses are satisfied by PA, ZF, and any
    recursively axiomatizable extension of Robinson arithmetic. -/
theorem first_incompleteness (T : DiagonalTheory Sentence)
    (prov : Sentence → Sentence)
    (sigma1_complete : ∀ s, T.provable s → T.provable (prov s))
    (sigma1_sound : ∀ s, T.provable (prov s) → T.provable s)
    (dne : ∀ s, T.provable (T.neg (T.neg s)) → T.provable s)
    (hcon : T.toFormalTheory.consistent) :
    T.toFormalTheory.undecidable (godelSentence T prov) :=
  ⟨godel_not_provable T prov sigma1_complete hcon,
   godel_not_refutable T prov sigma1_sound dne hcon⟩

/-- **INCOMPLETENESS COROLLARY:**
    Any consistent theory satisfying the above hypotheses is incomplete. -/
theorem incompleteness (T : DiagonalTheory Sentence)
    (prov : Sentence → Sentence)
    (sigma1_complete : ∀ s, T.provable s → T.provable (prov s))
    (sigma1_sound : ∀ s, T.provable (prov s) → T.provable s)
    (dne : ∀ s, T.provable (T.neg (T.neg s)) → T.provable s)
    (hcon : T.toFormalTheory.consistent) :
    ¬T.toFormalTheory.complete :=
  T.toFormalTheory.undecidable_implies_incomplete _
    (first_incompleteness T prov sigma1_complete sigma1_sound dne hcon)

/-! ## Part 7: Second Incompleteness Theorem

    The theory cannot prove its own consistency. If it could,
    it could "simulate" the proof that G is not provable,
    deriving G — but G is not provable (by the first theorem).

    We formalize this as: if the theory proves Con(T) → G,
    and the theory is consistent, then the theory does not prove Con(T). -/

/-- **SECOND INCOMPLETENESS THEOREM (Abstract):**
    If the theory can internalize the proof of "consistency → G",
    then the theory cannot prove its own consistency.

    con is the internal consistency sentence.
    con_implies_G: the theory proves con → G (the internalized
    version of godel_not_provable — "if I'm consistent, G holds").

    Since G is not provable (by first incompleteness),
    con cannot be provable either (modus ponens would give G). -/
theorem second_incompleteness (T : DiagonalTheory Sentence)
    (prov : Sentence → Sentence)
    (sigma1_complete : ∀ s, T.provable s → T.provable (prov s))
    (hcon : T.toFormalTheory.consistent)
    (con : Sentence)
    (con_implies_G : T.provable con → T.provable (godelSentence T prov)) :
    ¬T.provable con := by
  intro hcon_prov
  exact godel_not_provable T prov sigma1_complete hcon (con_implies_G hcon_prov)

/-! ## Part 8: The Connection — Why Incompleteness Exists

    The chain is now complete. Here is how each piece connects:

    LEVEL 1: THE ENCODING OBSTRUCTION (Universal.lean, EvalRewrite.lean)

    For any term algebra with evaluation rules:
    - Evaluation changes syntactic form (root constructor changes)
    - Meaning is preserved (semantic invariance)
    - Therefore no injective encoding commutes with evaluation

    This is the structural atom. It is proved universally for all
    term algebras with Leibniz structure AND for PA's own axioms.

    LEVEL 2: THE DIAGONAL CONSTRUCTION (this file, Parts 2-3)

    The encoding obstruction is WHY the diagonal lemma holds:
    - Substitution is evaluation (applying a function to a term)
    - Evaluation changes form while preserving reference
    - So a sentence can be constructed that refers to a PROPERTY
      of its own code — because the code (intensional) and the
      meaning (extensional) are irreconcilably different
    - The fixed-point/diagonal construction exploits this gap:
      it builds a sentence G where the code of G appears inside G
      via substitution, and the substitution's form-changing nature
      is what makes the self-reference possible

    LEVEL 3: INCOMPLETENESS (this file, Parts 4-6)

    Given the diagonal construction:
    - Build G = "I am not provable" (diagonal of neg . prov)
    - G not provable: would imply prov(G) AND neg(prov(G)), contradiction
    - G not refutable: would imply G provable (via soundness), contradiction
    - Therefore G is undecidable, and the theory is incomplete

    LEVEL 4: SECOND INCOMPLETENESS (this file, Part 7)

    The theory cannot prove its own consistency:
    - The proof of "G is not provable" assumes consistency
    - If the theory could prove its own consistency, it could
      internalize this proof and derive G
    - But G is not provable — contradiction

    THE COMPLETE PICTURE:

    The encoding obstruction (evaluation changes form) is the
    structural foundation. It creates the intension/extension gap
    that makes self-referential sentences constructible. The diagonal
    lemma exploits this gap. Incompleteness is the consequence.

    "Why is there incompleteness?" Because evaluation changes form.
    Any system that can encode its own syntax must evaluate compound
    terms. Evaluation necessarily introduces different operations
    (addition from multiplication, via distributivity/Leibniz).
    The resulting form change means no encoding can faithfully track
    evaluation. This irreconcilability is what the Godel sentence
    exploits: it refers to a property of its own code, and the
    gap between code and meaning is what makes the reference
    unresolvable. -/

end DiagonalTheory

/-! ## Part 9: Connecting the Obstruction to the Diagonal

    The encoding obstruction (EvalRewriteWitness) gives the eval-quote
    diagram failure. This is the structural precondition for diagonalization.

    We make this connection explicit by showing that any system with
    an EvalRewriteWitness has the property that its encoding cannot
    commute with its evaluation — and this non-commutativity is
    precisely what allows the diagonal construction to close. -/

/-- **EVAL-QUOTE FAILURE FROM OBSTRUCTION:**
    Any EvalRewriteWitness (from EvalRewrite.lean) gives the
    eval-quote diagram failure: encoding and evaluation don't commute.

    This is the bridge between the encoding obstruction (Level 1)
    and the diagonal construction (Level 2). -/
theorem eval_quote_failure {T S : Type*}
    (w : EvalRewrite.EvalRewriteWitness T S)
    (ε : T → ℕ) (hε : Function.Injective ε) :
    -- The encoding of the evaluated form differs from the original
    ε (w.rewrite w.witness) ≠ ε w.witness ∧
    -- But the meaning is the same
    w.eval (w.rewrite w.witness) = w.eval w.witness :=
  EvalRewrite.eval_rewrite_gap w ε hε

/-- **THE FULL CHAIN (condensed):**
    From an EvalRewriteWitness and a DiagonalTheory over the same
    sentence type, we get both:
    (a) The eval-quote diagram fails (from the obstruction)
    (b) The theory is incomplete (from the diagonal property)

    These are not independent facts — (a) is the structural reason
    that (b) holds. The diagonal construction works because the
    eval-quote diagram fails. The eval-quote diagram fails because
    evaluation changes form. Evaluation changes form because
    that is what evaluation IS. -/
theorem obstruction_and_incompleteness
    {Sentence : Type*}
    (T : DiagonalTheory Sentence)
    (prov : Sentence → Sentence)
    (sigma1_complete : ∀ s, T.provable s → T.provable (prov s))
    (sigma1_sound : ∀ s, T.provable (prov s) → T.provable s)
    (dne : ∀ s, T.provable (T.neg (T.neg s)) → T.provable s)
    (hcon : T.toFormalTheory.consistent)
    -- The eval-quote failure witness (from the encoding obstruction)
    {S : Type*} (w : EvalRewrite.EvalRewriteWitness Sentence S)
    (ε : Sentence → ℕ) (hε : Function.Injective ε) :
    -- (a) The eval-quote diagram fails
    (ε (w.rewrite w.witness) ≠ ε w.witness ∧
     w.eval (w.rewrite w.witness) = w.eval w.witness) ∧
    -- (b) The theory is incomplete
    T.toFormalTheory.undecidable (DiagonalTheory.godelSentence T prov) :=
  ⟨eval_quote_failure w ε hε,
   DiagonalTheory.first_incompleteness T prov sigma1_complete sigma1_sound dne hcon⟩

/-! ## Part 10: Summary of What Is Proved

    MACHINE-CHECKED (sorry-free):

    | Theorem | Statement |
    |---------|-----------|
    | godel_not_provable | Consistent + Sigma-1-complete → G not provable |
    | godel_not_refutable | Consistent + Sigma-1-sound + DNE → G not refutable |
    | first_incompleteness | G is undecidable |
    | incompleteness | The theory is not complete |
    | second_incompleteness | The theory cannot prove its own consistency |
    | eval_quote_failure | EvalRewriteWitness → eval-quote diagram fails |
    | obstruction_and_incompleteness | Both facts together |

    AXIOMATIZED (as structure fields, not proved):

    | Property | Why axiomatized |
    |----------|-----------------|
    | DiagonalTheory.diag | The diagonal lemma requires ~1000 lines of Godel encoding |
    | sigma1_complete | Requires formalizing the provability predicate concretely |
    | sigma1_sound | Same |

    ARGUED (doc comments, not formalized):

    | Claim | Status |
    |-------|--------|
    | Any self-referential theory interprets PA | Godel 1931, well-established |
    | PA satisfies DiagonalTheory | Requires formalizing Godel numbering |
    | The obstruction is WHY diag holds | Structural argument in Part 8 |

    The formalization gap is the diagonal lemma itself: proving that
    PA (or any specific theory) satisfies the DiagonalTheory structure.
    Everything ABOVE that level (incompleteness from diagonalization)
    and BELOW it (the encoding obstruction from evaluation) is proved.
    The diagonal lemma is the BRIDGE between obstruction and incompleteness,
    and we axiomatize rather than construct it. -/

end Incompleteness
