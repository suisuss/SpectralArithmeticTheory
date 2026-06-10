/-
  Theory Interfaces
  =================

  The abstract formal-theory structures, extracted from
  Incompleteness.lean into a file with NO imports.

  Why the extraction: instantiating these interfaces from the
  FormalizedFormalLogic Foundation library (FoundationBridge.lean)
  requires loading Foundation's oleans, which carry auto-generated
  equation lemmas for Mathlib declarations that also occur in
  Mathlib oleans pulled by `import Mathlib.Tactic` (e.g.
  `Matrix.map.eq_1` from `Mathlib.LinearAlgebra.Matrix.
  InvariantBasisNumber`) — loading both closures in one environment
  is a duplicate-declaration error. Keeping the interfaces
  import-free lets the bridge live on the Foundation side of that
  boundary while everything else keeps `Mathlib.Tactic`.

  Everything here is definitional or proved with core tactics.
  Incompleteness.lean re-exports these names by importing this file;
  no downstream reference changes.
-/

namespace Incompleteness

universe u

/-- A formal theory over a type of sentences.
    - `provable`: the set of theorems (sentences derivable from axioms)
    - `neg`: syntactic negation -/
structure FormalTheory (Sentence : Type u) where
  provable : Sentence → Prop
  neg : Sentence → Sentence

namespace FormalTheory

variable {Sentence : Type u}

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
  intro h
  exact (hcomp s).elim h.1 h.2

/-- An undecidable sentence witnesses incompleteness. -/
theorem undecidable_implies_incomplete (T : FormalTheory Sentence)
    (s : Sentence) (h : T.undecidable s) :
    ¬T.complete := by
  intro hcomp
  exact complete_no_undecidable T hcomp s h

end FormalTheory

/-- A formal theory with the diagonal/fixed-point property.
    For any sentence transformer P, there exists a sentence whose
    provability status is tied to P applied to itself.

    WARNING (2026-06-10, FoundationBridge.lean): this structure is
    DEGENERATE. Quantifying `diag` over arbitrary transformers
    P : Sentence → Sentence — rather than formula-definable ones —
    is satisfiable only by trivial theories (everything provable or
    nothing provable); see `FoundationBridge.diagonalTheory_trivial`.
    Real theories satisfy the diagonal lemma only for formulas;
    `Diagonal.GodelSystem` is the correct abstraction. Kept for the
    record and for the degeneracy theorem itself. -/
structure DiagonalTheory (Sentence : Type u) extends FormalTheory Sentence where
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

end Incompleteness
