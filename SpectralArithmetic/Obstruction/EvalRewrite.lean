/-
  The Evaluation Rewrite Obstruction
  ==================================

  PA's own evaluation rules create the encoding obstruction — no Leibniz
  rule or derivation operator needs to be imposed from outside.

  PA defines multiplication recursively:
    a × 0     = 0
    a × S(b)  = a × b + a

  The second rule is an EVALUATION REWRITE: it reduces a ×-rooted term
  to a +-rooted term. The root constructor changes from times to plus.
  This is the same structural pattern as the Leibniz rewrite (obs → add),
  but it comes from PA's own axioms, not from an external observation operator.

  The argument completes the universality chain:

  1. Any self-referential theory interprets PA [Godel / the video]
  2. PA's evaluation rules change root constructors [this file, proved]
  3. Root constructor change + injective encoding = obstruction [Universal.lean]
  4. Therefore: ANY self-referential theory hits the encoding obstruction

  The general principle (also proved here): ANY rewrite on ANY type
  that produces a syntactically distinct result creates the obstruction.
  Leibniz and PA-evaluation are both instances. The obstruction is not
  about derivations — it is about EVALUATION ITSELF.
-/

import Mathlib.Tactic

namespace EvalRewrite

/-! ## Part 1: The General Obstruction Principle

    The foundational theorem: for ANY type, ANY rewrite that changes
    a term's identity, ANY injective encoding must assign different codes.

    This is logically trivial (it follows from the definition of injectivity).
    Its significance is not in the proof but in the UNIVERSALITY: it
    applies to every type, every rewrite, every encoding. The non-trivial
    content is showing that specific rewrites (Leibniz, PA evaluation)
    satisfy the premise — and that every self-referential theory must
    have such a rewrite. -/

/-- **THE GENERAL OBSTRUCTION PRINCIPLE:**
    For ANY type T, ANY rewrite R, ANY term t with R(t) ≠ t,
    and ANY injective ε: ε(R(t)) ≠ ε(t).

    This is the atom from which all encoding obstructions are built. -/
theorem general_obstruction {T : Type*}
    {R : T → T} {t : T} (hne : R t ≠ t)
    {ε : T → ℕ} (hε : Function.Injective ε) :
    ε (R t) ≠ ε t := by
  intro h; exact absurd (hε h) hne

/-- The general obstruction with semantic invariance: the rewrite
    changes codes but preserves meaning. -/
theorem general_intension_extension_gap {T S : Type*}
    {R : T → T} {t : T} (hne : R t ≠ t)
    {eval : T → S} (hsem : eval (R t) = eval t)
    {ε : T → ℕ} (hε : Function.Injective ε) :
    ε (R t) ≠ ε t ∧ eval (R t) = eval t :=
  ⟨general_obstruction hne hε, hsem⟩

/-! ## Part 2: PA's Term Algebra

    PA's language: 0, S, +, ×. No observation operator, no Leibniz rule.
    Just the standard first-order language of arithmetic. -/

/-- Terms of Peano Arithmetic. -/
inductive PATerm : Type where
  | zero : PATerm
  | succ : PATerm → PATerm
  | plus : PATerm → PATerm → PATerm
  | times : PATerm → PATerm → PATerm
  deriving DecidableEq, Repr

namespace PATerm

/-! ## Part 3: PA's Evaluation Rewrites

    PA's recursive definitions of + and × ARE rewrite rules.
    These are not imposed from outside — they are PA's own axioms,
    read as left-to-right reductions. -/

/-- PA's multiplication evaluation step:
    a × S(b) → (a × b) + a

    This is PA's axiom "a × S(b) = a × b + a" read as a rewrite rule.
    It maps a times-rooted term to a plus-rooted term. -/
def mulStep : PATerm → PATerm
  | .times a (.succ b) => .plus (.times a b) a
  | t => t

/-- PA's addition evaluation step:
    a + S(b) → S(a + b)

    This is PA's axiom "a + S(b) = S(a + b)" read as a rewrite rule.
    It maps a plus-rooted term to a succ-rooted term. -/
def addStep : PATerm → PATerm
  | .plus a (.succ b) => .succ (.plus a b)
  | t => t

/-! ## Part 4: Root Constructor Changes in PA

    The KEY structural fact: PA's evaluation rules change root
    constructors. This is not a design choice — it is what evaluation IS.

    - mulStep: times → plus (multiplication introduces addition)
    - addStep: plus → succ  (addition introduces successor)

    Compare to the Leibniz rewrite: obs → add.
    The pattern is identical: evaluation of compound terms produces
    terms with a DIFFERENT top-level structure. -/

/-- **MULTIPLICATION CHANGES ROOT (times → plus):**
    For ALL PA terms a, b: mulStep(a × S(b)) ≠ a × S(b).

    The multiplication evaluation rule maps a times-rooted term
    to a plus-rooted term. These are distinct constructors. -/
theorem mulStep_changes_form (a b : PATerm) :
    mulStep (.times a (.succ b)) ≠ .times a (.succ b) := by
  simp [mulStep]

/-- **ADDITION CHANGES ROOT (plus → succ):**
    For ALL PA terms a, b: addStep(a + S(b)) ≠ a + S(b).

    The addition evaluation rule maps a plus-rooted term
    to a succ-rooted term. These are distinct constructors. -/
theorem addStep_changes_form (a b : PATerm) :
    addStep (.plus a (.succ b)) ≠ .plus a (.succ b) := by
  simp [addStep]

/-! ## Part 5: The Encoding Obstruction for PA

    PA's own evaluation rules create the encoding obstruction.
    No Leibniz rule, no observation operator, no eigenvalues.
    Just PA being PA. -/

/-- **PA MULTIPLICATION OBSTRUCTION:**
    No injective encoding of PA terms commutes with the
    multiplication evaluation step.

    For ALL injective ε and ALL terms a, b:
    ε(mulStep(a × S(b))) ≠ ε(a × S(b))

    This is the encoding obstruction arising from PA's OWN axioms. -/
theorem pa_mul_obstruction
    (ε : PATerm → ℕ) (hε : Function.Injective ε) (a b : PATerm) :
    ε (mulStep (.times a (.succ b))) ≠ ε (.times a (.succ b)) :=
  general_obstruction (mulStep_changes_form a b) hε

/-- **PA ADDITION OBSTRUCTION:**
    No injective encoding of PA terms commutes with the
    addition evaluation step.

    For ALL injective ε and ALL terms a, b:
    ε(addStep(a + S(b))) ≠ ε(a + S(b)) -/
theorem pa_add_obstruction
    (ε : PATerm → ℕ) (hε : Function.Injective ε) (a b : PATerm) :
    ε (addStep (.plus a (.succ b))) ≠ ε (.plus a (.succ b)) :=
  general_obstruction (addStep_changes_form a b) hε

/-! ## Part 6: Semantic Invariance — PA's Standard Model

    The evaluation rewrites preserve meaning in the standard model ℕ.
    This is the other half of the intension/extension gap:
    the codes differ, but the denotations agree. -/

/-- Standard evaluation of PA terms in ℕ. -/
def evalN : PATerm → ℕ
  | .zero => 0
  | .succ n => (evalN n) + 1
  | .plus a b => evalN a + evalN b
  | .times a b => evalN a * evalN b

/-- **MULTIPLICATION SEMANTIC INVARIANCE:**
    evalN(mulStep(a × S(b))) = evalN(a × S(b))

    PA's multiplication rule preserves meaning in the standard model.
    a × S(b) and (a × b) + a denote the same natural number. -/
theorem mulStep_preserves_semantics (a b : PATerm) :
    evalN (mulStep (.times a (.succ b))) = evalN (.times a (.succ b)) := by
  simp [mulStep, evalN]
  ring

/-- **ADDITION SEMANTIC INVARIANCE:**
    evalN(addStep(a + S(b))) = evalN(a + S(b))

    PA's addition rule preserves meaning in the standard model.
    a + S(b) and S(a + b) denote the same natural number. -/
theorem addStep_preserves_semantics (a b : PATerm) :
    evalN (addStep (.plus a (.succ b))) = evalN (.plus a (.succ b)) := by
  simp [addStep, evalN]
  omega

/-! ## Part 7: The Full Intension/Extension Gap for PA

    Combining the obstruction with semantic invariance:
    PA's evaluation rules change codes but preserve meaning.
    This is the intension/extension gap — proved for PA's own
    axioms, without any external observation operator. -/

/-- **PA MULTIPLICATION: THE INTENSION/EXTENSION GAP**
    Codes differ AND meaning agrees. Universal over all
    injective encodings and all terms. -/
theorem pa_mul_gap
    (ε : PATerm → ℕ) (hε : Function.Injective ε) (a b : PATerm) :
    ε (mulStep (.times a (.succ b))) ≠ ε (.times a (.succ b)) ∧
    evalN (mulStep (.times a (.succ b))) = evalN (.times a (.succ b)) :=
  general_intension_extension_gap (mulStep_changes_form a b)
    (mulStep_preserves_semantics a b) hε

/-- **PA ADDITION: THE INTENSION/EXTENSION GAP** -/
theorem pa_add_gap
    (ε : PATerm → ℕ) (hε : Function.Injective ε) (a b : PATerm) :
    ε (addStep (.plus a (.succ b))) ≠ ε (.plus a (.succ b)) ∧
    evalN (addStep (.plus a (.succ b))) = evalN (.plus a (.succ b)) :=
  general_intension_extension_gap (addStep_changes_form a b)
    (addStep_preserves_semantics a b) hε

/-! ## Part 8: Term Size Growth Under PA Evaluation

    Like the Leibniz rewrite, PA's evaluation rewrites change term size.
    The multiplication step increases size (introduces +).
    This confirms the trajectory divergence pattern. -/

/-- Size of a PA term. -/
def termSize : PATerm → ℕ
  | .zero => 1
  | .succ n => 1 + termSize n
  | .plus a b => 1 + termSize a + termSize b
  | .times a b => 1 + termSize a + termSize b

/-- The multiplication step increases term size:
    |mulStep(a × S(b))| = |(a × b) + a| = 1 + (1 + |a| + |b|) + |a|
                        = 2 + 2|a| + |b|
    vs |a × S(b)| = 1 + |a| + (1 + |b|) = 2 + |a| + |b|
    Growth = |a| ≥ 1. -/
theorem mulStep_grows (a b : PATerm) :
    termSize (mulStep (.times a (.succ b))) >
    termSize (.times a (.succ b)) := by
  simp [mulStep, termSize]
  have := termSize_pos a
  omega
where
  termSize_pos : ∀ t : PATerm, termSize t ≥ 1 := by
    intro t; cases t <;> simp [termSize] <;> omega

/-! ## Part 9: The Structural Equivalence — Leibniz and PA Evaluation

    The Leibniz rewrite and PA's multiplication evaluation are both
    instances of the same abstract pattern:

    PATTERN: A rewrite R on a term algebra T such that:
    (a) R maps terms with root constructor F to terms with root constructor G
    (b) F ≠ G (distinct constructors)
    (c) eval(R(t)) = eval(t) (semantics preserved)

    For Leibniz:  F = obs,   G = add,  R = leibnizRewrite
    For PA ×:     F = times, G = plus, R = mulStep
    For PA +:     F = plus,  G = succ, R = addStep

    In each case, the obstruction follows from (a) + (b) + injectivity.
    The semantic invariance (c) confirms the gap is in the FORM, not
    the MEANING. -/

end PATerm

/-- A rewrite system on a type T: a rewrite function and a term
    on which it provably changes form and preserves semantics. -/
structure EvalRewriteWitness (T S : Type*) where
  rewrite : T → T
  eval : T → S
  witness : T
  changes_form : rewrite witness ≠ witness
  preserves_meaning : eval (rewrite witness) = eval witness

/-- Any EvalRewriteWitness creates an encoding obstruction. -/
theorem eval_rewrite_obstruction {T S : Type*}
    (w : EvalRewriteWitness T S) (ε : T → ℕ) (hε : Function.Injective ε) :
    ε (w.rewrite w.witness) ≠ ε w.witness :=
  general_obstruction w.changes_form hε

/-- Any EvalRewriteWitness exhibits the intension/extension gap. -/
theorem eval_rewrite_gap {T S : Type*}
    (w : EvalRewriteWitness T S) (ε : T → ℕ) (hε : Function.Injective ε) :
    ε (w.rewrite w.witness) ≠ ε w.witness ∧
    w.eval (w.rewrite w.witness) = w.eval w.witness :=
  ⟨eval_rewrite_obstruction w ε hε, w.preserves_meaning⟩

namespace PATerm

/-! ## Part 10: Instances — Every Self-Referential Theory Has a Witness

    We construct EvalRewriteWitness instances for PA's evaluation rules.
    Since any self-referential theory interprets PA (the video's result),
    any self-referential theory has these witnesses, and therefore
    hits the encoding obstruction. -/

/-- PA multiplication witness: a × S(b) → (a × b) + a
    changes form and preserves semantics. -/
def paMulWitness (a b : PATerm) : EvalRewriteWitness PATerm ℕ where
  rewrite := mulStep
  eval := evalN
  witness := .times a (.succ b)
  changes_form := mulStep_changes_form a b
  preserves_meaning := mulStep_preserves_semantics a b

/-- PA addition witness: a + S(b) → S(a + b)
    changes form and preserves semantics. -/
def paAddWitness (a b : PATerm) : EvalRewriteWitness PATerm ℕ where
  rewrite := addStep
  eval := evalN
  witness := .plus a (.succ b)
  changes_form := addStep_changes_form a b
  preserves_meaning := addStep_preserves_semantics a b

/-- The obstruction for PA multiplication, via the general framework. -/
theorem pa_mul_via_general (a b : PATerm)
    (ε : PATerm → ℕ) (hε : Function.Injective ε) :
    ε (mulStep (.times a (.succ b))) ≠ ε (.times a (.succ b)) :=
  eval_rewrite_obstruction (paMulWitness a b) ε hε

/-- The obstruction for PA addition, via the general framework. -/
theorem pa_add_via_general (a b : PATerm)
    (ε : PATerm → ℕ) (hε : Function.Injective ε) :
    ε (addStep (.plus a (.succ b))) ≠ ε (.plus a (.succ b)) :=
  eval_rewrite_obstruction (paAddWitness a b) ε hε

/-! ## Part 11: The Connection to Leibniz

    PA's multiplication rule:     a × S(b) = a × b + a
    Leibniz (product rule):       D(a · b) = D(a) · b + a · D(b)

    These are not the same equation. But they share the structural
    property that creates the obstruction: evaluating/differentiating
    a MULTIPLICATIVE expression produces an ADDITIVE expression.

    The Leibniz rule is what you get when D is a derivation (linear,
    satisfying the product rule). PA's multiplication rule is what you
    get when you unfold the recursive definition of × (iterated +).

    Both come from the same algebraic root: multiplication distributes
    over addition. Distributivity IS the mechanism that changes root
    constructors from × to +. The Leibniz rule is the infinitesimal
    version. PA's evaluation rule is the discrete version. They are
    two faces of the same structural fact.

    Formally: PA's rule    a × (b + 1) = a × b + a × 1 = a × b + a
    is the DISTRIBUTIVE LAW specialized to the second argument being
    a successor. The Leibniz rule D(a·b) = D(a)·b + a·D(b) is the
    distributive law for how D interacts with ×.

    The spectral framework's Leibniz axiom:
      obs(compose(a,b)) = oplus(compose(obs(a),b), compose(a,obs(b)))

    PA's multiplication axiom:
      times(a, succ(b)) = plus(times(a, b), a)

    In both: evaluation of a binary operation (compose/times) produces
    a different binary operation (oplus/plus) at the root. In both:
    the meaning is preserved. In both: the form changes. In both:
    no injective encoding can bridge the gap.

    The obstruction is not about derivations. It is not about eigenvalues.
    It is about EVALUATION. Any theory that can evaluate compound terms
    — which any self-referential theory must, to verify proofs — has
    evaluation rules that change root constructors. And that is enough. -/

/-! ## Part 12: Universality Summary

    PROVED IN THIS FILE:
    1. general_obstruction: ANY form-changing rewrite blocks injective encoding
    2. mulStep_changes_form: PA's × evaluation changes root (times → plus)
    3. addStep_changes_form: PA's + evaluation changes root (plus → succ)
    4. mulStep_preserves_semantics: PA's × rule preserves meaning in ℕ
    5. addStep_preserves_semantics: PA's + rule preserves meaning in ℕ
    6. pa_mul_gap / pa_add_gap: The full intension/extension gap for PA
    7. EvalRewriteWitness: The abstract structure capturing both patterns
    8. paMulWitness / paAddWitness: PA as instance of the general pattern

    PROVED IN Universal.lean:
    9. universal_encoding_obstruction: Leibniz changes form, for all signatures
    10. leibnizRewrite_preserves_eval: Leibniz preserves meaning, for all models
    11. intension_extension_gap: The full gap for all Leibniz algebras

    ARGUED (commentary, not formalized):
    12. Any self-referential theory interprets PA (Godel)
    13. Therefore any self-referential theory has evaluation rewrites
    14. Therefore any self-referential theory hits the obstruction
    15. The obstruction is WHY incompleteness exists: self-encoding
        requires injective naming, evaluation requires form change,
        and these cannot be reconciled -/

end PATerm

end EvalRewrite
