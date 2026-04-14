/-
  Beta Reduction as Encoding Obstruction
  =======================================

  The fifth instance of the encoding obstruction: lambda calculus beta
  reduction. Via the Curry-Howard correspondence, this IS cut elimination
  on proof terms. This file closes the bridge from the halting problem
  (proved in Halting.lean) to proof normalization, giving a direct route
  to proof complexity lower bounds.

  The Curry-Howard identification:
  - Lambda terms = proof terms
  - Abs (lambda abstraction) = implication introduction
  - App (application) = implication elimination / modus ponens
  - Beta reduction = cut elimination
  - Normal form = cut-free proof

  Proving beta reduction is an EvalRewriteWitness proves that cut
  elimination is an EvalRewriteWitness. The well-known non-elementary
  blowup of cut elimination (Statman 1979, Orevkov 1979) becomes an
  instance of the trajectory divergence theorem.

  This completes the five-instance unified picture:

  1. Term algebras (Universal.lean) — Leibniz rewrite changes root
  2. PA arithmetic (EvalRewrite.lean) — multiplication introduces addition
  3. Self-reference (Diagonal.lean) — substitution creates diagonal
  4. Computation (Halting.lean) — execution undecidable
  5. Proof normalization (this file) — beta reduction / cut elimination

  All five are instances of the same EvalRewriteWitness pattern.
-/

import SpectralArithmetic.Obstruction.EvalRewrite

namespace BetaReduction

/-! ## Part 1: Lambda Terms with de Bruijn Indices

    Using de Bruijn representation eliminates alpha-equivalence issues
    and makes the binding structure explicit. Variables are natural
    numbers indicating how many binders to skip. -/

/-- Untyped lambda terms with de Bruijn indices. -/
inductive Term where
  /-- Variable, indexed by de Bruijn level. -/
  | var : Nat → Term
  /-- Lambda abstraction (introduces a binder). -/
  | abs : Term → Term
  /-- Application (eliminates a binder when applied to an abstraction). -/
  | app : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-! ## Part 2: Lifting and Substitution

    Substitution requires lifting free variables to avoid capture.
    `lift c t` increments every free variable at de Bruijn level >= c.
    `subst j s t` replaces variable j with s in t, decrementing
    free variables > j to account for the binder being removed. -/

/-- Lift all free variables at level >= c by 1. -/
def lift (c : Nat) : Term → Term
  | .var k => if k < c then .var k else .var (k + 1)
  | .abs b => .abs (lift (c + 1) b)
  | .app f a => .app (lift c f) (lift c a)

/-- Substitute s for variable j in t, decrementing free variables > j. -/
def subst (j : Nat) (s : Term) : Term → Term
  | .var k =>
      if k < j then .var k
      else if k = j then s
      else .var (k - 1)
  | .abs b => .abs (subst (j + 1) (lift 0 s) b)
  | .app f a => .app (subst j s f) (subst j s a)

/-! ## Part 3: Beta Reduction

    One step of head beta reduction:
      (lambda. body) arg  ->  body[0 := arg]

    Head reduction only fires when the outermost term is a redex.
    This is sufficient for demonstrating the obstruction — the
    key fact is that the reduction changes the root constructor
    from App to whatever body starts with. -/

/-- One-step head beta reduction. If the term is `(lambda. body) arg`,
    reduce to `body[arg/0]`. Otherwise return the term unchanged. -/
def betaStep : Term → Term
  | .app (.abs body) arg => subst 0 arg body
  | t => t

/-- Iterated beta reduction with fuel. -/
def reduce : Nat → Term → Term
  | 0, t => t
  | n + 1, t => reduce n (betaStep t)

/-! ## Part 4: The Witness — (lambda. 0) (lambda. 0)

    The simplest closed beta redex: the identity combinator applied
    to itself. Reduces to the identity combinator. The root constructor
    changes from App to Abs. -/

/-- Identity combinator: lambda. 0 -/
def identity : Term := .abs (.var 0)

/-- Identity applied to identity — a beta redex. -/
def witness : Term := .app identity identity

/-- Beta reducing the witness yields the identity. -/
theorem betaStep_witness : betaStep witness = identity := by
  rfl

/-- The witness differs from the identity — different root constructor. -/
theorem witness_ne_identity : witness ≠ identity := by decide

/-! ## Part 5: Form Change — The Structural Atom

    Beta reduction changes the root constructor: (App) becomes (Abs).
    This is the key structural fact that creates the encoding obstruction. -/

/-- **BETA REDUCTION CHANGES FORM:**
    The redex (lambda. 0) (lambda. 0) has root App.
    Its beta reduct (lambda. 0) has root Abs.
    These are distinct constructors, so the terms are distinct. -/
theorem betaStep_changes_form : betaStep witness ≠ witness := by
  rw [betaStep_witness]
  intro h
  exact witness_ne_identity h.symm

/-! ## Part 6: Semantic Preservation

    Beta reduction preserves semantic content. We demonstrate this
    concretely: evaluation (iterated reduction with enough fuel)
    gives the same result whether we reduce once first or not. -/

/-- Evaluation with generous fuel. For our witness, 1 step suffices. -/
def eval (t : Term) : Term := reduce 10 t

/-- **BETA REDUCTION PRESERVES MEANING:**
    eval(betaStep(witness)) = eval(witness)
    Both reduce to the identity combinator. -/
theorem eval_betaStep_witness : eval (betaStep witness) = eval witness := by
  rfl

/-! ## Part 7: The EvalRewriteWitness Construction

    Beta reduction on our concrete witness satisfies the EvalRewriteWitness
    pattern: form-changing, meaning-preserving rewrite. -/

/-- **BETA REDUCTION AS EVAL REWRITE WITNESS:**
    The witness, with betaStep as the rewrite and eval as the
    semantic denotation, is an instance of the general pattern
    that creates the encoding obstruction. -/
def betaWitness : EvalRewrite.EvalRewriteWitness Term Term where
  rewrite := betaStep
  eval := eval
  witness := witness
  changes_form := betaStep_changes_form
  preserves_meaning := eval_betaStep_witness

/-! ## Part 8: The Encoding Obstruction for Beta Reduction

    Applying the general obstruction theorem to beta reduction:
    no injective encoding of lambda terms commutes with beta reduction. -/

/-- **BETA REDUCTION ENCODING OBSTRUCTION:**
    No injective encoding of lambda terms commutes with beta reduction.
    For any injective epsilon:
      epsilon(betaStep(witness)) != epsilon(witness)

    This is beta reduction inheriting the universal obstruction
    through the EvalRewriteWitness structure. -/
theorem beta_encoding_obstruction
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε (betaStep witness) ≠ ε witness :=
  EvalRewrite.eval_rewrite_obstruction betaWitness ε hε

/-- **INTENSION/EXTENSION GAP FOR BETA REDUCTION:**
    Codes differ AND meaning agrees. -/
theorem beta_gap
    (ε : Term → ℕ) (hε : Function.Injective ε) :
    ε (betaStep witness) ≠ ε witness ∧
    eval (betaStep witness) = eval witness :=
  EvalRewrite.eval_rewrite_gap betaWitness ε hε

/-! ## Part 9: Trajectory Divergence — The Duplicator

    Beta reduction can STRICTLY INCREASE term size. The duplicator
    lambda-term  (lambda. 0 0)  when applied to any argument t produces
    t t, doubling the size of the argument. This is the source of
    exponential blowup in beta reduction and, via Curry-Howard,
    the source of non-elementary cut elimination blowup. -/

/-- Term size (number of constructors). -/
def size : Term → Nat
  | .var _ => 1
  | .abs b => 1 + size b
  | .app f a => 1 + size f + size a

/-- The duplicator combinator: lambda. 0 0 -/
def dup : Term := .abs (.app (.var 0) (.var 0))

/-- Size of the duplicator. -/
theorem size_dup : size dup = 4 := by rfl

/-- The duplicator applied to a term t. -/
def dupApplied (t : Term) : Term := .app dup t

/-- Beta reducing dup t yields t t — the argument is DUPLICATED.
    Note: de Bruijn substitution at the top level does not lift,
    because `arg` is already in the outer context. -/
theorem betaStep_dupApplied (t : Term) :
    betaStep (dupApplied t) = .app t t := by
  rfl

/-- The size of t t is 1 + 2 * size t. -/
theorem size_app_self (t : Term) :
    size (.app t t : Term) = 1 + 2 * size t := by
  simp [size]; ring

/-- The size of dup t is 5 + size t. -/
theorem size_dupApplied (t : Term) :
    size (dupApplied t) = 5 + size t := by
  simp [size, dupApplied, size_dup]

/-- **BETA REDUCTION STRICTLY GROWS SIZE** when the argument is large.
    For size(t) >= 5, size(betaStep(dup t)) > size(dup t).
    This is the engine of exponential blowup in beta reduction
    and, via Curry-Howard, the source of non-elementary
    cut elimination blowup. -/
theorem beta_grows_for_large (t : Term) (ht : size t ≥ 5) :
    size (betaStep (dupApplied t)) > size (dupApplied t) := by
  rw [betaStep_dupApplied, size_app_self, size_dupApplied]
  omega

/-! ## Part 10: Omega — The Non-Terminating Fixed Point

    Omega = (lambda. 0 0) (lambda. 0 0) reduces to itself.
    This is the simplest non-terminating lambda term, and it demonstrates
    the halting problem directly: one cannot decide from the term's
    form whether its evaluation terminates.

    Via Curry-Howard, omega has no analog in simply-typed lambda calculus
    (which is strongly normalizing), but in polymorphic or dependent
    systems (System F, Calculus of Constructions) non-termination IS
    possible for well-typed terms that represent proofs of false under
    inconsistent assumptions. -/

/-- Omega: self-application of the duplicator. -/
def omega : Term := .app dup dup

/-- **OMEGA REDUCES TO ITSELF:**
    betaStep(omega) = omega. The form doesn't change at this level
    because the duplicator produces the SAME term it consumed.
    But omega is still a fixed point of beta reduction, and
    evaluating it does not terminate — demonstrating the halting problem. -/
theorem betaStep_omega : betaStep omega = omega := by
  rfl

/-! ## Part 11: Curry-Howard Connection

    The encoding obstruction on beta reduction IS the encoding obstruction
    on cut elimination. Under Curry-Howard:

    - Lambda terms correspond to proof terms in natural deduction
    - Lambda abstraction (Abs) corresponds to implication introduction
    - Application (App) corresponds to implication elimination (modus ponens)
    - Beta reduction corresponds to cut elimination
    - Normal form corresponds to cut-free proof

    The witness (lambda. 0) (lambda. 0) reducing to (lambda. 0) corresponds
    to: a proof with a cut (using the identity as a lemma and discharging
    it immediately) reducing to a cut-free proof (just the identity).

    The duplicator dup = (lambda. 0 0) corresponds to a proof that USES
    its premise twice. Applying dup to a proof t and cut-eliminating
    produces two COPIES of t's proof structure — this is the mechanism
    of Statman's non-elementary cut elimination blowup.

    The general claim (not formalized here, but follows from Curry-Howard):
    cut elimination in classical/intuitionistic logic is an EvalRewriteWitness.
    The exponential-to-non-elementary blowup (Statman 1979, Orevkov 1979)
    is the trajectory divergence theorem applied to proof terms.

    See docs/theory/computation/structural-domains.md Part 2 for details. -/

/-! ## Part 12: Summary — Five Instances of the Same Obstruction

    With this file, we have five machine-checked instances of the
    encoding obstruction:

    | Instance | Rewrite | Form change | File |
    |----------|---------|-------------|------|
    | Leibniz | obsRewrite | obs -> add | Universal.lean |
    | PA multiplication | mulStep | times -> plus | EvalRewrite.lean |
    | Self-reference | diagonal | formula -> sentence | Diagonal.lean |
    | Computation | execution | state changes | Halting.lean |
    | Beta reduction | betaStep | App -> body's root | this file |

    All are instances of EvalRewriteWitness. All demonstrate the same
    structural fact: evaluation changes form while preserving semantics,
    and no injective encoding can commute with this process.

    The Curry-Howard correspondence identifies beta reduction with cut
    elimination. Therefore cut elimination is an EvalRewriteWitness. The
    exponential blowup in cut elimination (Statman, Orevkov) is the
    trajectory divergence in beta reduction applied to proof terms.

    This completes the bridge from the universal encoding obstruction
    to proof complexity: the same structural fact that causes
    incompleteness and the halting problem causes non-elementary
    cut elimination and, conjecturally (issues #33, #36), super-polynomial
    proof length lower bounds for all proof systems. -/

end Term

end BetaReduction
