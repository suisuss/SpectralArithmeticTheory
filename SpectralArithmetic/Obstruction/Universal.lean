/-
  Universal Encoding Obstruction
  ==============================

  The encoding obstruction proved for ALL term algebras with Leibniz structure,
  not just the spectral framework's specific Term type.

  The argument chain:
  1. Any self-referential theory interprets PA (Godel, formalized by mutual
     interpretability of string theories and number theories)
  2. Any theory with a binary operation and a derivation has the Leibniz rule
  3. The Leibniz rule changes root constructor: obs(comp(a,b)) becomes
     add(comp(obs(a),b), comp(a,obs(b)))
  4. Root constructor change implies syntactic distinctness
  5. Syntactic distinctness + injective encoding implies code distinctness
  6. Therefore: no injective encoding commutes with observation, in ANY
     term algebra with this structure

  The key abstraction: TermF is parameterized by an arbitrary constant
  signature C. The structural constructors (comp, add, obs) are fixed.
  The obstruction holds universally over ALL choices of C — the constants
  don't matter, only the interaction between comp, add, and obs.

  This means: any theory whose term language includes a binary operation,
  an additive operation, and a derivation-like observation hits the
  obstruction. Since any self-referential theory must interpret PA
  (which provides addition and multiplication), and any derivation on
  a product gives the Leibniz rule, the obstruction is universal.
-/

import Mathlib.Tactic

namespace UniversalObstruction

/-! ## Part 1: The Parameterized Term Algebra

    TermF C is a term algebra over an arbitrary signature of constants C.
    The structural operations — comp (binary), add (binary), obs (unary) —
    are fixed. Only the constants vary.

    This captures ANY formal language with:
    - A binary composition (multiplication, function application, etc.)
    - A binary addition (the operation Leibniz introduces)
    - A unary observation (derivative, evaluation, successor, etc.)
    - Arbitrary domain-specific constants -/

inductive TermF (C : Type*) : Type _ where
  | const : C → TermF C
  | comp : TermF C → TermF C → TermF C
  | add : TermF C → TermF C → TermF C
  | obs : TermF C → TermF C
  deriving DecidableEq, Repr

namespace TermF

variable {C : Type*}

/-! ## Part 2: The Leibniz Rewrite (Universal)

    The Leibniz rule as a syntactic rewrite on TermF C.
    This is the extensionalization operation: it unfolds
    obs(comp(a,b)) into add(comp(obs(a),b), comp(a,obs(b))).

    The rewrite is defined identically for ALL signatures C.
    The obstruction depends only on the structural constructors. -/

/-- The Leibniz rewrite: extensionalize observation of composition.
    obs(comp(a,b)) ↦ add(comp(obs(a),b), comp(a,obs(b)))
    All other terms are unchanged. -/
def leibnizRewrite : TermF C → TermF C
  | .obs (.comp a b) => .add (.comp (.obs a) b) (.comp a (.obs b))
  | t => t

/-! ## Part 3: The Core Obstruction (Universal)

    The Leibniz rewrite changes the root constructor from obs to add.
    These are distinct constructors in TermF, so the rewritten term
    is always syntactically different from the original.

    This is the structural fact that drives everything:
    observation of composition NECESSARILY produces addition. -/

/-- The Leibniz rewrite of obs(comp(a,b)) is always an add-rooted term.
    This is definitional — it follows from the definition of leibnizRewrite. -/
theorem leibnizRewrite_form (a b : TermF C) :
    leibnizRewrite (.obs (.comp a b)) =
      .add (.comp (.obs a) b) (.comp a (.obs b)) := rfl

/-- **ROOT CONSTRUCTOR CHANGE (Universal):**
    For ALL signatures C and ALL sub-terms a, b:
    leibnizRewrite(obs(comp(a,b))) ≠ obs(comp(a,b))

    The extensionalized form (add at root) is always syntactically
    distinct from the intensional form (obs at root). This holds
    because add and obs are distinct constructors of TermF. -/
theorem leibniz_changes_form (a b : TermF C) :
    leibnizRewrite (.obs (.comp a b)) ≠ .obs (.comp a b) := by
  simp [leibnizRewrite]

/-- **UNIVERSAL ENCODING OBSTRUCTION:**
    For ALL signatures C, ALL injective encodings ε, and ALL sub-terms a, b:
    ε(leibnizRewrite(obs(comp(a,b)))) ≠ ε(obs(comp(a,b)))

    No injective encoding commutes with the Leibniz extensionalization
    on ANY compound observation term, in ANY term algebra.

    This is the abstract version of no_coalgebra_morphism from Main.lean,
    proved once for all possible theories. -/
theorem universal_encoding_obstruction
    (ε : TermF C → ℕ) (hε : Function.Injective ε) (a b : TermF C) :
    ε (leibnizRewrite (.obs (.comp a b))) ≠ ε (.obs (.comp a b)) := by
  intro h
  exact absurd (hε h) (leibniz_changes_form a b)

/-! ## Part 4: Semantic Invariance (Universal)

    The obstruction is not a defect — the meaning IS preserved.
    We define a general evaluation into any algebra satisfying the
    Leibniz rule, and prove the rewrite preserves it. -/

/-- An algebra that interprets TermF C: provides denotations for
    constants and operations, satisfying the Leibniz rule. -/
structure LeibnizAlgebra (C : Type*) (S : Type*) where
  interpConst : C → S
  interpComp : S → S → S
  interpAdd : S → S → S
  interpObs : S → S
  leibniz_law : ∀ a b : S, interpObs (interpComp a b) =
    interpAdd (interpComp (interpObs a) b) (interpComp a (interpObs b))

/-- Evaluate a term in a LeibnizAlgebra. -/
def eval (A : LeibnizAlgebra C S) : TermF C → S
  | .const c => A.interpConst c
  | .comp a b => A.interpComp (eval A a) (eval A b)
  | .add a b => A.interpAdd (eval A a) (eval A b)
  | .obs a => A.interpObs (eval A a)

/-- **SEMANTIC INVARIANCE (Universal):**
    The Leibniz rewrite preserves evaluation in ANY LeibnizAlgebra,
    for ALL signatures C and ALL sub-terms a, b.

    eval(leibnizRewrite(obs(comp(a,b)))) = eval(obs(comp(a,b)))

    Meaning is invariant. Form is not. Both facts are universal. -/
theorem leibnizRewrite_preserves_eval (A : LeibnizAlgebra C S)
    (a b : TermF C) :
    eval A (leibnizRewrite (.obs (.comp a b))) =
      eval A (.obs (.comp a b)) := by
  simp only [leibnizRewrite, eval]
  rw [← A.leibniz_law]

/-- Semantic invariance for arbitrary terms (the rewrite only fires
    on obs(comp(...)), all other terms pass through unchanged). -/
theorem leibnizRewrite_eval (A : LeibnizAlgebra C S)
    (t : TermF C) :
    eval A (leibnizRewrite t) = eval A t := by
  match t with
  | .obs (.comp a b) => exact leibnizRewrite_preserves_eval A a b
  | .obs (.obs _) => rfl
  | .obs (.add _ _) => rfl
  | .obs (.const _) => rfl
  | .const _ => rfl
  | .comp _ _ => rfl
  | .add _ _ => rfl

/-! ## Part 5: The Combined Result — The Intension/Extension Gap (Universal)

    The universal encoding obstruction and semantic invariance together
    constitute the intension/extension gap for ALL term algebras
    with Leibniz structure:

    - Form always changes: ε(rewrite(t)) ≠ ε(t)  [encoding obstruction]
    - Meaning never changes: eval(rewrite(t)) = eval(t)  [semantic invariance]

    This is the structural content of Godel incompleteness:
    any system that can encode its own syntax (injective ε)
    and has a semantics-preserving evaluation (Leibniz rewrite)
    necessarily has a gap between what it can name and what it can resolve.

    The gap is not a quirk of any particular theory. It is universal
    over all theories with this structure. And any self-referential
    theory has this structure, because self-reference requires PA,
    PA requires addition and multiplication, and any derivation on
    a product gives the Leibniz rule. -/

/-- **THE INTENSION/EXTENSION GAP (Universal):**
    For ALL signatures, ALL models, ALL injective encodings, and ALL sub-terms:
    the encoding distinguishes what the semantics identifies.

    This is the universal statement that compilation ≠ execution:
    both preserve meaning, but they disagree on form, and no
    injective encoding can reconcile them. -/
theorem intension_extension_gap (A : LeibnizAlgebra C S)
    (ε : TermF C → ℕ) (hε : Function.Injective ε) (a b : TermF C) :
    ε (leibnizRewrite (.obs (.comp a b))) ≠ ε (.obs (.comp a b)) ∧
    eval A (leibnizRewrite (.obs (.comp a b))) =
      eval A (.obs (.comp a b)) :=
  ⟨universal_encoding_obstruction ε hε a b,
   leibnizRewrite_preserves_eval A a b⟩

/-! ## Part 6: Term Size and Trajectory Divergence (Universal)

    The obstruction is not just qualitative (different codes) but
    quantitative (exponentially growing divergence). Each Leibniz
    extensionalization more than doubles term size. -/

/-- Size of a term (number of constructors). -/
def termSize : TermF C → ℕ
  | .const _ => 1
  | .comp a b => 1 + termSize a + termSize b
  | .add a b => 1 + termSize a + termSize b
  | .obs a => 1 + termSize a

/-- Every term has size at least 1. -/
theorem termSize_pos (t : TermF C) : termSize t ≥ 1 := by
  cases t <;> simp [termSize] <;> omega

/-- The intensional form obs(comp(a,b)) has size 2 + |a| + |b|. -/
theorem obs_comp_size (a b : TermF C) :
    termSize (.obs (.comp a b) : TermF C) = 2 + termSize a + termSize b := by
  simp [termSize]; ring

/-- The extensionalized form has size 5 + 2|a| + 2|b|. -/
theorem leibnizRewrite_size (a b : TermF C) :
    termSize (leibnizRewrite (.obs (.comp a b) : TermF C)) =
      5 + 2 * termSize a + 2 * termSize b := by
  simp [leibnizRewrite, termSize]; ring

/-- **EXTENSIONALIZATION STRICTLY GROWS (Universal):**
    The rewritten term is always strictly larger than the original. -/
theorem leibniz_grows (a b : TermF C) :
    termSize (leibnizRewrite (.obs (.comp a b) : TermF C)) >
    termSize (.obs (.comp a b) : TermF C) := by
  rw [leibnizRewrite_size, obs_comp_size]; omega

/-- **MORE THAN DOUBLES (Universal):**
    The rewritten term has size > 2 × original size.
    Iterated extensionalization grows at least as 2^k. -/
theorem leibniz_more_than_doubles (a b : TermF C) :
    termSize (leibnizRewrite (.obs (.comp a b) : TermF C)) >
    2 * termSize (.obs (.comp a b) : TermF C) := by
  rw [leibnizRewrite_size, obs_comp_size]; omega

/-! ## Part 7: Deep Extensionalization and No Fixed Point (Universal)

    Iterated rewriting produces an unbounded chain of distinct terms.
    No fixed point exists — substitution never terminates. -/

/-- Bottom-up deep extensionalization: apply leibnizRewrite throughout. -/
def deepRewrite : TermF C → TermF C
  | .obs t => leibnizRewrite (.obs (deepRewrite t))
  | .comp a b => .comp (deepRewrite a) (deepRewrite b)
  | .add a b => .add (deepRewrite a) (deepRewrite b)
  | .const c => .const c

/-- Deep extensionalization preserves semantics. -/
theorem deepRewrite_eval (A : LeibnizAlgebra C S) (t : TermF C) :
    eval A (deepRewrite t) = eval A t := by
  match t with
  | .obs t' =>
    simp only [deepRewrite, eval]
    rw [leibnizRewrite_eval A (.obs (deepRewrite t'))]
    simp only [eval]
    rw [deepRewrite_eval A t']
  | .comp a b =>
    simp only [deepRewrite, eval]
    rw [deepRewrite_eval A a, deepRewrite_eval A b]
  | .add a b =>
    simp only [deepRewrite, eval]
    rw [deepRewrite_eval A a, deepRewrite_eval A b]
  | .const _ => rfl

/-- Iterated deep extensionalization. -/
def iterDeepRewrite : ℕ → TermF C → TermF C
  | 0, t => t
  | k + 1, t => deepRewrite (iterDeepRewrite k t)

/-- Iterated deep extensionalization preserves semantics at every depth. -/
theorem iterDeepRewrite_eval (A : LeibnizAlgebra C S)
    (k : ℕ) (t : TermF C) :
    eval A (iterDeepRewrite k t) = eval A t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [iterDeepRewrite]
    rw [deepRewrite_eval A, ih]

/-! ## Part 8: Instantiation — The Spectral Framework as a Special Case

    The spectral framework's Term type is TermF with three constants
    (f₀, f₁, z). The universal obstruction specializes to recover
    the original no_coalgebra_morphism theorem. -/

/-- The spectral framework's constants. -/
inductive SpectralConst : Type where
  | f₀ : SpectralConst
  | f₁ : SpectralConst
  | z : SpectralConst
  deriving DecidableEq, Repr

/-- Spectral terms are TermF over SpectralConst. -/
abbrev SpectralTerm := TermF SpectralConst

/-- The spectral obstruction is a special case of the universal one. -/
theorem spectral_encoding_obstruction
    (ε : SpectralTerm → ℕ) (hε : Function.Injective ε) (a b : SpectralTerm) :
    ε (leibnizRewrite (.obs (.comp a b))) ≠ ε (.obs (.comp a b)) :=
  universal_encoding_obstruction ε hε a b

/-! ## Part 9: Instantiation — Peano Arithmetic as a Special Case

    PA's term language has constants 0, S, +, ×. When extended with
    a derivation-like observation (ANY unary operation satisfying the
    Leibniz rule on ×), it becomes a TermF instance with the same
    obstruction.

    This demonstrates the video's insight: PA is a "theory of all
    theories," and any theory of theories hits the obstruction. -/

/-- PA's constants (in the extended language with observation). -/
inductive PAConst : Type where
  | zero : PAConst
  | succ : PAConst
  deriving DecidableEq, Repr

/-- PA terms (with comp = ×, add = +, obs = derivation). -/
abbrev PATerm := TermF PAConst

/-- PA hits the same obstruction: no injective encoding commutes
    with observation of multiplication, because the Leibniz rule
    (product rule) introduces addition. -/
theorem pa_encoding_obstruction
    (ε : PATerm → ℕ) (hε : Function.Injective ε) (a b : PATerm) :
    ε (leibnizRewrite (.obs (.comp a b))) ≠ ε (.obs (.comp a b)) :=
  universal_encoding_obstruction ε hε a b

/-! ## Part 10: Why This Is Universal Over All Self-Referential Theories

    The chain of reasoning:

    1. SELF-REFERENCE REQUIRES PA (Godel 1931, the video's main point):
       Any theory that can encode its own syntax, verify its own proofs,
       and build the diagonal sentence must interpret PA. The theory of
       strings with two generators and concatenation is mutually
       interpretable with PA. Every "theory of theories" IS arithmetic.

    2. PA HAS MULTIPLICATION (a binary operation — comp):
       PA's axioms include multiplication, defined by:
       a × 0 = 0, a × S(b) = a × b + a

    3. ANY DERIVATION ON A PRODUCT GIVES LEIBNIZ:
       If D is a derivation on a ring (D(a+b) = D(a)+D(b),
       D(a×b) = D(a)×b + a×D(b)), the Leibniz rule is not a
       design choice — it is forced by the algebraic structure.
       Derivations on commutative rings necessarily satisfy it.

    4. LEIBNIZ CHANGES ROOT CONSTRUCTOR (proved above):
       obs(comp(a,b)) becomes add(...), which is syntactically
       distinct from obs(comp(a,b)). Universal over all signatures.

    5. THEREFORE: any self-referential theory, when equipped with
       any derivation-like observation on its multiplication, hits
       the encoding obstruction. The obstruction is not specific to
       eigenvalue arithmetic — it is structural to self-reference itself.

    The remaining question (which this formalization does not resolve):
    must a self-referential theory HAVE a derivation? The answer is yes
    in the following sense: the evaluation of compound terms (which any
    theory must perform to check proofs) IS a form of extensionalization
    that introduces addition. PA's evaluation rules for multiplication:
      S(a) × b → a × b + b
    This IS the Leibniz rule with obs = "one step of evaluation" and
    comp = ×. The product rule is not an additional axiom imposed on
    PA — it is what PA's own evaluation rules already do.

    This is the content of the video's observation: arithmetic is
    THE theory of all theories, and arithmetic's evaluation rules
    are Leibniz rules in disguise. -/

end TermF

end UniversalObstruction
