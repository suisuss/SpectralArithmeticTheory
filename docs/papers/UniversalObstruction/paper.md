# The Encoding Obstruction: A Structural Characterization of Self-Referential Impossibility, Formalized in Lean 4

**Status:** draft in progress. Follow the ordering in `outline.md`. Each section has a `> TODO` marker if not yet drafted.

**Target venue:** CPP 2027 or ITP 2027.

**Working paper scope:** the 12 core `Obstruction/` modules (~4,200 lines, 12 named axioms at boundary points, zero sorries). Scaffolding and extensions are cited but not headline.

---

## 1. Abstract

> TODO — draft last, once §§2, 4-10 have enough content to know what the abstract is abstracting. Target 200 words per outline.

---

## 2. Introduction

> TODO — draft after §4 and §6 so motivating examples land concretely. ~3 pages per outline.

---

## 3. Background and Related Work

> TODO — needs careful reading of Lawvere 1969, Yanofsky 2003, and a pass over Flypitch before drafting. ~2 pages per outline.

---

## 4. The Universal Encoding Obstruction

This section presents the central theorem of the formalization and its proof over a parameterized term algebra. We state the theorem once, universally, and recover each domain-specific instance as a specialization in later sections.

### 4.1 The parameterized term algebra

We isolate the structural content of a Leibniz-style rewrite by parameterizing the term algebra over an arbitrary signature of constants.

```lean
inductive TermF (C : Type*) : Type _ where
  | const : C → TermF C
  | comp  : TermF C → TermF C → TermF C
  | add   : TermF C → TermF C → TermF C
  | obs   : TermF C → TermF C
```

Three structural operations are fixed: a binary composition `comp`, a binary addition `add`, and a unary observation `obs`. The type `C` is left abstract. Arithmetic instantiates `C` with `{zero, succ}`; the spectral framework instantiates `C` with `{f₀, f₁, z}`; a lambda-calculus-style setting would instantiate with function symbols. The obstruction theorem is proved once at this level of abstraction and transports to every instantiation.

The choice to fix exactly these three structural constructors is load-bearing. `comp` is the binary operation that the observation will be applied to; `add` is the operation that observation introduces when extensionalized; `obs` is the operation that triggers the rewrite. If `add ≠ obs` as Lean constructors of `TermF C`, the obstruction is immediate. If they were unified — for example if we worked over an algebraic signature with a single binary operation and relied on commutativity to recover extensionalization — the form-change premise would no longer be definitional and the proof would require domain-specific arithmetic work.

### 4.2 The Leibniz rewrite

The Leibniz rewrite is defined identically for every signature `C`:

```lean
def leibnizRewrite : TermF C → TermF C
  | .obs (.comp a b) => .add (.comp (.obs a) b) (.comp a (.obs b))
  | t => t
```

On the trigger pattern `obs(comp(a, b))` the rewrite produces an `add`-rooted term. On every other input it is the identity. The rewrite is total and terminates in one step; we are not studying a reduction system here but a single-step form-changing operation.

### 4.3 Root constructor change

The structural fact driving the obstruction is that `leibnizRewrite` changes the root constructor on its trigger pattern:

```lean
theorem leibniz_changes_form (a b : TermF C) :
    leibnizRewrite (.obs (.comp a b)) ≠ .obs (.comp a b) := by
  simp [leibnizRewrite]
```

The proof is one line. The reason it works is that `add` and `obs` are distinct constructors of `TermF C`, which Lean's `simp` dispatches via `Function.Injective` facts on inductive constructors. Nothing domain-specific enters.

This is the key point: the rewrite does not merely produce a term with different "contents" or a "different value" — it produces a term with a **different top-level constructor**. At the level of syntactic inductive types, that is a binary, model-independent distinction. No injective map can collapse it. We expand on why this specific structural feature is load-bearing — as opposed to weaker "form changes" such as size growth alone — in §5.

### 4.4 The universal encoding obstruction

From `leibniz_changes_form` and injectivity the obstruction is immediate.

```lean
theorem universal_encoding_obstruction
    (ε : TermF C → ℕ) (hε : Function.Injective ε) (a b : TermF C) :
    ε (leibnizRewrite (.obs (.comp a b))) ≠ ε (.obs (.comp a b)) := by
  intro h
  exact absurd (hε h) (leibniz_changes_form a b)
```

For every signature `C`, every injective encoding `ε : TermF C → ℕ`, and every pair of sub-terms `a, b`: the Gödel number of the extensionalized form differs from the Gödel number of the intensional form. The proof is the contrapositive of injectivity applied to the form-change lemma.

At this level of abstraction the theorem is, mathematically, almost trivial: the non-trivial work has been pushed into the definition of `TermF` and the choice of `leibnizRewrite`. We consider this honest rather than hollow. The contribution of §4 is not the proof but the claim that this specific combination — a parameterized algebraic signature, a particular structural rewrite, and the resulting constructor-level form change — is strong enough to subsume the concrete impossibility results of §§6-9 while being weak enough to admit a uniform proof. The non-trivial work lies in showing that each concrete instance (Gödel encoding, beta reduction, resolution) genuinely fits this abstraction; that work is done in the instance sections.

### 4.5 Semantic invariance

The obstruction is not a defect of the rewrite. Meaning is preserved. We formalize this over an abstract algebra satisfying the Leibniz law:

```lean
structure LeibnizAlgebra (C : Type*) (S : Type*) where
  interpConst : C → S
  interpComp  : S → S → S
  interpAdd   : S → S → S
  interpObs   : S → S
  leibniz_law : ∀ a b : S, interpObs (interpComp a b) =
    interpAdd (interpComp (interpObs a) b) (interpComp a (interpObs b))
```

Evaluating a term in such an algebra respects the rewrite pointwise:

```lean
theorem leibnizRewrite_preserves_eval (A : LeibnizAlgebra C S)
    (a b : TermF C) :
    eval A (leibnizRewrite (.obs (.comp a b))) =
      eval A (.obs (.comp a b)) := by
  simp only [leibnizRewrite, eval]
  rw [← A.leibniz_law]
```

The proof is one rewrite by the algebra's `leibniz_law`. Every `LeibnizAlgebra` is a witness that the rewrite is semantics-preserving. A derivation on a commutative ring is a `LeibnizAlgebra`; the evaluation of PA multiplication with `obs` read as "one step of evaluation" and `comp` read as `×` is a `LeibnizAlgebra`; interpretations of lambda terms satisfying η-equivalence on application form a `LeibnizAlgebra` modulo parsing.

### 4.6 The intension/extension gap

Combining 4.4 and 4.5 gives the structural statement that organizes the rest of the paper:

```lean
theorem intension_extension_gap (A : LeibnizAlgebra C S)
    (ε : TermF C → ℕ) (hε : Function.Injective ε) (a b : TermF C) :
    ε (leibnizRewrite (.obs (.comp a b))) ≠ ε (.obs (.comp a b)) ∧
    eval A (leibnizRewrite (.obs (.comp a b))) =
      eval A (.obs (.comp a b)) :=
  ⟨universal_encoding_obstruction ε hε a b,
   leibnizRewrite_preserves_eval A a b⟩
```

The encoding distinguishes what the semantics identifies. Form changes; meaning does not. Both facts are universal over signatures, models, injective encodings, and sub-terms.

This is the structural content we claim underlies the classical impossibility results. In each later section we exhibit a specific rewrite — the Gödel diagonal for §6, the halting computation for §7, beta reduction for §8, resolution for §9 — and show that it fits the pattern: the rewrite changes a structural feature no injection can track, while preserving the semantic property we care about. The proof obligations are then uniform: form change and semantic preservation, both local and constructor-level. What varies between instances is not the obstruction but the choice of what counts as "form" and what counts as "meaning."

### 4.7 Trajectory divergence

One further fact from `Universal.lean` that will be used in §8 and §9: the Leibniz rewrite does not merely change the root constructor, it also strictly grows term size — by more than a factor of two.

```lean
theorem leibniz_more_than_doubles (a b : TermF C) :
    termSize (leibnizRewrite (.obs (.comp a b) : TermF C)) >
    2 * termSize (.obs (.comp a b) : TermF C) := by
  rw [leibnizRewrite_size, obs_comp_size]; omega
```

Iterated, this gives an unbounded chain of distinct terms with exponentially growing size. We use this quantitative refinement in §8 (beta reduction's duplicator) and §9 (proof-length lower bounds from size-bounded rewrites).

---

## 5. The `EvalRewriteWitness` Abstraction

§4 proved the obstruction for one specific rewrite (`leibnizRewrite`) on one specific term algebra (`TermF C`). This section extracts the structural content into an abstraction, identifies precisely what hypothesis is doing the work, and — critically — shows that a weaker hypothesis one might be tempted to assume instead is insufficient.

### 5.1 The three ingredients

The obstruction requires three distinct things, not two:

1. A term algebra `T`.
2. A semantic interpretation `eval : T → S`, so that distinct terms can mean the same thing.
3. A rewrite `R : T → T` that is both **form-changing** (`R t ≠ t` for some witness `t`) and **meaning-preserving** (`eval (R t) = eval t`).

A natural first guess is that (1) + (2) alone already creates the obstruction. That is, as soon as a term algebra admits two distinct terms with the same denotation, injective encoding should be impossible. This is false, and the falsity is where most of the content of this section lies. We make the distinction sharp in 5.3.

### 5.2 The abstraction

`EvalRewriteWitness` packages the three ingredients as a Lean structure:

```lean
structure EvalRewriteWitness (T S : Type*) where
  rewrite           : T → T
  eval              : T → S
  witness           : T
  changes_form      : rewrite witness ≠ witness
  preserves_meaning : eval (rewrite witness) = eval witness
```

From any witness the encoding obstruction is immediate, by the same one-line proof as §4.4:

```lean
theorem eval_rewrite_obstruction {T S : Type*}
    (w : EvalRewriteWitness T S) (ε : T → ℕ) (hε : Function.Injective ε) :
    ε (w.rewrite w.witness) ≠ ε w.witness :=
  general_obstruction w.changes_form hε
```

The `general_obstruction` lemma is the pure form of the argument — divorced from any specific term algebra:

```lean
theorem general_obstruction {T : Type*}
    {R : T → T} {t : T} (hne : R t ≠ t)
    {ε : T → ℕ} (hε : Function.Injective ε) :
    ε (R t) ≠ ε t := by
  intro h; exact absurd (hε h) hne
```

This is logically trivial, as we observed in §4. What it buys is: the obstruction is not a specific result about a specific rewrite. It is a pattern that fires whenever the three ingredients above are simultaneously instantiated.

### 5.3 Non-trivial semantics alone is not enough

A reviewer's natural challenge: "Isn't `EvalRewriteWitness` just notation for 'there exist distinct terms with the same denotation'?" We answer formally: no.

Consider the weaker hypothesis packaged on its own:

```lean
structure NonTrivialSemantics (T S : Type*) where
  eval         : T → S
  term1 term2  : T
  distinct     : term1 ≠ term2
  same_meaning : eval term1 = eval term2
```

This is the hypothesis "two distinct terms with the same denotation." It is strictly weaker than `EvalRewriteWitness`: there is no rewrite mentioned. The following is provable in Lean:

```lean
theorem nontrivial_semantics_admits_injection
    (_NTS : NonTrivialSemantics ℕ ℕ) :
    ∃ ε : ℕ → ℕ, Function.Injective ε :=
  ⟨id, Function.injective_id⟩
```

The identity function is an injective encoding of any non-trivially-semantic witness. There is no contradiction: the encoding gives `term1` and `term2` different codes, which is fine because no process requires them to have the same code. Semantic equivalence between distinct terms is the ordinary, unobstructed case.

What changes when we add a rewrite? Given any `NonTrivialSemantics` witness on a type with decidable equality, we can build an `EvalRewriteWitness` by defining the rewrite to swap `term1` to `term2`:

```lean
def NonTrivialSemantics.toRewrite {T S : Type*} [DecidableEq T]
    (NTS : NonTrivialSemantics T S) : EvalRewriteWitness T S where
  rewrite := fun t => if t = NTS.term1 then NTS.term2 else t
  eval    := NTS.eval
  witness := NTS.term1
  ...
```

Once the rewrite is present, the obstruction appears:

```lean
theorem rewrite_creates_obstruction
    {T S : Type*} [DecidableEq T] (NTS : NonTrivialSemantics T S)
    (ε : T → ℕ) (hε : Function.Injective ε) :
    ε ((NTS.toRewrite).rewrite (NTS.toRewrite).witness) ≠
    ε (NTS.toRewrite).witness
```

The rewrite is the active ingredient. Semantic equivalence alone is inert. This is the precise formal statement answering the reviewer's challenge, and it is what we mean when we say the obstruction is about **rewrites**, not about semantics.

### 5.4 Multiple sufficient conditions for form change

`changes_form` asks only for `R t ≠ t`, a syntactic inequality in the term type. Many structural features of a rewrite establish this. Root-constructor change is one; commutativity is another; size growth is a third. Each independently yields the obstruction.

We formalize this by exhibiting two distinct witnesses on toy algebras. First, a root-constructor-changing rewrite on a two-constructor type:

```lean
inductive ABTerm where | a : ABTerm | b : ABTerm

def abRewrite : ABTerm → ABTerm
  | .a => .b
  | t  => t
```

This is the caricature of the Leibniz rewrite: one pattern fires, the root constructor changes, and the obstruction follows by `eval_rewrite_obstruction`.

Second, a commutativity-style rewrite on a single-constructor pair type:

```lean
inductive PairTerm where | mk : ABTerm → ABTerm → PairTerm

def swapRewrite : PairTerm → PairTerm
  | .mk x y => .mk y x
```

Here the root constructor is preserved — every `PairTerm` is a `.mk`, before and after. Form change is carried entirely by sub-term rearrangement. The obstruction still fires, because `.mk .a .b ≠ .mk .b .a` as inductive values.

The general pattern we highlight across all our instances in §§6-9 is root-constructor change, but the abstraction is agnostic to the mechanism. Any syntactic inequality combined with semantic equivalence — regardless of whether the top-level constructor changes — is sufficient.

### 5.5 Why root-constructor change is our working hypothesis

Although commutativity, associativity, and other root-preserving form changes also create the obstruction, every instance we formalize in §§6-9 uses root-constructor change:

| Instance (section) | Rewrite | Root change |
|---|---|---|
| Leibniz (§4) | `leibnizRewrite` | `obs` → `add` |
| PA multiplication (§6) | `mulStep` | `times` → `plus` |
| PA addition (§6) | `addStep` | `plus` → `succ` |
| Beta reduction (§8) | single beta step | `App` → function body's root |
| Cut elimination (§8) | via Curry-Howard | same as beta |

Root-constructor change has two properties that make it the cleanest working hypothesis:

1. It is **local**: the distinction is visible at the term's outermost level, without descending into sub-terms. This keeps the form-change proof at one line per instance.
2. It is **model-independent**: it depends only on inductive-type structure, not on any chosen semantics. `mulStep_changes_form`, `leibniz_changes_form`, and the beta analog are all discharged by `simp` in one step.

Root-constructor change is a sufficient condition, not a necessary one. We frame the abstraction in the more general form (`changes_form`) and take root-constructor change as the specific mechanism common to our instances. This matters for the Related Work discussion (§§3, 11): Lawvere 1969 and Yanofsky 2003 abstract the fixed-point / self-reference pattern; we abstract the complementary rewrite/encoding pattern, and locate the concrete obstruction in a structural constructor-level fact rather than in any categorical machinery.

### 5.6 What §5 establishes

The paper's sharpest framing, which we carry from here forward:

> The encoding obstruction is a consequence of a form-changing, meaning-preserving rewrite. Root-constructor change is the cleanest sufficient condition for form change and is the pattern observed across all our instances. Generic non-trivial semantics — distinct terms with the same denotation but no rewrite moving between them — does not create the obstruction.

The sections that follow instantiate this pattern six times. The burden on each instance section is to exhibit a rewrite, prove it changes form, and prove it preserves the relevant semantics. In each case the proof obligations are local and one to two lines.

---

## 6. Self-Reference and Incompleteness

The first instance where the abstraction of §§4-5 buys something non-trivial is Gödel's first and second incompleteness theorems. The formalization follows two parallel paths, both machine-checked and sorry-free: one in `Diagonal.lean` that axiomatizes the low-level Gödel-encoding primitives and proves the diagonal lemma as a theorem, and one in `Incompleteness.lean` that axiomatizes the diagonal property directly and gets to incompleteness faster. We describe both, then relate them back to §§4-5.

### 6.1 The `GodelSystem` abstraction

The lower of the two paths isolates what must be assumed about a theory for the diagonal construction to work. The key move is that the diagonal lemma is *not* among the assumptions:

```lean
structure GodelSystem (Sentence : Type*) where
  provable          : Sentence → Prop
  neg               : Sentence → Sentence
  Formula           : Type*
  subst             : Formula → ℕ → Sentence
  scode             : Sentence → ℕ
  fcode             : Formula → ℕ
  decode            : ℕ → Formula
  decode_fcode      : ∀ φ, decode (fcode φ) = φ
  diagN             : ℕ → ℕ
  diagN_spec        : ∀ n, diagN n = scode (subst (decode n) n)
  compose_diag      : Formula → Formula
  compose_diag_prov : ∀ β n,
    provable (subst (compose_diag β) n) ↔ provable (subst β (diagN n))
  compose_diag_neg  : ∀ β n, ...
```

The axioms fall into three classes:

1. **Coding/decoding**: `scode`, `fcode`, `decode`, with `decode_fcode` stating that decoding inverts formula coding.
2. **The diagonal function**: `diagN` with `diagN_spec` stating that `diagN n` is the code of what you get by decoding `n` into a formula and substituting `n` back in as its argument.
3. **Representability of composition with `diagN`**: `compose_diag β` is a formula whose substitution is equivalent to substituting `β` at `diagN n`.

These are the *genuine* primitives of Gödel encoding. In PA they correspond to Gödel's 1931 representability theorem (for `compose_diag_prov`) and to the unique prime factorization argument (for `decode_fcode`). The PA instance of this structure is scaffolded in `PAGodelSystem.lean`, with Phase 1 (prime factorization) now fully discharged (PR #49) and Phases 2-4 tracked under issues #50-#52; we discuss this in §10.

### 6.2 The diagonal lemma is a theorem

From these axioms the diagonal lemma is provable in ~10 lines. The key computation is:

```lean
theorem diagN_at_compose (β : G.Formula) :
    G.diagN (G.fcode (G.compose_diag β)) =
    G.scode (godelConstruction G β) := by
  simp only [godelConstruction, selfApply]
  rw [G.diagN_spec]
  congr 1; congr 1
  exact G.decode_fcode _
```

This says: the diagonal number of the code of `compose_diag β` equals the sentence code of the Gödel construction `godelConstruction β = selfApply (compose_diag β)`. Unpacking: `diagN_spec` rewrites `diagN n` as the code of a substitution, `decode_fcode` cancels `decode ∘ fcode`, and the two substitutions are definitionally equal. All three ingredients are axioms of `GodelSystem`, but each is substantially more primitive than the diagonal lemma itself.

The lemma follows as a biconditional:

```lean
theorem diagonal_lemma (β : G.Formula) :
    G.provable (godelConstruction G β) ↔
    G.provable (G.subst β (G.scode (godelConstruction G β))) :=
  ⟨diagonal_lemma_mp G β, diagonal_lemma_mpr G β⟩
```

This is the fixed-point statement: for every formula `β`, there is a sentence whose provability is equivalent to `β` applied to its own code. Most textbook treatments of incompleteness take the diagonal lemma itself as the primitive step; here it is decomposed into coding, decoding, and representability of `diagN`, each of which is independently meaningful and independently checkable against a concrete instantiation.

### 6.3 First incompleteness

Provability must be internalized before the Gödel sentence can be constructed. `ProvabilityData` packages what is needed:

```lean
structure ProvabilityData (G : GodelSystem Sentence) where
  prov            : G.Formula
  neg_prov        : G.Formula
  neg_prov_spec   : ∀ n, G.subst neg_prov n = G.neg (G.subst prov n)
  sigma1_complete : ∀ s, G.provable s → G.provable (G.subst prov (G.scode s))
  sigma1_sound    : ∀ s, G.provable (G.subst prov (G.scode s)) → G.provable s
  dne             : ∀ s, G.provable (G.neg (G.neg s)) → G.provable s
```

The Gödel sentence is `godelSentence = godelConstruction neg_prov`. The diagonal lemma gives us `provable(gs) ↔ provable(subst(neg_prov, scode(gs))) = provable(neg(subst(prov, scode(gs))))`. The two halves of first incompleteness are then immediate:

```lean
theorem godel_not_provable (D : ProvabilityData G) (hcon : consistent G) :
    ¬G.provable (godelSentence G D)

theorem godel_not_refutable (D : ProvabilityData G) (hcon : consistent G) :
    ¬G.provable (G.neg (godelSentence G D))
```

`godel_not_provable` uses Σ₁-completeness; `godel_not_refutable` uses Σ₁-soundness and double-negation elimination. Both are direct contradictions from the diagonal lemma, the provability-data properties, and consistency. Combined:

```lean
theorem first_incompleteness (D : ProvabilityData G) (hcon : consistent G) :
    ¬G.provable (godelSentence G D) ∧
    ¬G.provable (G.neg (godelSentence G D))
```

### 6.4 Second incompleteness

We formalize the second theorem via the contrapositive of internalization. If the theory can prove `con → G` (its own consistency implies the Gödel sentence), then it cannot prove `con`:

```lean
theorem second_incompleteness (D : ProvabilityData G) (hcon : consistent G)
    (con : Sentence)
    (con_implies_G : G.provable con → G.provable (godelSentence G D)) :
    ¬G.provable con
```

The proof is two lines: assume the theory proves `con`; apply `con_implies_G` to get a proof of the Gödel sentence; contradict `godel_not_provable`. The assumption `con_implies_G` is the hard part and is itself a substantial theorem in the concrete PA setting — we do not discharge it. What the formalization contributes is the explicit, minimal dependency structure: second incompleteness is no more than first incompleteness plus an internalized proof.

### 6.5 The abstract path: `DiagonalTheory`

The parallel file `Incompleteness.lean` axiomatizes the diagonal property directly, skipping the coding/decoding infrastructure:

```lean
structure DiagonalTheory (Sentence : Type*) extends FormalTheory Sentence where
  diag         : (Sentence → Sentence) → Sentence
  diag_mp      : ∀ P, provable (diag P) → provable (P (diag P))
  diag_mpr     : ∀ P, provable (P (diag P)) → provable (diag P)
  diag_neg_mp  : ∀ P, provable (neg (diag P)) → provable (neg (P (diag P)))
  diag_neg_mpr : ∀ P, provable (neg (P (diag P))) → provable (neg (diag P))
```

`DiagonalTheory` trades precision for brevity. Its axioms are what a theory with Gödel encoding *does*, not how it does it. The incompleteness proofs (`godel_not_provable`, `godel_not_refutable`, `first_incompleteness`, `second_incompleteness`) go through with the same structure as §6.3-§6.4 but shorter, because the diagonal property is given rather than derived.

The two paths are complementary:
- `Diagonal.lean` answers "what must be true for the diagonal lemma to hold?"
- `Incompleteness.lean` answers "what follows from the diagonal property?"

A concrete theory such as PA satisfies the lower-level `GodelSystem` axioms, which gives the diagonal lemma, which gives the `DiagonalTheory` structure. Both paths terminate in the same incompleteness theorems; the choice is about where to place the axiomatic burden.

### 6.6 Why the obstruction explains diagonalization

The claim of §§4-5 was that the obstruction is the structural content underlying classical impossibility results. The connection to incompleteness is not decorative, it is the formal bridge statement in `Incompleteness.lean`:

```lean
theorem obstruction_and_incompleteness
    (T : DiagonalTheory Sentence) (prov : ...) (...)
    (w : EvalRewrite.EvalRewriteWitness Sentence S)
    (ε : Sentence → ℕ) (hε : Function.Injective ε) :
    (ε (w.rewrite w.witness) ≠ ε w.witness ∧
     w.eval (w.rewrite w.witness) = w.eval w.witness) ∧
    T.toFormalTheory.undecidable (DiagonalTheory.godelSentence T prov)
```

This gives, from a single set of hypotheses: (a) an `EvalRewriteWitness` exhibits the eval-quote failure on the sentence type, and (b) the theory is incomplete. These are not presented as independent facts. The theorem's role is to record, in the proof-carrying record, that the two are available together.

The informal claim we draw from this is stronger than the theorem: the obstruction (a) is the *structural reason* the diagonal property (and therefore incompleteness) exists. Substitution in a theory with a non-trivial syntax is a form-changing, meaning-preserving rewrite — precisely the pattern of §5. The fact that the formal substitution is a rewrite is what gives `diagN_spec` its force: `diagN` is not the identity, it computes the code of a genuinely different object, and it is precisely this gap that the diagonal construction exploits. We do not prove this informal claim, and cannot within the present scaffolding: `DiagonalTheory` is agnostic about whether `diag` comes from substitution or from an arbitrary fixed-point operator. What we do prove is that when both structures are present, they cohabit; the deeper claim that the obstruction is *the* source of the diagonal property is a hypothesis the paper defends through its collection of instances, not a theorem within any single instance.

This is as good as it gets at the present level of abstraction. A stronger formal link would require giving `DiagonalTheory.diag` a concrete construction from `EvalRewriteWitness`, which would effectively be porting all of `Diagonal.lean`'s `GodelSystem` story into the abstract setting. We have chosen instead to keep the two paths separate and let the reader trace the informal connection — and to make the concrete connection in §10 via `PAGodelSystem.lean`, where the `GodelSystem` axioms do bottom out in PA's own substitution, which is an `EvalRewriteWitness` (by `EvalRewrite.lean`'s `paMulWitness`/`paAddWitness`).

---

## 7. The Halting Problem

The halting problem is the second instance. The proof is a century-old diagonal argument and the formalization adds no new mathematical content; what it contributes is the observation — made concrete in Lean — that the argument uses the same self-substitution mechanism as the Gödel construction of §6. We state the setup, the theorem, and the structural equivalence in under a page.

### 7.1 Setup

A computation system is a type of programs with an execution function and an injective coding:

```lean
structure ComputationSystem where
  Program        : Type*
  exec           : Program → ℕ → Option Bool
  code           : Program → ℕ
  code_injective : Function.Injective code
```

`exec p n = none` models non-termination on input `n`; `exec p n = some b` models halting with output `b`. The type `Option Bool` is the minimal commitment that keeps the argument clean: we do not need a halting oracle over an arbitrary output type, only a predicate that can say "halts with true," "halts with false," or "loops."

A halting decider is a program that correctly identifies which programs halt on which inputs:

```lean
structure HaltingDecider where
  decider     : C.Program
  pair        : ℕ → ℕ → ℕ
  sound_halts : ∀ p n, C.halts p n → C.exec decider (pair (C.code p) n) = some true
  sound_loops : ∀ p n, C.loops p n → C.exec decider (pair (C.code p) n) = some false
```

Finally, `HasDiagonal C H` packages the assumption that the diagonal program exists in the system — a weak universality assumption: whatever behavior is computable in terms of `H`, there is a program realizing it.

```lean
structure HasDiagonal (C : ComputationSystem) (H : HaltingDecider C) where
  diagProg      : C.Program
  diagProg_spec : C.exec diagProg (C.code diagProg) =
    diagonalBehavior C H (C.code diagProg)
```

where `diagonalBehavior` is the defining behavior: on input `n`, consult `H` about whether `n` halts on `n` and do the opposite.

### 7.2 The contradiction

From a halting decider and the diagonal program the contradiction is immediate:

```lean
theorem halting_undecidable (H : HaltingDecider C) (D : HasDiagonal C H) :
    False
```

Proof by case on `exec D.diagProg (code D.diagProg)`. In both cases — `some val` (halting) and `none` (looping) — the soundness hypothesis of the decider combined with `diagProg_spec` produces a contradiction with the case assumption. The proof is twenty lines and completely routine. Its content is entirely in the setup: once `HaltingDecider` and `HasDiagonal` are written as Lean structures, `halting_undecidable` is a direct case analysis.

### 7.3 The structural equivalence with incompleteness

The halting problem and first incompleteness use the same mechanism and the same ingredients:

| Role | Incompleteness (§6) | Halting (§7) |
|---|---|---|
| Self-substitution | `G = diag (neg ∘ prov)` | `D` applied to `code(D)` |
| The decider | Provability predicate `prov` | Halting decider `H.decider` |
| The fixed point | Gödel sentence `godelSentence` | Diagonal program `diagProg` |
| The contradiction | `G` provable iff `G` not provable | `D(code D)` halts iff `D(code D)` loops |
| The encoding assumption | `decode ∘ fcode = id` | `code_injective` |

In both cases: self-substitution is the form-changing operation (§4 content at the abstract level; §6.2's `diagN_spec` in the incompleteness case; `diagProg_spec` in the halting case), the decider is required to commute with self-substitution, and the obstruction of §4-§5 blocks that commutation. The incompleteness proof is a deductive contradiction in a formal theory; the halting proof is a computational contradiction in an execution system. The structural content is the same.

The file makes the local connection explicit with a one-theorem bridge:

```lean
theorem execution_obstruction
    {State : Type*} (step : State → State) (s : State) (hne : step s ≠ s)
    (ε : State → ℕ) (hε : Function.Injective ε) :
    ε (step s) ≠ ε s := by
  intro h; exact absurd (hε h) hne
```

This is `general_obstruction` from §5, renamed for the computational setting. It is not a new theorem; it is a relabeling that makes the §5 abstraction visibly present in the halting proof's vocabulary. Under this reading, a halting decider is a function that would need to agree across an encoding/execution pair; `execution_obstruction` says no such function can exist when execution is genuinely form-changing.

The outline-level claim we draw from §7 is narrow and honest: the halting problem fits the `EvalRewriteWitness` pattern in the same way the Gödel construction does, and the shared pattern is not a loose analogy but the same formal ingredient (`general_obstruction`) applied to a different term/state algebra. The halting result is not a consequence of the obstruction in any stronger sense than incompleteness is; it is a second instance of the same argument, presented here to corroborate the unification claim.

---

## 8. Beta Reduction and Curry-Howard

The third and fourth instances fit the pattern of §§4-5 from a different direction. Beta reduction on lambda terms is an `EvalRewriteWitness`; via Curry-Howard, it is cut elimination on proof terms. The formalization — `BetaReduction.lean` and `CurryHoward.lean` together — establishes both instances and sets up the quantitative lever used in §9: beta reduction's duplicator strictly grows term size, and iterated it blows up exponentially, which under Curry-Howard is the mechanism behind Statman's non-elementary cut elimination bound.

### 8.1 Lambda terms with de Bruijn indices

We use de Bruijn representation to sidestep alpha-equivalence entirely:

```lean
inductive Term where
  | var : Nat → Term
  | abs : Term → Term
  | app : Term → Term → Term
```

Substitution and lifting are defined in the standard way; the key operation for §8's purposes is head beta reduction:

```lean
def betaStep : Term → Term
  | .app (.abs body) arg => subst 0 arg body
  | t => t
```

On the head redex `(λ. body) arg` the rewrite produces `body[arg/0]`; on every other input it is the identity. Head reduction is a one-step operation and is sufficient for the obstruction argument — the full reduction relation adds convergence and confluence content we do not need.

### 8.2 The witness: `(λ. 0) (λ. 0)`

The minimal closed redex is the identity combinator applied to itself:

```lean
def identity : Term := .abs (.var 0)
def witness  : Term := .app identity identity
```

On this input, `betaStep` reduces `witness` to `identity`:

```lean
theorem betaStep_witness : betaStep witness = identity := by rfl
```

The root changes from `.app` to `.abs`. Form change is then a three-line proof by discharging the constructor distinctness:

```lean
theorem betaStep_changes_form : betaStep witness ≠ witness := by
  rw [betaStep_witness]
  intro h
  exact witness_ne_identity h.symm
```

Semantic invariance under evaluation (iterated `betaStep` with generous fuel) is immediate by reflexivity: both `witness` and `betaStep witness` evaluate to `identity` within one step. The `EvalRewriteWitness` instance is then just a packaging:

```lean
def betaWitness : EvalRewrite.EvalRewriteWitness Term Term where
  rewrite           := betaStep
  eval              := eval
  witness           := witness
  changes_form      := betaStep_changes_form
  preserves_meaning := eval_betaStep_witness
```

and the obstruction is inherited by `eval_rewrite_obstruction` (§5.2).

The content of 8.2 is narrow. What makes beta reduction interesting from the paper's perspective is not the single-step form-change — that is trivial on any reducible redex — but the size-growth behavior of the next subsection, which carries the quantitative load in §9.

### 8.3 The duplicator and size growth

Beta reduction can *strictly increase* term size. The duplicator combinator `λ. 0 0`, applied to any term `t`, reduces to `t t`:

```lean
def dup : Term := .abs (.app (.var 0) (.var 0))

theorem betaStep_dupApplied (t : Term) :
    betaStep (dupApplied t) = .app t t := by rfl
```

Term size before and after:

```lean
theorem size_dupApplied (t : Term) :
    size (dupApplied t) = 5 + size t

theorem size_app_self (t : Term) :
    size (.app t t : Term) = 1 + 2 * size t
```

For `size t ≥ 5`, the output is strictly larger than the input:

```lean
theorem beta_grows_for_large (t : Term) (ht : size t ≥ 5) :
    size (betaStep (dupApplied t)) > size (dupApplied t) := by
  rw [betaStep_dupApplied, size_app_self, size_dupApplied]
  omega
```

Iterated — a term that keeps applying `dup` to its growing self — this pattern produces size growth that is at least exponential in the number of reduction steps. The same pattern appears in `Universal.lean` as `leibniz_more_than_doubles` (§4.7); there and here, size growth is the mechanism by which trajectory divergence produces quantitative lower bounds in §9.

The dual behavior — the non-terminating fixed point `Ω = (λ. 0 0) (λ. 0 0)` — illustrates an adjacent phenomenon. Ω reduces to itself (`betaStep Ω = Ω`), exhibiting no form change under `betaStep`. Ω is a witness that "form change" is the active ingredient for the obstruction: a term can be non-terminating yet have an identity reduction step; what produces the obstruction is not non-termination per se but the mismatch between a step that would change form and an encoding that cannot commute with it. For Ω, `betaStep` is the identity on this particular point and the obstruction argument does not fire; for `witness` and `dupApplied t`, it does.

### 8.4 Curry-Howard: cut elimination is beta reduction

Under the Curry-Howard correspondence, lambda terms are proof terms of minimal implicational logic:

| Lambda term | Natural-deduction reading |
|---|---|
| `.var n` | a hypothesis |
| `.abs body` | implication introduction (discharge a hypothesis) |
| `.app f a` | implication elimination (modus ponens) |
| `betaStep` | a single cut-elimination step |
| normal form | cut-free proof |

`CurryHoward.lean` makes this identification syntactically:

```lean
abbrev Proof : Type := BetaReduction.Term
def cutElim : Proof → Proof := BetaReduction.Term.betaStep
```

`cutElim` is *definitionally* equal to `betaStep`. Every theorem about beta reduction is a theorem about cut elimination under this renaming. The `EvalRewriteWitness` instance for beta reduction lifts immediately:

```lean
def cutWitness : EvalRewrite.EvalRewriteWitness Proof Proof :=
  BetaReduction.Term.betaWitness

theorem cut_elim_obstruction
    (ε : Proof → ℕ) (hε : Function.Injective ε) :
    ε (cutElim proofWithCut) ≠ ε proofWithCut :=
  BetaReduction.Term.beta_encoding_obstruction ε hε
```

The witness `proofWithCut = (λ. 0) (λ. 0)` corresponds, under Curry-Howard, to a proof that uses the identity as a lemma and immediately discharges it; the cut-free version is the identity proof with no cut. The reduction from one to the other is a single beta step, which is a single cut-elimination step.

We emphasize what this gives and what it does not. It gives: a machine-checked statement that cut elimination on proof terms is a form-changing, meaning-preserving rewrite, i.e., that cut elimination is an `EvalRewriteWitness`. It does not give: any specific complexity-theoretic result about cut elimination. That comes from composition with §9's size argument applied to Statman's specific terms, discussed next.

### 8.5 Statman's blowup as an instance

Statman 1979 constructs families of proofs for which every cut-free proof is of non-elementary size in the cut proof. Under Curry-Howard, these correspond to lambda terms whose normal forms are non-elementary in the initial term's size. The mechanism that produces the blowup is exactly the duplicator pattern of §8.3: a proof that uses a hypothesis twice (a Curry-Howard analog of `(λ. 0 0) t`) reduces by duplicating the hypothesis's proof structure; iterated, this gives towers of exponentials.

`CurryHoward.lean` records the single-step instance:

```lean
theorem cut_elim_grows_proof
    (hypothesis : Proof) (h : BetaReduction.Term.size hypothesis ≥ 5) :
    BetaReduction.Term.size (cutElim (BetaReduction.Term.dupApplied hypothesis)) >
    BetaReduction.Term.size (BetaReduction.Term.dupApplied hypothesis)
```

This is `beta_grows_for_large` under the Curry-Howard renaming. It is not Statman's theorem — Statman's theorem requires constructing specific terms whose iterated-reduction trajectory realizes the non-elementary bound. What we have shown is that the *mechanism* Statman exploits (the hypothesis-duplication step that strictly grows proof size) fits the framework of §4.7 and §9: a size-bounded rewrite with a step-wise growth factor. Given Statman's specific term families and our proof-length lower bound theorem from §9, one can read off a non-elementary lower bound on cut elimination length.

To be precise about the division of labor: Statman 1979 provides the combinatorial construction (specific proofs with non-elementary normal forms); the formalization here provides the structural frame (cut elimination is `EvalRewriteWitness`, size growth is lower-bounded per step, iteration gives exponential blowup). We do not claim to derive Statman's bound from the obstruction alone; we claim the obstruction organizes the mechanism Statman identified.

### 8.6 Universal proof systems via Curry-Howard

`CurryHoward.lean` generalizes beyond lambda calculus to a structural characterization of proof systems that inherits the obstruction:

```lean
structure NormalizationProofSystem where
  Proof              : Type*
  Theorem            : Type*
  normStep           : Proof → Proof
  proves             : Proof → Theorem
  normStep_preserves : ∀ p, proves (normStep p) = proves p
```

Any proof system whose verification involves a normalization-like step — natural deduction, sequent calculus, Hilbert systems, type-theoretic proof checkers — is a `NormalizationProofSystem`. The obstruction fires whenever there is a form-changing witness:

```lean
theorem verification_has_obstruction
    (witness : PS.Proof) (changes_form : PS.normStep witness ≠ witness)
    (ε : PS.Proof → ℕ) (hε : Function.Injective ε) :
    ε (PS.normStep witness) ≠ ε witness
```

This is `general_obstruction` at the proof-system level. It is a sufficient (not necessary) characterization: there may be proof systems whose verification does not factor through a normalization step, and the theorem says nothing about those. What it says, honestly, is: *if* verification is normalization-style, *and* normalization has at least one form-changing witness, *then* no injective encoding of proofs commutes with verification.

The practical upshot is that the obstruction is not pinned to lambda calculus or to any specific inference system. Any proof system structurally compatible with Curry-Howard inherits it. We use this generality in §9 when we turn to resolution, whose "rewrite" is the clause-extension step rather than beta reduction but whose structural profile fits the same abstraction.

---

## 9. Proof Complexity

> TODO — ~3 pages. `ProofComplexity.lean` + `Resolution.lean` + `VerificationArithmetic.lean`. Haken 1985 must be read before drafting. Decide whether to include `HakenBottleneck.lean` in the headline figure.

---

## 10. The PA GodelSystem Instance

> TODO — ~2 pages. `PAGodelSystem.lean`. Lean on the scaffolded axiom tracking (#50-#52) to frame as honest future work.

---

## 11. Related Work, In Detail

> TODO — ~2 pages. Extends §3.

---

## 12. Future Directions

> TODO — ~2 pages. Be explicit about P vs NP as speculation, not deliverable.

---

## 13. Conclusion

> TODO — ~1 page. Draft after everything else.
