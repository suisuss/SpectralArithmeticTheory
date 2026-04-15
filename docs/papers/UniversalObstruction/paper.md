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

This is the section where the framework does quantitative work. §§4-8 showed that a variety of rewrites satisfy the `EvalRewriteWitness` pattern; §9 turns the pattern into proof-length lower bounds by combining it with per-step size bounds. The result we re-derive is Haken 1985's exponential bound on resolution proofs of the pigeonhole principle. The section is written with care about the division of labor: the framework contributes a length-from-states bound; Haken contributes the combinatorial state-count bound; neither alone recovers the result.

### 9.1 The dual framing: `SizeGrowth` and `SizeBounded`

Two structures with opposite directions of bound:

```lean
structure SizeGrowth (T : Type*) where
  rewrite  : T → T
  size     : T → ℕ
  positive : ∀ t, size t ≥ 1
  grows    : ∀ t, size (rewrite t) ≥ 2 * size t

structure SizeBounded (T : Type*) where
  rewrite  : T → T
  size     : T → ℕ
  positive : ∀ t, size t ≥ 1
  bounded  : ∀ t, size (rewrite t) ≤ 2 * size t
```

`SizeGrowth` yields an *upper* bound on how few iterations suffice to reach a large size (size grows exponentially, so size 2^k is reached in at most k steps). `SizeBounded` yields a *lower* bound on how many iterations are required (size grows at most exponentially per step, so reaching size M requires at least log₂(M/initial) steps). For proof-length lower bounds we want `SizeBounded`: a rewrite where each step cannot jump the state too far, composed with a target whose size must be large.

Both structures are instantiated by a straightforward induction:

```lean
theorem iter_size (t : T) (k : ℕ) :                    -- SizeGrowth
    S.size (iter S.rewrite k t) ≥ 2^k * S.size t

theorem iter_size_upper (t : T) (k : ℕ) :              -- SizeBounded
    B.size (iter B.rewrite k t) ≤ 2^k * B.size t
```

The factor "2" is cosmetic — either structure could parameterize over an arbitrary growth constant c ≥ 1. We keep 2 as the canonical threshold since it is the rate exhibited by `leibniz_more_than_doubles` (§4.7) and by the `dup` pattern (§8.3).

### 9.2 The proof-length lower bound

From `SizeBounded` and a target-size hypothesis the lower bound is immediate:

```lean
theorem proof_length_lower_bound (t : T) (k : ℕ) (M : ℕ)
    (hM : B.size (iter B.rewrite k t) ≥ M) :
    2^k * B.size t ≥ M
```

Unpacking: if the trajectory of length `k` from `t` reaches size at least `M`, then `2^k ≥ M / size t`. Taking log base 2, any proof reaching a size-M state must have at least `log₂(M / initial_size)` steps.

Composed with an injective encoding (the obstruction), we get the combined statement:

```lean
theorem obstruction_length_bound (t : T) (k : ℕ) (M : ℕ)
    (hM : B.size (iter B.rewrite k t) ≥ M)
    (ε : T → ℕ) (hε : Function.Injective ε) :
    2^k ≥ M / B.size t
```

This is the structural form of a proof complexity result: size bound + encoding injectivity + target size = length bound. The theorem is logically content-light — it is the composition of `iter_size_upper` with division. What makes it useful is that it plugs into the `EvalRewriteWitness` picture: each step of the rewrite is form-changing (so the obstruction holds), and each step is size-bounded (so the length bound holds), and the obstruction guarantees that distinct points in the trajectory have distinct codes.

### 9.3 Cut elimination as the first application

Beta reduction on duplicator-style terms is size-bounded at the 2× threshold:

```lean
theorem dup_bounded_by_two
    (t : BetaReduction.Term) (_ht : BetaReduction.Term.size t ≥ 5) :
    BetaReduction.Term.size (BetaReduction.Term.betaStep
      (BetaReduction.Term.dupApplied t)) ≤
    2 * BetaReduction.Term.size (BetaReduction.Term.dupApplied t)
```

Composed with Statman's specific terms (§8.5), whose cut-free form is of non-elementary size in the cut form, `proof_length_lower_bound` gives a non-elementary lower bound on cut elimination length. We do not formalize Statman's construction; what we formalize is the structural mechanism (size-bounded step + obstruction) that his argument requires. Stating this precisely: if one has a family of proofs whose cut forms are of size `s(n)` and whose cut-free forms are of size `M(n)`, and the per-step growth is bounded by 2, then cut elimination on that family requires at least `log₂(M(n) / s(n))` steps. For Statman's family, this is non-elementary; for generic families, the bound may be trivial.

### 9.4 Resolution: each step adds exactly one clause

Resolution is the second, sharper application. A proof state is a list of clauses; a resolution step identifies two clauses and a pivot and appends the resolvent:

```lean
abbrev ProofState := List Clause

def resolutionStep (state : ProofState) (c1 c2 : Clause) (v : ℕ) : ProofState :=
  resolveOn c1 c2 v :: state
```

Size grows by exactly one per step:

```lean
theorem resolutionStep_size (state : ProofState) (c1 c2 : Clause) (v : ℕ) :
    stateSize (resolutionStep state c1 c2 v) = stateSize state + 1
```

This is much stronger than `SizeBounded`'s 2× threshold — resolution is size-bounded by +1 per step, the tightest possible linear bound. Form change is a trivial consequence: sizes differ, so states differ.

```lean
theorem resolutionStep_changes_form
    (state : ProofState) (c1 c2 : Clause) (v : ℕ) :
    resolutionStep state c1 c2 v ≠ state
```

Along a resolution trajectory, all state sizes are distinct, hence all states are distinct:

```lean
theorem stateAtStep_distinct (initial : ProofState) (proof : ResolutionProof)
    (i j : ℕ) (hi : i ≤ proof.length) (hj : j ≤ proof.length) (hne : i ≠ j) :
    stateAtStep initial proof i ≠ stateAtStep initial proof j
```

The encoding obstruction then guarantees distinct codes along the trajectory. The length of the proof equals the difference between final and initial state sizes:

```lean
theorem proof_length_eq_size_growth
    (initial final : ProofState) (proof : ResolutionProof)
    (h : applyProof initial proof = final) :
    proof.length = stateSize final - stateSize initial
```

So far everything holds for *any* resolution proof of *any* unsatisfiable formula. The content is: resolution length equals state-size growth, and all intermediate states are distinguishable by any injection. There is no lower bound on length yet — that requires a hypothesis that the proof must reach a large state.

### 9.5 Haken's bound: the honest separation

Haken 1985 proved: any resolution refutation of PHP(n+1, n) uses at least 2^(n/20) clauses. The argument has two parts in our framework:

1. **Combinatorial (Haken's contribution):** any refutation of PHP must pass through proof states containing certain "wide" clauses, and the number of such clauses is 2^(n/20). This is a non-trivial combinatorial bottleneck argument about pigeonhole instances; it does not follow from anything in the obstruction framework.

2. **Structural (what the framework gives for free):** given that the final state is of size at least `initial + 2^(n/20)`, and each resolution step adds exactly one clause, the proof length is at least 2^(n/20).

The formalization makes the separation explicit. We axiomatize Haken's contribution:

```lean
opaque PHP_state_lower_bound (n : ℕ) : ℕ
axiom PHP_state_lower_bound_spec (n : ℕ) : PHP_state_lower_bound n ≥ 2^(n / 20)
```

and prove the structural composition:

```lean
theorem haken_lower_bound (n : ℕ) (proof : ResolutionProof)
    (h_size : stateSize (applyProof (PHP_initial n) proof) ≥
              stateSize (PHP_initial n) + PHP_state_lower_bound n) :
    proof.length ≥ 2^(n / 20)
```

The proof is four lines: use `applyProof_size` to equate size growth with length, rewrite the hypothesis, `omega`.

We state the position plainly: the framework recovers Haken's exponential bound given his state-count lemma as input. The framework does not derive the state-count lemma. That is the honest scope. A formalization that derived `PHP_state_lower_bound_spec` from primitives would require porting Haken's proof — a substantial independent project, tracked as issue #37 and positioned as medium-term follow-up (see §12).

This separation is what the outline's "framework provides LENGTH-from-STATES, Haken provides STATE-COUNT-from-COMBINATORICS" phrase refers to. A reviewer skeptical of the obstruction's proof-complexity relevance should note the following: the length-from-states step is almost trivial once resolution is cast as a +1-per-step rewrite, so the structural contribution is organizational rather than deep. Its value is in saying that proof-complexity lower bounds for size-bounded rewrite systems fit a uniform pattern, and in making the division of labor between combinatorial content and structural content explicit at the level of Lean proofs.

### 9.6 Universal proof systems via verification arithmetic

`VerificationArithmetic.lean` gives an alternative route to the obstruction for arbitrary proof systems, complementary to the Curry-Howard route of §8.6. The structural assumption is Cook-Reckhow:

```lean
structure CookReckhowSystem where
  Proof                   : Type*
  Theorem                 : Type*
  verify                  : Proof → Theorem → Bool
  verifyStep              : Proof → Proof
  verifyStep_witness      : Proof
  verifyStep_changes_form : verifyStep verifyStep_witness ≠ verifyStep_witness
  verifyStep_preserves    : ∀ p T, verify (verifyStep p) T = verify p T
```

The assumption is that a proof system's verifier factors through at least one form-changing, verification-preserving internal computation. Given this, the obstruction is immediate:

```lean
theorem verification_obstruction (T : CR.Theorem)
    (ε : CR.Proof → ℕ) (hε : Function.Injective ε) :
    ε (CR.verifyStep CR.verifyStep_witness) ≠ ε CR.verifyStep_witness
```

The concrete inhabitant: a toy system in which proofs are PA terms, the verification step is `mulStep` from `EvalRewrite.lean`, and verification decides numerical equality in the standard model:

```lean
def paArithmeticSystem : CookReckhowSystem where
  Proof      := PATerm
  Theorem    := PATerm
  verify     := fun p T => decide (evalN p = evalN T)
  verifyStep := mulStep
  ...
```

This makes concrete the claim that "verification requires arithmetic" in the weakest possible form: the PA arithmetic system is a Cook-Reckhow proof system, and its verification step is a PA evaluation rule whose form-changing character is exactly §4.3's `mulStep_changes_form`. Any real proof system (Hilbert, sequent, natural deduction) that internally performs PA arithmetic inherits the obstruction via this structural route. The claim is honest about its form: we do not instantiate the structure for a full-strength proof system; we demonstrate the structure is inhabited by PA arithmetic and state that any proof system meeting the assumption inherits the obstruction.

Together with §8.6's `NormalizationProofSystem`, this gives two complementary sufficient conditions for the obstruction at the proof-system level: *verification involves normalization* (Curry-Howard route) and *verification involves arithmetic* (Cook-Reckhow route). Both route to the same intermediate `EvalRewriteWitness`; the choice between them is about which structural feature of a given proof system is more natural to expose. Neither route is claimed necessary.

---

## 10. The PA GödelSystem Instance

§6 axiomatized the `GodelSystem` structure and proved incompleteness from its axioms. This section takes the remaining step toward a fully grounded formalization: instantiating `GodelSystem` for Peano arithmetic. The scope is deliberately narrow. We describe what is discharged (Phase 1, now complete), what is scaffolded (Phases 2-4, with seven named axioms), and what the scaffolding costs the paper's claims.

### 10.1 What a PA instance requires

A `GodelSystem PATerm` instance must supply twelve fields: `provable`, `neg`, `Formula`, `subst`, `scode`, `fcode`, `decode`, `decode_fcode`, `diagN`, `diagN_spec`, `compose_diag`, `compose_diag_prov`, `compose_diag_neg`. The intellectual content of a PA instance is spread unevenly across these:

- **Trivial for PA**: `provable` and `neg` are Peano's provability predicate and syntactic negation; these are standard objects in any formalization of PA.
- **Discharged combinatorially**: `scode`, `fcode`, `decode`, `decode_fcode`, `diagN`, `diagN_spec`, `subst` are Gödel's 1931 encoding machinery. Doable by unique prime factorization and explicit manipulation; tedious but mechanical.
- **The representability theorem**: `compose_diag`, `compose_diag_prov`, `compose_diag_neg` are the essential technical content of Gödel's 1931 paper. They state that the diagonal function is represented by a PA formula. Formalizing this in Lean is a substantial independent project (Flypitch-scale).

`PAGodelSystem.lean` sets up the combinatorial half and scaffolds the representability half with named axioms.

### 10.2 Phase 1: the Gödel encoding (discharged)

The Gödel encoding via prime factorization:

```lean
def encodeTerm : PATerm → ℕ
  | .zero        => 1
  | .succ t      => 2 ^ (1 + encodeTerm t)
  | .plus  a b   => 3 ^ (1 + encodeTerm a) * 5  ^ (1 + encodeTerm b)
  | .times a b   => 7 ^ (1 + encodeTerm a) * 11 ^ (1 + encodeTerm b)
```

The central lemma is injectivity:

```lean
theorem encodeTerm_injective : Function.Injective encodeTerm
```

The proof reduces to seven small arithmetic facts: `3 ∤ 2^k`, `7 ∤ 2^k`, `7 ∤ 3^x · 5^y`, `3 ∤ 7^x · 11^y`, `pow_two_injective`, `plus_pairing_injective`, `times_pairing_injective`. These were originally axiomatized in the paper's scaffolding. PR #49 discharged all seven as theorems using Mathlib's `Nat.Prime.dvd_of_dvd_pow` (for the non-divisibility facts) and `Nat.factorization` (for the pairing injectivities via a shared `pair_factorization_eq` helper). The encoding-level of `PAGodelSystem.lean` is now axiom-free.

### 10.3 Phases 2-4: seven named axioms

The remaining scaffolding stores seven axioms:

```lean
axiom phase2_decode_inverse : ∀ (φ : PAFormula), decodeFormula φ.code = φ
axiom compose_diag : PAFormula → PAFormula
axiom compose_diag_apply : ∀ (β : PAFormula) (n : ℕ),
    (compose_diag β).apply n = β.apply (diagN n)
axiom paProvable : PATerm → Prop
axiom paNeg : PATerm → PATerm
axiom phase3_compose_diag_provable : ∀ (β : PAFormula) (n : ℕ),
    paProvable ((compose_diag β).apply n) ↔ paProvable (β.apply (diagN n))
axiom phase3_compose_diag_neg_provable : ∀ (β : PAFormula) (n : ℕ), ...
```

Each axiom is a precise mathematical claim corresponding to a standard result in Gödel's 1931 paper or in the classical theory of PA. The three classes match the three sub-issues tracking the work:

| Axioms | Content | Issue |
|---|---|---|
| `phase2_decode_inverse` | The `PAFormula` stub must be replaced with a proper syntactic formula type, and `decode` made a left inverse of `fcode` | #50 |
| `compose_diag`, `compose_diag_apply`, `phase3_compose_diag_provable`, `phase3_compose_diag_neg_provable` | The diagonal function is representable in PA (Gödel's 1931 representability theorem) | #51 |
| `paProvable`, `paNeg` | PA's deductive system: axioms, inference rules, derivability | #52 |

Given these axioms, the `GodelSystem PATerm` instance is constructive:

```lean
noncomputable def paGodelSystem : Diagonal.GodelSystem PATerm where
  provable     := paProvable
  neg          := paNeg
  Formula      := PAFormula
  subst        := fun φ n => φ.apply n
  scode        := encodeTerm
  fcode        := PAFormula.code
  decode       := decodeFormula
  decode_fcode := phase2_decode_inverse
  diagN        := diagN
  diagN_spec   := fun _ => rfl
  compose_diag := compose_diag
  compose_diag_prov := by intro β n; rw [compose_diag_apply]
  compose_diag_neg  := by intro β n; rw [compose_diag_apply]
```

Composing `paGodelSystem` with the machinery of §6 gives: PA is an incomplete theory, modulo the seven axioms. The axioms are the only remaining obligation.

### 10.4 What the scaffolding costs

A reviewer entitled to press on this point will ask: is "PA is incomplete modulo seven axioms" actually a contribution, given that each axiom restates a classical result of Gödel or a fact about PA?

The honest answer in two parts:

First, the paper's central contribution does not depend on discharging these axioms. §§4-9 hold independently: the universal obstruction theorem is proved in `Universal.lean`, the `EvalRewriteWitness` abstraction in `EvalRewrite.lean` and `RootConstructorChange.lean`, the incompleteness proofs in `Diagonal.lean` and `Incompleteness.lean`, and the proof-complexity results in §9 do not rely on the PA instance at all. The PA instance is the extension-of-claim from "any `GodelSystem` is incomplete" to "PA is incomplete, fully machine-checked from primitives." §§4-9 make the former claim; §10 describes what the latter would require.

Second, the axioms are precise. Each is stated at the level of a specific mathematical theorem whose discharge is known to be possible — Flypitch discharged the representability theorem in Lean 3 over thousands of lines. The honest framing: the paper formalizes a framework and names the specific obligations it leaves open. These are future work (issues #50, #51, #52), not mathematical gaps. A reader can inspect the axioms, verify that each is a standard result, and take the scaffolding as a bookkeeping device rather than a substantive claim about PA.

### 10.5 The structural connection between PA and the obstruction

One non-trivial observation from the PA scaffolding is worth preserving in the paper's framing. The representability axioms (`compose_diag_prov`, `compose_diag_neg`) are the *reason* the diagonal lemma holds in PA: they express that PA's formulas can internally represent the `diagN` function, which is the abstract `subst (decode n) n` operation. That abstract operation is the `EvalRewriteWitness` for substitution — a form-changing, meaning-preserving rewrite. The content of the representability theorem is: PA can internalize its own substitution operation, which is already an obstruction witness at the term level (`EvalRewrite.lean`'s `paMulWitness`, `paAddWitness`).

Reading these together: the obstruction's presence in PA's evaluation rules (§4.6 + §5's `EvalRewriteWitness`) and the representability of its internalized form (Phase 3 axioms) are two sides of the same object. The first says PA's multiplication rule changes form; the second says PA can recognize, inside its own language, that this happens. The diagonal sentence exploits both: the structural mismatch between code and meaning is the reason the fixed point exists, and representability is what lets PA express the statement. Neither alone yields incompleteness; their simultaneous presence does.

This observation is not new — it is implicit in Gödel's original construction and explicit in Lawvere 1969. What the formalization contributes is the factoring into two independent structural ingredients, one at the term-rewriting level and one at the theory-internalization level, each axiomatized separately and each with a clear roadmap for discharge.

### 10.6 Where this leaves the paper

After §10, the paper's standing is:

- **Proved, sorry-free**: the universal obstruction (§4), the `EvalRewriteWitness` abstraction (§5), incompleteness from `GodelSystem` / `DiagonalTheory` axioms (§6), the halting problem (§7), beta reduction and cut elimination as obstruction instances (§8), proof-length lower bounds from `SizeBounded` rewrites (§9), `haken_lower_bound` from Haken's combinatorial state-count axiom (§9.5), and the `CookReckhowSystem` structural argument for universal proof-system obstruction (§9.6).

- **Axiomatized at precise boundary points**: seven axioms in `PAGodelSystem.lean` corresponding to Phase 2-4 of the PA instantiation (Gödel's 1931 representability theorem plus the PA deductive system), one axiom in `Resolution.lean` corresponding to Haken's combinatorial state-count bound, three axioms in `HakenBottleneck.lean` corresponding to Haken's bottleneck counting argument, and one axiom in `NaturalProofsEvasion.lean` corresponding to the Razborov-Rudich largeness condition. Twelve named axioms in total.

- **Informal, defended by the collection of instances**: the claim that the encoding obstruction is the *structural reason* each of the six impossibility results holds. The formalization records cohabitation (`obstruction_and_incompleteness` in §6.6, the table in §7.3, the duplicator mechanism in §8.3 and §9.3) without claiming entailment from the obstruction alone.

This is the honest statement of what we have. §11 situates it against related work; §12 lays out the discharge plans for the named axioms and research directions beyond.

---

## 11. Related Work, In Detail

> DRAFTING BLOCKED on careful reading. This section requires substantive engagement with Lawvere 1969, Yanofsky 2003, Flypitch (Han, van Doorn), Statman 1979, and Haken 1985. The skeleton below sets the structural positions the paper must take and flags the specific reading obligations before each subsection can be written. Do not merge §11 into a submission draft until the flagged readings are complete.

### 11.1 Lawvere 1969: categorical fixed-point theorem

> READ BEFORE DRAFTING: F. W. Lawvere, "Diagonal arguments and cartesian closed categories," *Reports of the Midwest Category Seminar IV*, Lecture Notes in Mathematics 92, Springer 1969.

**The position the paper must take:** Lawvere's theorem abstracts Cantor, Gödel, and Tarski into a categorical fixed-point argument in cartesian closed categories. The encoding obstruction refines this in one specific way: by working in a term-rewriting setting rather than at the level of arrows in a CCC, the form-change mechanism becomes an explicit constructor-level fact rather than an existential claim about diagonal arrows. This refinement is the basis for machine-checkability in Lean.

**What to write:** a careful comparison of Lawvere's diagonal construction with `diagN_at_compose` in §6.2. What does Lawvere's theorem *not* say that §6 does say? The honest answer is probably: not much at the level of logical content, but the term-rewriting formulation makes the form-change mechanism explicit and amenable to formalization in a type-theoretic proof assistant. Lawvere's abstraction is more general (any CCC, not just term algebras); ours is more concrete (specific syntactic constructors).

**What NOT to claim:** that this work supersedes or improves on Lawvere. The paper's position is that Lawvere identified the categorical core; we formalize a concrete term-rewriting instance of it in Lean, which is a complementary contribution.

### 11.2 Yanofsky 2003: universal self-reference paradoxes

> READ BEFORE DRAFTING: N. S. Yanofsky, "A universal approach to self-referential paradoxes, incompleteness and fixed points," *Bulletin of Symbolic Logic* 9(3), 2003.

**The position:** Yanofsky extends Lawvere to a broader class of self-referential paradoxes — Russell, Epimenides, Gödel, Tarski, Löb, Rice, halting, Berry — using the same CCC fixed-point machinery. Our `EvalRewriteWitness` is a syntactic counterpart organized around rewrites and encodings rather than diagonal arrows.

**What to write:** a table-based comparison showing which of Yanofsky's instances correspond to which of ours (§6 incompleteness ↔ Yanofsky's Gödel; §7 halting ↔ Yanofsky's Turing/halting; etc.) and which do not (Yanofsky's Russell paradox has no direct `EvalRewriteWitness` analog in our formalization). The paper's position is that Yanofsky's machinery is broader but less formalization-friendly; our machinery is narrower but Lean-formalized.

**What NOT to claim:** that this work is a Lean port of Yanofsky. It is not; our starting point (the Leibniz rewrite in eigenvalue arithmetic) is different, and the unifying abstraction emerged from a different direction. Yanofsky is a convergent prior result, not a source.

### 11.3 Flypitch (Han and van Doorn): Lean 3 incompleteness from PA

> READ BEFORE DRAFTING: J. M. Han and F. van Doorn, "A formal proof of the independence of the continuum hypothesis," *CPP 2020*; and the Flypitch project source code. Relevant comparison point: their formalization of Gödel's representability theorem.

**The position:** Flypitch formalized Gödel's incompleteness in Lean 3, from PA primitives, over ~20,000 lines. Our formalization takes a different organizing principle: rather than deriving incompleteness directly, we derive it as an instance of a universal obstruction that also covers halting, cut elimination, and resolution bounds. Our Phase 1 is discharged, Phases 2-4 are axiomatized at precise boundary points corresponding to Flypitch's representability theorem.

**What to write:** (a) a scope comparison — Flypitch proves more, about incompleteness specifically; we prove less about incompleteness but cover more impossibility results under one abstraction; (b) a Lean-version comparison — Flypitch is Lean 3, we are Lean 4 with Mathlib v4.28.0, so direct porting is not possible but the architectural techniques transfer; (c) an honest statement that Flypitch's representability theorem is the template for discharging issues #50-#52.

**What NOT to claim:** that our formalization matches Flypitch's depth on incompleteness alone. It does not. The paper's contribution is different in kind, not a competitor on the same axis.

### 11.4 Statman 1979 and Orevkov 1979: cut elimination blowup

> READ BEFORE DRAFTING: R. Statman, "Lower bounds on Herbrand's theorem," *Proc. AMS* 75(1), 1979. V. P. Orevkov, "Lower bounds for increasing complexity of derivations after cut elimination" (Russian), *Zapiski Nauchnykh Seminarov LOMI* 88, 1979.

**The position:** Statman and Orevkov independently proved that cut elimination can produce proofs of non-elementary size. The combinatorial content is a specific construction of formula families whose cut-free normal forms are towers of exponentials. §8.5 recovers the *mechanism* of this blowup (size growth under iterated duplication) but not the specific formula families.

**What to write:** a clear statement of what Statman/Orevkov's theorems are, a clear statement of what §8.5 contributes (the structural mechanism via `beta_grows_for_large` composed with iteration), and an explicit separation — we do not formalize Statman's combinatorial construction, we formalize the size-growth mechanism his construction exploits.

**What NOT to claim:** that our framework *derives* non-elementary cut elimination blowup. It does not; Statman's construction provides the specific terms that realize the bound.

### 11.5 Haken 1985: PHP resolution lower bound

> READ BEFORE DRAFTING: A. Haken, "The intractability of resolution," *Theoretical Computer Science* 39, 1985.

**The position:** Haken proved any resolution refutation of PHP(n+1, n) requires at least 2^(n/20) clauses. The proof has a combinatorial core (the bottleneck lemma: any refutation must pass through "wide" clauses whose count is exponential). §9.5 recovers Haken's bound given this combinatorial lemma as input; the lemma itself is `PHP_state_lower_bound_spec`, axiomatized.

**What to write:** (a) a precise statement of Haken's theorem and proof structure; (b) a precise statement of our separation between the length-from-states composition (proved) and the state-count bound (axiomatized); (c) a reference to issue #37 as the tracking item for discharging the state-count axiom from Haken's primitives.

**What NOT to claim:** that the obstruction framework *derives* Haken's PHP bound from scratch. It does not. We recover it modulo Haken's combinatorial input.

### 11.6 Cook-Reckhow 1979: proof complexity foundations

> READ BEFORE DRAFTING: S. A. Cook and R. A. Reckhow, "The relative efficiency of propositional proof systems," *Journal of Symbolic Logic* 44(1), 1979.

**The position:** Cook-Reckhow define proof systems as polynomial-time verifiers. §9.6's `CookReckhowSystem` structure is a direct formalization of their definition plus the assumption that verification factors through a form-changing internal step. This assumption is not part of Cook-Reckhow's original definition; it is a structural hypothesis under which the obstruction fires.

**What to write:** how our structural hypothesis relates to Cook-Reckhow's original definition (namely, it is a refinement, not a requirement), and how §9.6's claim compares to the classical expectation that super-polynomial proof lengths imply P ≠ NP.

### 11.7 Coalgebraic logic

> READ BEFORE DRAFTING: J. J. M. M. Rutten, "Universal coalgebra: a theory of systems," *Theoretical Computer Science* 249, 2000; B. Jacobs, *Introduction to Coalgebra: Towards Mathematics of States and Observation*, Cambridge 2017.

**The position:** Coalgebra studies bisimulation between syntactic and semantic structures. The encoding obstruction's "no injective encoding commutes with evaluation" statement is structurally related but distinct: coalgebraic bisimulation is about behavioral equivalence, while the obstruction is about failure of commutation under an additional encoding step.

**What to write:** a brief comparison noting the adjacent but distinct subject matter. We do not claim a coalgebraic formulation; we note the neighborhood.

**What NOT to claim:** a coalgebraic generalization of our framework. Not formalized; not obviously meaningful without additional structure.

### 11.8 Differential algebra: Ritt and Kolchin

> READ BEFORE DRAFTING: E. R. Kolchin, *Differential Algebra and Algebraic Groups*, Academic Press 1973. J. F. Ritt, *Differential Algebra*, AMS Colloquium Publications 1950.

**The position:** The Leibniz rule (§4.2's `leibnizRewrite`) comes from differential algebra. Ritt and Kolchin develop the algebraic theory of derivations. Part 1 of the `SpectralArithmeticTheory` project (not the focus of this paper) uses the Leibniz rule in a spectral / eigenvalue setting; Part 2 (the universal obstruction, this paper) uses it in a term-rewriting setting.

**What to write:** a short note placing the Leibniz rule in its original algebraic context, and explaining why its term-rewriting presentation is the relevant one for this paper.

---

**Summary of §11's obligations before submission:**

| Citation | Required reading | Status |
|---|---|---|
| Lawvere 1969 | LNM 92 Springer, full paper | not read |
| Yanofsky 2003 | BSL 9(3), full paper | not read |
| Flypitch | Han-van Doorn CPP 2020 + source | partial |
| Statman 1979 | Proc. AMS 75(1) | not read |
| Orevkov 1979 | Zapiski LOMI 88 (Russian) | not read, translation needed |
| Haken 1985 | TCS 39 | partial |
| Cook-Reckhow 1979 | JSL 44(1) | partial |
| Rutten 2000 / Jacobs 2017 | background texts | not required for tone |
| Kolchin / Ritt | background texts | not required for tone |

Until these are read, §11's substantive claims remain speculative. The skeleton records the positions the paper must take and flags reading as prerequisite work. Do not treat §11 as draft-complete without completing the reading list.

---

## 12. Future Directions

We organize this section by tractability rather than by ambition. Three tiers: concrete axiom-discharge work with known techniques (tractable); new bounds that the framework organizes but does not yet derive (medium-term); and genuinely speculative directions toward P vs NP and its known barriers (speculative — explicitly *not* a deliverable). The GitHub issue numbers are the project's live tracking of these items; we include them so the reader can check the current status.

### 12.1 Discharging the twelve named axioms

The formalization contains twelve named axioms at `Obstruction/` boundary points. Each corresponds to a known classical result; none are known to be wrong. Discharging any of them strengthens the paper's claims; none are required for §§4-9.

**PA GödelSystem Phases 2-4** (seven axioms, issues #50-#52). Sub-projects of issue #40, tracked as independent follow-ups. Phase 2 (syntactic formulas + decoding) is estimated at ~2 weeks; Phase 3 (representability of PR functions in PA) is the hard one at 1-2 months and is the Flypitch-scale piece; Phase 4 (PA deductive system) is ~2 weeks. Discharging all three yields a machine-checked derivation of Gödel's first and second incompleteness theorems from PA primitives, through the obstruction framework.

**Haken's state-count (three axioms in `HakenBottleneck.lean`, one in `Resolution.lean`, issue #37).** The `PHP_state_lower_bound_spec` axiom (§9.5) encodes Haken's combinatorial bottleneck argument as an input. Discharging it requires formalizing Haken 1985 from primitives — a multi-month project of independent value, currently the most paper-adjacent medium-term item. The expected deliverable is an axiom-free derivation of `haken_lower_bound` and corresponding statements in `HakenBottleneck.lean`.

**Natural proofs evasion (one axiom in `NaturalProofsEvasion.lean`, issue #39).** The axiom `obstruction_property_not_large` states that the obstruction property does not satisfy the Razborov-Rudich "largeness" condition, hence is not subject to the natural proofs barrier. Discharging this axiom is small in scope (the argument is structural, not combinatorial), and its presence converts the framework's relationship to natural proofs from commentary to theorem. Positioned in §12.3 under barriers.

The paper's framing is that these axioms are *bookkeeping for future work*, not hidden gaps. Each is stated precisely in Lean, each has a known classical proof, and each is tracked as an issue. A reader skeptical of the scaffolding is invited to read any single axiom's statement and confirm that it is not smuggling non-trivial content.

### 12.2 New proof complexity results

§9 recovers Haken modulo his combinatorial input. The framework's value-add is a uniform lens on *any* size-bounded rewrite system, and the natural question is whether that lens produces *new* bounds — not merely re-organizations of known ones.

**Tree-like resolution, Frege, extended Frege (issues #38, #44).** Each of these is a proof system for which classical lower bounds are either open or rely on specialized techniques. The obstruction framework's claim is that length lower bounds for any size-bounded form-changing rewrite system follow from target-size growth. Whether this perspective yields a new bound is a research question, not a resolved one. The framework organizes the question; it does not answer it.

**Trajectory-structure-based bounds (#41).** The observation that `EvalRewriteWitness` comes with both form-change data (blocks encoding) and size-growth data (bounds length) invites a more refined invariant. Can the structure of the *trajectory* — what is preserved and what changes at each step — give sharper bounds than size alone? This is currently speculation; an honest account is that size is the only invariant we have exploited quantitatively.

**Multiplicative-to-additive transformation (#42).** The Leibniz pattern (§4) is specifically multiplication becoming addition under differentiation/evaluation. If this transformation itself is a complexity measure — tracking how many `comp`-to-`add` steps occur in a proof's internal computation — it may provide a structural lower bound mechanism. Currently exploratory.

**Craig interpolation (#43).** Craig interpolation lower bounds (Krajíček, Pudlák) are a known route to proof complexity separations. The framework's relationship to interpolation is untested; the obstruction's structural content may or may not be compatible with interpolation-based lower bounds. Research direction, not planned work.

Each of these items is speculation-colored work: the framework is the organizing principle, not a proof engine that mechanically produces new bounds.

### 12.3 Speculative: P vs NP and its known barriers

A framework that connects encoding obstructions to proof complexity invites the question: does it suggest an approach to P vs NP?

We are explicit that it does not, and that this section is speculation colored by a commitment to stating scope honestly.

**The structural argument.** An NP-complete problem has a verifier; any verifier is a computation; computation has `EvalRewriteWitness` structure (§9.6's two routes); therefore an NP-complete problem's verifier has the obstruction. If the obstruction's quantitative consequences (size growth in trajectories) could be shown to force super-polynomial verification length for NP-complete problems, P ≠ NP would follow. This is the informal claim we state and the informal claim we have not proved.

**The three classical barriers** to separating P from NP (Razborov-Rudich 1994, Baker-Gill-Solovay 1975, Aaronson-Wigderson 2008) apply to large classes of proof techniques. The framework's relationship to each:

- **Relativization (Baker-Gill-Solovay).** The obstruction is about term-rewriting on syntactic term algebras. Relativization is about oracle access. The two domains do not obviously interact: the obstruction is a statement about syntactic encoding regardless of the underlying theory's oracle access. Whether this constitutes non-relativizing content is open; the formalization does not settle it.

- **Natural proofs (Razborov-Rudich).** The obstruction property (form change + semantic preservation) is not plausibly a "largeness" property of Boolean functions in the Razborov-Rudich sense — it is a structural property of rewrite systems, not a statistical property of the function being computed. Issue #39 and `NaturalProofsEvasion.lean` formalize this claim behind a single axiom (`obstruction_property_not_large`); discharging that axiom gives the theorem "the obstruction property is not large, hence not subject to the natural proofs barrier." This is the most concrete barrier-evasion claim and the one most ripe for formalization.

- **Algebrization (Aaronson-Wigderson).** Algebrization generalizes relativization to algebraic extensions. The obstruction's relationship to algebraic extensions is unanalyzed. We make no claim about algebrization.

**What we do claim.** The speculative structural argument is *explicitly a research direction, not a result*. The formalization provides the scaffolding to examine whether the obstruction evades the known barriers (partially, via issue #39) and whether it can be sharpened into a complexity-class separation (not known). The paper's contribution to this question is to state it clearly, not to answer it.

**What a reviewer should read into §12.3.** The paper's structural claim stops at "incompleteness, halting, cut elimination, and Haken's resolution bound share the same obstruction pattern." Extensions of this claim to P vs NP are speculative and separated from the paper's substantive content. We prefer a paper whose quantitative claims are defensible and whose speculative claims are openly labeled over a paper whose speculation is hidden.

### 12.4 Other domains

Three further directions are natural given the formalization:

**Binding theory (substitution).** Substitution in any language with variable binding is a form-changing rewrite (§8.1's lift/subst). A deeper formalization of why substitution changes form — not merely that it does in concrete cases — would sharpen the universality claim. Currently substitution appears as one instance among several; a binding-theoretic account would connect it to the structure of contexts and capture-avoiding reduction more abstractly.

**Sequent calculus.** §8's Curry-Howard route identifies beta reduction with cut elimination on natural deduction proofs. Sequent calculus is the classical alternative formulation, with cut elimination as its own primitive operation. Formalizing a sequent calculus and instantiating `NormalizationProofSystem` would provide a second proof-system instance and make the §8.6 claim concrete beyond lambda calculus.

**Type theory and dependent types.** The obstruction on beta reduction carries to polymorphic and dependently typed systems. System F and the Calculus of Constructions admit non-terminating terms (via polymorphism) that are closer analogs of Ω (§8.3). A dependently typed proof system inherits the obstruction through the same Curry-Howard route. This is low-lift follow-on work.

### 12.5 What future work does not address

The paper deliberately does not pursue:

- **P vs NP independence.** The formalization's structural argument is a research direction, not a deliverable. No formalization claim is made about independence of P vs NP from PA or ZFC.
- **New explanations of incompleteness.** Gödel 1931 remains the source text. Our work formalizes a structural perspective that is implicit in Lawvere 1969 and makes it machine-checkable; it does not claim new mathematical content about incompleteness.
- **Replacing or reframing Haken's / Statman's / Orevkov's work.** We recover these results modulo their combinatorial inputs. The classical theorems stand; the framework provides an alternative organizing principle for viewing them.

---

## 13. Conclusion

> TODO — ~1 page. Draft after everything else.
