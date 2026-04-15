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

> TODO — ~3 pages. The `Diagonal.lean` + `Incompleteness.lean` pair.

---

## 7. The Halting Problem

> TODO — ~1 page. Short section; `Halting.lean` is compact.

---

## 8. Beta Reduction and Curry-Howard

> TODO — ~3 pages. `BetaReduction.lean` + `CurryHoward.lean`. Statman 1979 must be read before drafting.

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
