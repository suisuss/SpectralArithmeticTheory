# The Encoding Obstruction: A Structural Characterization of Self-Referential Impossibility, Formalized in Lean 4

**Status:** draft in progress. Follow the ordering in `outline.md`. Each section has a `> TODO` marker if not yet drafted.

> **REVISION STATUS (2026-06-10, final pass complete).** All sections
> now reflect the June results; figures measured at the repository
> head (17 core modules, 5,721 lines, six axioms, zero sorries).
> REMAINING BEFORE SUBMISSION — author obligations: (a) §11 is now
> DRAFTED from verified sources (2026-06-10), with its own remaining
> list: page-level reading of Lawvere/Yanofsky/Popescu-Traytel,
> Orevkov bibliographic data, and the §11.9 full-abstraction
> proximity check; (b) §3 informal review still TODO; (c) an author
> voice pass over the whole; (d) venue formatting and the
> artifact-evaluation package; (e) re-run the CLAUDE.md greps at
> submission time and refresh the measured figures.

**Target venue:** CPP 2027 or ITP 2027.

**Working paper scope:** 17 core `Obstruction/` modules, 5,721 lines (measured 2026-06-10 at the repository head): the original 12 plus `TheoryInterfaces`, `Bisimulation`, `UniversalBisimulation`, `QuotationCost`, and `FoundationBridge`. Zero sorries; six named axioms at boundary points, each a satisfiable proposition over opaque data with its interpretation documented. Scaffolding and extensions are cited but not headline.

---

## 1. Abstract

Several classical impossibility results — Gödel's incompleteness theorems, Turing's halting problem, Statman's cut elimination blowup, Haken's pigeonhole resolution bound — share a structural mechanism: a rewrite that changes syntactic form while preserving semantic content, confronted with an encoding that must remain injective. We formalize this mechanism in Lean 4 and prove the theorem that makes it load-bearing: an observable of a self-encoding term algebra supports a bisimulation between syntax and semantics if and only if it is extensional (factors through evaluation). The classical encoding obstruction is the intensional extreme of this boundary — injective codings are maximally intensional — and the impossibility results instantiate its intensional side, machine-checked six times across term algebras, PA arithmetic, self-reference, program execution, beta reduction, and resolution. A quantitative companion fixes the boundary's cost: every compositional Gödel coding pays super-polynomial quotation overhead along observation trajectories, while an exactly matching counterexample shows arbitrary injective codings need not — compositionality, not injectivity, is what forces codes to pay for form. The abstract `GodelSystem` interface from which we prove the diagonal lemma and both incompleteness theorems is instantiated by genuine Peano Arithmetic via the FormalizedFormalLogic Foundation library, with the instantiated diagonal lemma depending on the standard Lean axioms alone. The development is sorry-free; six named axioms remain at boundary points, each satisfiable with its satisfying interpretation documented. We position the work against Lawvere, Yanofsky, Popescu-Traytel's abstract incompleteness, and the Foundation library, and frame the complexity-theoretic horizon as limitation theorems about formalized calculi — the genre of the classical barriers — rather than as an approach to separations.

---

## 2. Introduction

Several classical impossibility results share a structural feature that is rarely stated explicitly. Gödel's first incompleteness theorem relies on the Gödel sentence `G`, constructed by self-substitution: the code of `G` appears inside `G` as an argument to the provability predicate, and the resulting sentence is undecidable. Turing's halting problem relies on the diagonal program `D`, which consults a hypothetical halting decider on `D(code D)` and does the opposite. Statman's non-elementary cut elimination blowup relies on lambda terms whose normal form is exponentially larger than the original, obtained by iterated application of a duplicating combinator. Haken's pigeonhole resolution lower bound relies on showing that any refutation must pass through a state set of exponential size.

These four results have been understood as "diagonal arguments" since Lawvere 1969 identified their common categorical core. What they share at a more concrete level — the level at which a proof assistant can record them — is a combination of two ingredients: a rewrite that changes syntactic form while preserving semantic content, and an encoding that must remain injective. Whenever a rewrite changes a term's identity as an inductive value, no injective encoding can commute with it. This is a trivial consequence of injectivity once the hypothesis is stated; what is non-trivial is recognizing that the hypothesis holds in each of these four cases and that it supplies the structural load-bearing content of the classical arguments.

### The paper's contribution

We formalize this observation in Lean 4 as an abstraction called `EvalRewriteWitness`: a rewrite that is form-changing and meaning-preserving, paired with a term on which both conditions are witnessed. The obstruction — that no injective encoding can commute with a form-changing rewrite — follows from the definition of injectivity in one line. The work of the formalization is to show that six independent term algebras admit `EvalRewriteWitness` instances and that the resulting obstruction suffices to recover the classical impossibility results, with explicit attribution of which parts of each classical argument are supplied by the framework and which remain domain-specific.

The paper claims, in summary:

1. **The bisimulation boundary theorem** (§5b): an observable of a self-encoding term algebra supports a bisimulation between the syntactic and semantic dynamics if and only if it is extensional; the observable hierarchy extensional ⊊ rewrite-invariant ⊊ all is strict with machine-checked witnesses, and injectivity is maximal intensionality. Proved both for the concrete spectral algebra and universally over all signatures and Leibniz algebras.

2. **The quotation cost pair** (§5c): every compositional coding — the class containing all standard Gödel codings — pays super-polynomial quotation overhead along the canonical observation trajectory (doubly exponential codes against singly exponential semantic content), and an explicit injective counterexample shows the compositionality hypothesis is exactly necessary.

3. A Lean 4 abstraction (`EvalRewriteWitness`) capturing the structural pattern shared by diagonal arguments — now positioned as the intensional side of the boundary — with a formal proof that non-trivial semantics alone is insufficient, and six machine-checked instances (§§4-9).

4. A proof-length lower bound framework (`SizeBounded` + obstruction) that recovers Haken 1985's PHP lower bound, given his combinatorial bottleneck lemma as an explicit axiom, and organizes Statman's non-elementary cut elimination bound within the same framework.

5. **A `GodelSystem` instance for genuine Peano Arithmetic** (§10.7), built on the FormalizedFormalLogic Foundation library: decoding is a true `Encodable` decode, representability is discharged by the arithmetic fixed-point theorem, and the instantiated diagonal lemma depends on the standard Lean axioms alone. The toy PA instance with its scaffolding axioms is retained as the worked example but is no longer load-bearing.

The development is sorry-free. Six named axioms sit at boundary points (Haken's combinatorial state-count and width lemma, the Razborov-Rudich largeness conjecture, and the toy PA instance's two coding hooks); each is a satisfiable proposition over opaque data, with a satisfying interpretation documented at the declaration — a convention adopted after an audit found three earlier placeholder-based axioms refutable (§10.4). Their discharge is tracked as follow-up work and is not required for the paper's central claims.

### What the paper is and is not

Claims we make carefully:

- **Unification via formalization.** The six classical results share a common structural mechanism, and the sharing is made visible by a single Lean abstraction instantiated six times.
- **Honest recovery of classical bounds.** Haken's PHP bound and Statman's cut elimination blowup are recovered modulo their combinatorial inputs; the framework provides the structural composition, not the inputs.
- **A roadmap for full discharge.** The PA instance makes explicit what would be required to derive incompleteness from PA primitives through the framework; the required work is factored and tracked.

Claims we do not make:

- **New mathematical content.** The universal obstruction, at the abstract level, is logically almost trivial; its novelty is in the formalization and in the observation that a specific structural hypothesis (form-changing rewrite) is load-bearing across the instances.
- **New proof complexity results.** We recover Haken modulo his inputs and situate Statman; we do not prove new lower bounds.
- **P vs NP or its independence.** §12.3 records the structural argument as a research direction, openly labeled, not as a result.
- **Re-proving incompleteness from primitives.** The concrete mechanized lineage — Shankar, O'Connor, Harrison, Paulson — and, in Lean 4, the FormalizedFormalLogic Foundation library formalize incompleteness from representability up; we do not redo that work. Our real-PA instance (§10.7) *imports* Foundation's fixed-point theorem rather than re-deriving it; the contribution is the converse direction — an independent library's PA instantiates our abstraction, evidence that the abstraction is the one real theories satisfy.

### Organization

§3 reviews the encoding obstruction informally and positions it relative to the categorical and formalization literature. §4 presents the universal encoding obstruction on parameterized term algebras, and §5 extracts the `EvalRewriteWitness` abstraction, including the formal argument that non-trivial semantics alone is insufficient. §5b proves the paper's central theorem — the bisimulation boundary — and §5c its quantitative companion, the quotation cost pair. §6 instantiates the intensional side for incompleteness (including the degeneracy of the over-abstracted alternative), §7 for halting, §8 for beta reduction and cut elimination. §9 combines the abstraction with size-bounded rewrites to recover proof-length lower bounds, including Haken's PHP bound. §10 grounds `GodelSystem` twice: the toy instance whose audited missteps fixed the project's axiom conventions, and the real instance over Foundation's PA (§10.7). §11 situates the paper against Lawvere, Yanofsky, the mechanized-incompleteness lineage, Popescu-Traytel's abstract account, Foundation, Statman, Orevkov, Haken, and Cook-Reckhow. §12 outlines future directions under the limitation-theorems framing. §13 concludes.

---

## 3. Background and Related Work

> TODO — informal review section; draft after §11's positions, from which it can now borrow. ~2 pages per outline.

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

## 5b. The Bisimulation Boundary

*(Added 2026-06-10; Lean source: `Bisimulation.lean`, `UniversalBisimulation.lean`.)*

§§4-5 prove that no injective encoding commutes with a form-changing rewrite — a one-line consequence of injectivity. The natural objection is that the theorem is about strict equality of codes, where injectivity decides everything. This section answers the objection by moving to the equivalence under which the question has content: bisimulation.

**Observation systems.** An observation system is a carrier with a step function and an output map; a bisimulation between two systems over a shared output type is a relation that matches outputs and is closed under stepping — the standard coalgebraic notion for the functor X ↦ O × X. The syntactic system steps a term by applying `obs` and unfolding it through the Leibniz rewrite (`synStep`); the semantic system steps a state by `obs` itself. The syntactic step implements the semantic one through evaluation: `eval (synStep t) = obs (eval t)`.

**Tier 1 (positive).** The graph of `eval` is a bisimulation between the syntactic system observed through `eval` and the semantic system observed directly (`evalGraphBisim`), and for any code/decode retraction the Gödel-code dynamics are bisimilar to the semantics (`codeBisim`). The eval-quote square commutes up to bisimulation — quotation is behaviorally free — when observation is extensional.

**Tier 2 (the boundary).** That qualifier is exact. An observable `o` of syntax supports a bisimulation relating every term to its evaluation if and only if `o` is extensional, i.e. factors through `eval` (`supportsBisim_iff_extensional`). Strictness is machine-checked at both inclusions of the hierarchy extensional ⊊ rewrite-invariant ⊊ all observables: the root constructor is not even rewrite-invariant (the form-change phenomenon of §4, relocated to the observable side); syntactic equality with `f₀` is rewrite-invariant but separates terms every model identifies; and any injective coding fails extensionality outright (`injective_no_bisim`). Injectivity is precisely maximal intensionality. The same characterization holds at the generality of §4 — over every constant signature and every Leibniz algebra (`supportsBisimF_iff_extensionalF`) — where the witness pair is free: a term and its Leibniz rewrite are distinct yet evaluation-equal in every algebra.

**What this changes.** The encoding obstruction of §§4-5 is no longer a fact about codes failing to be clever: it is the extreme point of a characterized boundary. The impossibility results of §§6-9 instantiate the intensional side of that boundary. This is the theorem that makes the abstraction load-bearing rather than descriptive.

## 5c. Quotation Cost: the Quantitative Boundary

*(Added 2026-06-10; Lean source: `QuotationCost.lean`.)*

The boundary of §5b is qualitative. Its quantitative companion fixes what crossing the eval-quote square costs.

**The trajectory.** The canonical observation trajectory iterates `synStep` from `f₂ = compose(f₁, f₁)`. Its even stages have an exact closed form: `trajectory (2m) = dup^m(f₂)` where `dup a = oplus(obs a, obs a)` — duplication towers, with f₁-leaf count exactly `2^(m+1)`. Semantically, `eval (trajectory j) = 2^j · f₂`: the meaning at stage j is the number 2^j, j+1 bits of content.

**The separation.** A compositional coding — computed bottom-up with pairings dominating the product, the floor satisfied by every standard Gödel coding — must pay for every f₁ leaf: `encode (trajectory (2m)) ≥ 2^(2^(m+1))`, doubly exponential. Hence no polynomial in the semantic value bounds the code (`quotation_overhead_superpolynomial`). Quotation is behaviorally free (§5b) and quantitatively ruinous: the code tracks form, form grows doubly exponentially, meaning grows singly.

**The sharpness witness.** The hypothesis is exactly necessary. An explicit injective coding (`compressedCode`) enumerates the trajectory on the even numbers — codes at most 2j at stage j, logarithmic in the semantic value — refuting the generalization of the separation to arbitrary injective codings (`compositionality_necessary`). Trajectory membership is decidable by bounded search (`trajectory_index_le`), so the counterexample is computable in principle, making it a fair refutation of the conjecture this section descends from, which had quantified over all primitive recursive injections. Compositionality, not injectivity, is what forces a code to pay for syntactic structure.

**Genre.** A limitation theorem about a formalized class of techniques, together with the exact sharpness witness for its class boundary, is the structure of the classical complexity barriers; §12.3 develops this positioning.

---

## 6. Self-Reference and Incompleteness

The first instance where the abstraction of §§4-5 buys something non-trivial is Gödel's first and second incompleteness theorems. The formalization originally followed two parallel paths: one in `Diagonal.lean` that axiomatizes the low-level Gödel-encoding primitives and proves the diagonal lemma as a theorem, and one in `Incompleteness.lean` that axiomatizes the diagonal property directly. Both are machine-checked and sorry-free — but only the first survives contact with real theories: §6.5 records the machine-checked proof that the second path's hypothesis is unsatisfiable for every nontrivial theory. We describe both, the degeneracy included, then relate them back to §§4-5.

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

These are the *genuine* primitives of Gödel encoding. In PA they correspond to Gödel's 1931 representability theorem (for `compose_diag_prov`, stated at the self-application point — the only instance the diagonal lemma uses, and the only one real theories satisfy; see §10.7) and to injective coding with a decode (for `decode_fcode`). The structure is grounded twice in §10: a toy instance whose scaffolding history fixed our axiom conventions, and the real instance over Foundation's PA, where every field above is either defined or proved.

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

`DiagonalTheory` trades precision for brevity — and the trade fails, instructively. Its `diag` field quantifies over *arbitrary* sentence transformers `P : Sentence → Sentence`, not formula-definable ones, and that is too strong for any real theory: `FoundationBridge.diagonalTheory_trivial` proves, machine-checked, that every `DiagonalTheory` instance is trivial — either everything is provable or nothing is. (Take `P s := if provable s then f else t` for a provable `t` and unprovable `f`; both diag directions then contradict.) Real theories satisfy the diagonal lemma only for formulas, which is exactly the discipline `GodelSystem`'s `compose_diag : Formula → Formula` enforces.

We retain `DiagonalTheory` and its incompleteness proofs as a cautionary exhibit: the proofs are valid conditional theorems, but their hypothesis is unsatisfiable for every nontrivial theory, so this path to incompleteness is vacuous. The defect was found the same way three earlier refutable axioms were found (§10.4) — by testing the abstraction against a real instantiation. `Diagonal.lean`'s `GodelSystem` is the abstraction real theories satisfy, as §10.7 demonstrates for genuine PA.

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

This gives, from a single set of hypotheses: (a) an `EvalRewriteWitness` exhibits the eval-quote failure on the sentence type, and (b) the theory is incomplete. We state plainly what the proof term is: a pair of two independently proved facts. The theorem records cohabitation, not derivation — no implication from the obstruction to incompleteness is formalized here. The load-bearing connection lives elsewhere, in §5b's boundary theorem: the encoding obstruction is the intensional extreme of a characterized boundary, and the diagonal construction operates on that intensional side.

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

§6 axiomatized the `GodelSystem` structure and proved incompleteness from its axioms. This section grounds it twice over. §§10.1-10.6 describe the self-contained toy instance over a four-constructor term language: Phase 1 (the Gödel encoding and its injectivity) is discharged, the deeper phases are scaffolded as satisfiable named axioms, and §10.4 records what an audit of that scaffolding taught about stating axioms at all. §10.7 — added 2026-06-10 — supersedes the scaffolding for the thesis: `GodelSystem` is instantiated by genuine Peano Arithmetic via the FormalizedFormalLogic Foundation library, with the instantiated diagonal lemma depending on the standard Lean axioms alone. The toy instance remains as the worked example whose missteps motivated the conventions; its axioms are no longer load-bearing.

### 10.1 What a PA instance requires

A `GodelSystem PATerm` instance must supply thirteen fields: `provable`, `neg`, `Formula`, `subst`, `scode`, `fcode`, `decode`, `decode_fcode`, `diagN`, `diagN_spec`, `compose_diag`, `compose_diag_prov`, `compose_diag_neg`. The intellectual content of a PA instance is spread unevenly across these:

- **Trivial for PA**: `provable` and `neg` are Peano's provability predicate and syntactic negation; these are standard objects in any formalization of PA.
- **Discharged combinatorially**: `scode`, `fcode`, `decode`, `decode_fcode`, `diagN`, `diagN_spec`, `subst` are Gödel's 1931 encoding machinery. Doable by unique prime factorization and explicit manipulation; tedious but mechanical.
- **The representability theorem**: `compose_diag`, `compose_diag_prov`, `compose_diag_neg` are the essential technical content of Gödel's 1931 paper. They state that the diagonal function is represented by a PA formula. Formalizing this in Lean is a substantial independent project (compare Paulson 2014 in Isabelle, O'Connor 2005 in Coq, and Foundation's Lean 4 development).

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

### 10.3 The scaffolding, its audit, and the repaired form

*(Rewritten 2026-06-10.)* The April scaffolding stored seven axioms for Phases 2-4. An audit found the set inconsistent. The instructive exhibit:

```lean
-- April form — REFUTABLE, kept here as the cautionary example:
axiom phase2_decode_inverse : ∀ (φ : PAFormula), decodeFormula φ.code = φ
```

`decodeFormula` was a concrete stub (constant `apply`, free `code` field), and `code` is not injective on `PAFormula` — two formulas sharing a code but differing in `apply` refute the axiom outright. Two further axioms in the wider scaffolding had the same shape of defect (a largeness conjecture stated over a `True`-placeholder definition; a width lemma with a placeholder hypothesis ranging over phantom proofs). All three were derivably false; `False`-derivation check files confirmed it against the pre-repair tree.

The repair fixed a convention the project now states as policy: **axioms are reserved for satisfiable propositions over `opaque` data — never for properties of concrete placeholder definitions — and each axiom's declaration documents an interpretation satisfying it jointly with the rest.** Under that convention the toy instance carries exactly two axioms:

```lean
opaque decodeFormula : ℕ → PAFormula
axiom decodeFormula_code (n : ℕ) : (decodeFormula n).code = n
opaque compose_diag : CodedFormula → CodedFormula
axiom compose_diag_apply (β : CodedFormula) (n : ℕ) :
    (compose_diag β).val.apply n = β.val.apply (diagN n)
```

with `provable`/`neg` as opaque data, the instance built over the `CodedFormula` subtype (decode-canonical formulas, on which `code` *is* injective, making `decode_fcode` a theorem), and the former phase-3 axioms derived as theorems from `compose_diag_apply`. The all-zero stub decode interprets both axioms, witnessing joint satisfiability.

### 10.4 What the scaffolding episode costs — and teaches

A reviewer entitled to press will ask two questions. First: is "PA is incomplete modulo scaffolding axioms" a contribution? The answer is that the paper no longer makes that claim — §10.7's real instance carries it on standard Lean axioms, and the toy instance's two remaining axioms are not load-bearing for anything in §§4-9 or §10.7. Second: why keep a section about axioms that were once stated falsely? Because the episode is part of the paper's evidence. The defects were caught by the method the paper advocates — testing abstractions against instantiation — and the same method subsequently caught the `DiagonalTheory` degeneracy (§6.5) and the over-quantified representability field (§10.7). A formalization paper that presents only the final clean state hides exactly the information a reader adopting these techniques needs: where the failure modes are and which discipline finds them.

### 10.5 The structural connection between PA and the obstruction

One non-trivial observation from the PA scaffolding is worth preserving in the paper's framing. The representability axioms (`compose_diag_prov`, `compose_diag_neg`) are the *reason* the diagonal lemma holds in PA: they express that PA's formulas can internally represent the `diagN` function, which is the abstract `subst (decode n) n` operation. That abstract operation is the `EvalRewriteWitness` for substitution — a form-changing, meaning-preserving rewrite. The content of the representability theorem is: PA can internalize its own substitution operation, which is already an obstruction witness at the term level (`EvalRewrite.lean`'s `paMulWitness`, `paAddWitness`).

Reading these together: the obstruction's presence in PA's evaluation rules (§4.6 + §5's `EvalRewriteWitness`) and the representability of its internalized form (Phase 3 axioms) are two sides of the same object. The first says PA's multiplication rule changes form; the second says PA can recognize, inside its own language, that this happens. The diagonal sentence exploits both: the structural mismatch between code and meaning is the reason the fixed point exists, and representability is what lets PA express the statement. Neither alone yields incompleteness; their simultaneous presence does.

This observation is not new — it is implicit in Gödel's original construction and explicit in Lawvere 1969. What the formalization contributes is the factoring into two independent structural ingredients, one at the term-rewriting level and one at the theory-internalization level, each axiomatized separately and each with a clear roadmap for discharge.

### 10.6 Where this leaves the paper

After §10, the paper's standing is:

- **Proved, sorry-free**: the universal obstruction (§4), the `EvalRewriteWitness` abstraction (§5), incompleteness from `GodelSystem` / `DiagonalTheory` axioms (§6), the halting problem (§7), beta reduction and cut elimination as obstruction instances (§8), proof-length lower bounds from `SizeBounded` rewrites (§9), `haken_lower_bound` from Haken's combinatorial state-count axiom (§9.5), and the `CookReckhowSystem` structural argument for universal proof-system obstruction (§9.6).

- **Axiomatized at precise boundary points** (2026-06-10 census): two axioms in `PAGodelSystem.lean` (the toy instance's coding hooks, non-load-bearing after §10.7), one in `Resolution.lean` (Haken's combinatorial state-count), two in `HakenBottleneck.lean` (the bottleneck width lemma over valid refutations, and the counting spec over an opaque count), and one in `NaturalProofsEvasion.lean` (the Razborov-Rudich largeness conjecture, re-scoped per §12.3). Six named axioms in total, each satisfiable over opaque data with the interpretation documented at the declaration.

- **Informal, defended by the collection of instances**: the claim that the encoding obstruction is the *structural reason* each of the six impossibility results holds. The formalization records cohabitation (`obstruction_and_incompleteness` in §6.6, the table in §7.3, the duplicator mechanism in §8.3 and §9.3) without claiming entailment from the obstruction alone.

This is the honest statement of what we have. §11 situates it against related work; §12 lays out the discharge plans for the named axioms and research directions beyond.

---


### 10.7 The real instance: GodelSystem for genuine PA via Foundation

*(Added 2026-06-10; Lean source: `FoundationBridge.lean`.)*

The FormalizedFormalLogic Foundation library provides first-order arithmetic with genuine Gödel coding, the arithmetic fixed-point theorem, and Gödel-Rosser incompleteness. Pinning it as a dependency, `paGodelSystemF : GodelSystem (Sentence ℒₒᵣ)` instantiates our abstraction with real PA:

- `scode`/`fcode` are Foundation's Gödel quote, which over the standard model is `Encodable.encode`;
- `decode` is the genuine `Encodable` decode — `decode_fcode`, the field whose toy counterpart was once a refutable axiom (§10.4), is a theorem about real coding;
- `compose_diag` is Foundation's `diag`, and the representability field is discharged by the fixed-point theorem of arithmetic.

One adjustment to the abstraction was required, and it is a finding: `compose_diag_prov` originally demanded the diagonal equivalence at every natural number, which no real theory satisfies — at numbers coding no formula, a concrete decode bears no relation to the theory's internal substitution. The diagonal lemma only ever uses the self-application instance, the fields were weakened to exactly that, and the fixed-point theorem delivers exactly that. This is the recurring lesson of the project stated once more: abstractions calibrated against real instances, not intuition.

The instantiated diagonal lemma, `pa_diagonal_lemma`, runs our §6 construction on Foundation's PA. Its `#print axioms` output is `propext`, `Classical.choice`, `Quot.sound` — the standard Lean axioms; not even Foundation's own pending Δ₁-definability axioms enter the closure, because the fixed-point theorem's proof is semantic. Separately, our `FormalTheory` abstraction is instantiated with PA (`paTheory`), its consistency proved by soundness over ℕ (standard axioms only), and an undecidable sentence obtained from Foundation's Gödel-Rosser theorem (`paTheory_incomplete`, which carries exactly one upstream axiom, `PA_delta1Definable`, reported per our transparency convention).

Engineering note for replicators: Foundation's compiled modules and the full `Mathlib.Tactic` closure carry duplicate auto-generated equation lemmas and cannot be loaded into one environment; the bridge is therefore an import-leaf library, with the interface structures extracted to an import-free module. On the narrow axis of machine-checked incompleteness, Foundation (like the Isabelle and Coq developments before it) is deeper than our toy scaffolding ever aimed to be; the contribution here is the converse direction — an independent library's PA instantiates *our* abstraction, confirming the abstraction is the one real theories satisfy.

## 11. Related Work, In Detail

> STATUS (2026-06-10): drafted from verified sources. Citations checked
> against publisher/arXiv/AFP records; the Flypitch miscitation in
> earlier drafts (it is the CH-independence project, not an
> incompleteness formalization) is corrected throughout. REMAINING
> AUTHOR OBLIGATIONS: page-level reading of Lawvere's TAC reprint,
> Yanofsky's full text, and Popescu-Traytel's JAR paper (AFP entry
> consulted; journal version paywalled); exact bibliographic data for
> Orevkov's cut-elimination bounds; and the §11.9 proximity check
> against full-abstraction results.

### 11.1 Lawvere 1969: the categorical fixed-point theorem

Lawvere, "Diagonal arguments and cartesian closed categories" (Lecture Notes in Mathematics 92, 1969, 134-145; reprinted with author commentary in TAC Reprints). The theorem: in a cartesian closed category, if `f : A → B^A` is weakly point-surjective, every endomorphism `g : B → B` has a fixed point — with Cantor, Gödel, and Tarski as contrapositive instances. This is the conceptual ancestor of everything in this paper, and the division of labor is clean: Lawvere's theorem explains why fixed points *exist* once self-application is available; it is silent about the syntactic mechanism that makes self-application costly. Our contribution lives in that silence. At the level of CCC arrows, the form-change content of evaluation is invisible — uncurrying does not record that the Leibniz step replaces an `obs` root with an `add` root. Working in term algebras makes form change a constructor-level fact, dischargeable by `simp`, and the boundary theorem (§5b) then asks a question Lawvere's setting cannot pose: *which observations* of the syntax-semantics pair are mutually coherent. The answer — exactly the extensional ones — is a complement to the fixed-point theorem, not a refinement of it.

### 11.2 Yanofsky 2003: the scheme without the category theory

Yanofsky, "A universal approach to self-referential paradoxes, incompleteness and fixed points" (Bulletin of Symbolic Logic 9(3), 2003, 362-386; arXiv:math/0305282), broadens Lawvere's scheme across the semantic paradoxes, computability, complexity, and formal language theory, in deliberately elementary dress. Yanofsky demonstrates breadth by exhibition; nothing is machine-checked, and the instances share a scheme rather than satisfying a characterized condition. Our six instances upgrade exhibition to verification, and the unification from a shared scheme to a boundary with a strictness hierarchy and a price (§5c). Where Yanofsky's survey gestures at complexity theory, §12.3 takes the disciplined version of that gesture: limitation theorems about formalized technique-classes.

### 11.3 Mechanized incompleteness: the concrete lineage

Machine-checked incompleteness has a four-decade history: Shankar (1986, Nqthm), O'Connor (2005, Coq — Gödel-Rosser essential incompleteness), Harrison (2009, HOL Light), and Paulson (2014, Isabelle — both theorems, over hereditarily finite sets following Świerczkowski; the first mechanization of the second theorem). In Lean 4, the FormalizedFormalLogic Foundation library (§11.5) is the deepest arithmetic development. We record a correction: earlier drafts of this paper cited the Flypitch project (Han and van Doorn) as a Lean incompleteness formalization; Flypitch is the formalization of the independence of the continuum hypothesis — first-order logic infrastructure, completeness, and forcing — and makes no incompleteness claim. We do not compete with the concrete lineage on depth: our incompleteness content is interface-level (§6), and the concrete arithmetic work in §10.7 is imported, not re-proved.

### 11.4 Popescu and Traytel: abstract incompleteness, formally verified

The closest formal neighbor to our `GodelSystem` is Popescu and Traytel's abstract account of the incompleteness theorems (IJCAR 2019; journal version "Distilling the Requirements of Gödel's Incompleteness Theorems with a Proof Assistant", J. Automated Reasoning 2021; AFP entries from 2020). They formalize, in Isabelle, sufficient conditions for both incompleteness theorems over a partially specified logic — distilling provability, representability, and derivability-condition assumptions — including Rosser's variant of the first theorem and Jeroslow's of the second, with two concrete instantiations over hereditarily finite sets. As abstract incompleteness, their account is more thorough than ours: we have no derivability conditions and no Rosser variant at the interface level. The differences that remain ours: the interface sits under a characterized boundary (§5b) that positions incompleteness as one instance of the intensional side; the instantiation in §10.7 is by an *independent* library's arithmetic, which tests the abstraction rather than the instantiator; and we document the failure modes of over-abstraction as results — the `DiagonalTheory` degeneracy (§6.5) is precisely a non-sufficiency theorem of the kind a distillation program needs, found by instantiation pressure. We regard their work and ours as the same genre approached from opposite ends: they distill downward from the classical proofs; we built upward from a rewriting obstruction and report where the tower had to be corrected.

### 11.5 The FormalizedFormalLogic Foundation library

Foundation is this paper's most important formal dependency: §10.7's instance is built on it, pinned at a specific revision, with the axiom closure of every imported result reported. Three points, precisely. First, the dependency direction: their PA instantiates our abstraction; the evidence produced is about the abstraction's fitness, not about their theorems, which we import. Second, the engineering boundary, recorded for replicators: Foundation's compiled modules and the full Mathlib tactic closure carry duplicate auto-generated equation lemmas and cannot share an environment; bridges must be import-leaf libraries with interface structures extracted to minimal-import modules. Third, the transparency ledger: `pa_diagonal_lemma` closes over the standard Lean axioms alone, while `paTheory_incomplete` additionally carries Foundation's one pending Δ₁-definability axiom — both facts reported rather than averaged.

### 11.6 Statman and Orevkov: the cost of normalization

Statman, "The typed λ-calculus is not elementary recursive" (Theoretical Computer Science 9(1), 1979, 73-81): deciding β-convertibility of typed terms is not elementary, the canonical source of non-elementary normalization growth; Orevkov's lower bounds on proof lengthening after cut elimination (Zapiski LOMI, 1979; English translation in J. Soviet Mathematics — exact bibliographic data to be verified) are the sequent-calculus counterpart. Our §8 organizes this material rather than extending it: beta reduction is an `EvalRewriteWitness`, the duplicator's growth is trajectory divergence, and Curry-Howard transports both to cut elimination. The non-elementary inputs are theirs; the uniform structural frame is the contribution.

### 11.7 Haken: the resolution lower bound

Haken, "The intractability of resolution" (Theoretical Computer Science 39, 1985, 297-308): pigeonhole refutations require exponential size. §9 recovers the bound with the combinatorial core axiomatized over valid refutations, and the attribution explicit: the framework supplies length-from-states; Haken supplies the states. The planned discharge route (issue #37) is the Ben-Sasson-Wigderson width method rather than the original bottleneck counting, chosen for its formalization-friendly induction.

### 11.8 Cook and Reckhow: the frame we presuppose

Cook and Reckhow, "The relative efficiency of propositional proof systems" (Journal of Symbolic Logic 44(1), 1979, 36-50), defines the proof-system abstraction and the simulation order under which proof complexity is organized. Our length-lower-bound framework operates below that abstraction — on the rewrite dynamics of a single system's proof states — and makes no simulation claims. The Cook-Reckhow frame becomes load-bearing only in §12.3's program, where limitation theorems over reasoning calculi are the stated horizon.

### 11.9 Coalgebraic logic and the full-abstraction proximity check

Rutten's universal coalgebra (Theoretical Computer Science 249(1), 2000, 3-80) supplies the bisimulation vocabulary of §5b; Turi and Plotkin's bialgebraic semantics (LICS 1997) is the classical synthesis of syntax-as-algebra with semantics-as-coalgebra; Abramsky and Shah's comonadic semantics relates structure to power along a different axis. The boundary theorem's shape — observations compatible with semantics are exactly those that factor through evaluation — has a family resemblance to full-abstraction results in programming language semantics, where definable observations characterize observational equivalence. We flag this as the section's open verification obligation: before submission, the claim of novelty for §5b must be checked against the full-abstraction literature in detail. Our present understanding of the difference: full abstraction characterizes when a *model* matches a fixed notion of observation; the boundary theorem characterizes which *observations* of a fixed syntax-semantics pair admit a bisimulation at all, with the Gödel coding as one such observation — but family resemblances of this kind are exactly where novelty claims die, and this one gets verified, not assumed.

### 11.10 Differential algebra

Ritt (Differential Algebra, 1950) and Kolchin (1973) own the algebra of derivations that Part 1 of the project reads arithmetically; Buium's arithmetic differential calculus goes a different direction (p-adic, not foundational). The flagship paper touches this only through the spectral instance of §4; the arithmetic interpretation is the subject of the planned Part 1 companion note, not of this paper.

---

## 12. Future Directions

We organize this section by tractability rather than by ambition. Three tiers: concrete axiom-discharge work with known techniques (tractable); new bounds that the framework organizes but does not yet derive (medium-term); and genuinely speculative directions toward P vs NP and its known barriers (speculative — explicitly *not* a deliverable). The GitHub issue numbers are the project's live tracking of these items; we include them so the reader can check the current status.

### 12.1 Discharging the named axioms

*(Updated 2026-06-10.)* The formalization contains six named axioms at `Obstruction/` boundary points: Haken's combinatorial state-count and width lemma (`Resolution.lean`, `HakenBottleneck.lean`), the Razborov-Rudich largeness conjecture (`NaturalProofsEvasion.lean`, re-scoped under §12.3), and the toy PA instance's two coding hooks (`PAGodelSystem.lean`, no longer load-bearing after §10.7). Each is a satisfiable proposition over opaque data with its satisfying interpretation documented — a convention adopted after an audit found three earlier placeholder-based axioms refutable. Discharging any of them strengthens the paper's claims; none are required for §§4-9 or for the §10.7 instance.

**PA GödelSystem completion (issue #40, re-scoped by §10.7).** The from-scratch Phases 2-4 plan is superseded: the real instance imports Foundation's representability rather than re-deriving it, and the toy instance's two remaining axioms are not load-bearing. What remains in scope is milestone 3 — instantiating `ProvabilityData` from Foundation's standard provability predicate (their derivability conditions D1-D3 exist upstream) to run our first and second incompleteness theorems end-to-end on real PA through our own chain. Weeks-scale; a §10.7 strengthener held for the rebuttal phase rather than a submission blocker.

**Haken's state-count (three axioms in `HakenBottleneck.lean`, one in `Resolution.lean`, issue #37).** The `PHP_state_lower_bound_spec` axiom (§9.5) encodes Haken's combinatorial bottleneck argument as an input. Discharging it requires formalizing Haken 1985 from primitives — a multi-month project of independent value, currently the most paper-adjacent medium-term item. The expected deliverable is an axiom-free derivation of `haken_lower_bound` and corresponding statements in `HakenBottleneck.lean`.

**Natural proofs (one axiom in `NaturalProofsEvasion.lean`, issue #39 — re-scoped 2026-06-10).** The axiom `obstruction_property_not_large` conjectured that an (opaque) obstruction property fails Razborov-Rudich largeness — an evasion claim. Issue #39 is re-scoped away from evasion: the target is now a formalization of the Razborov-Rudich limitation theorem itself, with the evasion axiom retained only as consistent scaffolding pending that work. See §12.3 for the framing and the honest gating (a time-bounded computation model, which no current Lean library provides).

The paper's framing is that these axioms are *bookkeeping for future work*, not hidden gaps. Each is stated precisely in Lean, each has a known classical proof, and each is tracked as an issue. A reader skeptical of the scaffolding is invited to read any single axiom's statement and confirm that it is not smuggling non-trivial content.

### 12.2 New proof complexity results

§9 recovers Haken modulo his combinatorial input. The framework's value-add is a uniform lens on *any* size-bounded rewrite system, and the natural question is whether that lens produces *new* bounds — not merely re-organizations of known ones.

**Tree-like resolution, Frege, extended Frege (issues #38, #44).** Each of these is a proof system for which classical lower bounds are either open or rely on specialized techniques. The obstruction framework's claim is that length lower bounds for any size-bounded form-changing rewrite system follow from target-size growth. Whether this perspective yields a new bound is a research question, not a resolved one. The framework organizes the question; it does not answer it.

**Trajectory-structure-based bounds (#41).** The observation that `EvalRewriteWitness` comes with both form-change data (blocks encoding) and size-growth data (bounds length) invites a more refined invariant. Can the structure of the *trajectory* — what is preserved and what changes at each step — give sharper bounds than size alone? This is currently speculation; an honest account is that size is the only invariant we have exploited quantitatively.

**Multiplicative-to-additive transformation (#42).** The Leibniz pattern (§4) is specifically multiplication becoming addition under differentiation/evaluation. If this transformation itself is a complexity measure — tracking how many `comp`-to-`add` steps occur in a proof's internal computation — it may provide a structural lower bound mechanism. Currently exploratory.

**Craig interpolation (#43).** Craig interpolation lower bounds (Krajíček, Pudlák) are a known route to proof complexity separations. The framework's relationship to interpolation is untested; the obstruction's structural content may or may not be compatible with interpolation-based lower bounds. Research direction, not planned work.

Each of these items is speculation-colored work: the framework is the organizing principle, not a proof engine that mechanically produces new bounds.

### 12.3 P vs NP: limitation theorems about formalized calculi

*(Rewritten 2026-06-10.)* A framework that connects encoding obstructions to proof complexity invites the question: does it suggest an approach to P vs NP? Our answer is no — and we think the honest relationship runs in a different and more defensible direction.

**The genre.** The serious metamathematics of P vs NP consists of *limitation theorems about formalized classes of solution techniques*. The regime of encodings, rewrite rules, and expression is itself well-mapped by existing calculi — term rewriting and Post systems for substitution; descriptive complexity (Fagin: NP as existential second-order logic) for machine-free characterization; implicit computational complexity (Bellantoni-Cook, light linear logic) capturing P as syntax; and bounded arithmetic (Cook's PV, Buss's S^1_2) as the calculus of feasible reasoning. The limitation theorems live over these. That is exactly what the three classical barriers are. Relativization (Baker-Gill-Solovay 1975) is a limitation theorem about diagonalization-style arguments: any technique insensitive to oracles cannot separate P from NP. Natural proofs (Razborov-Rudich 1997) is a limitation theorem, conditional on pseudorandom generators, about a formalized class of combinatorial lower-bound techniques — a class broad enough to contain the then-existing corpus of circuit lower bounds, which is what gave the theorem its force. Razborov's unprovability results place circuit lower bounds outside certain bounded-arithmetic theories under cryptographic assumptions: "this calculus of feasible reasoning cannot settle the question." Aaronson's survey of the formal-independence question maps this terrain; Krajicek's proof-complexity-generators program is the serious ongoing attempt to push it further. The recurring, genuinely strange feature — that by Razborov-Rudich the hardness of proving hardness is itself a consequence of hardness — is the substance behind the folklore observation that if P = NP, short proofs of it would be easy to find.

**Where this paper's results sit in that genre.** Two of our theorems are limitation theorems in precisely this sense, and we prefer to present them as such rather than as steps toward a separation:

- **The quotation cost separation** (`quotation_overhead_superpolynomial`, §5b) is a limitation theorem about the class of *compositional codings*: every coding computed bottom-up with a pairing that dominates the product pays super-polynomial quotation overhead along the observation trajectory. The class is broad and natural — it contains every standard Godel coding. The companion theorem (`compression_exists`) proves the class boundary is exact: outside compositionality, an injective coding exists with logarithmic overhead. A limitation theorem together with the sharpness witness for its technique-class is the structure the barrier literature teaches, and it is machine-checked here.

- **The framework-internal impossibility** (the DynSemiring normalization results: the Leibniz rule is the unique correct rewrite, and normalization preserves the SAT-determining invariant at every depth) is a limitation theorem about a *narrow* class: one algebraic calculus. We state plainly that its breadth is the open question. A barrier matters in proportion to the techniques its class contains; relativization and natural proofs earned their status by covering the existing corpus. Our calculus currently covers itself. Showing that recognized techniques embed in it — or proving they cannot — is the only way this result acquires or loses force, and we do not prejudge the outcome.

**Formalizing the barriers themselves (issue #39, re-scoped).** The earlier version of this work conjectured that the obstruction technique *evades* the natural proofs barrier, behind an axiom. We have withdrawn that framing: the claim quantified over an unspecified property and is not what the formalization supports. The re-scoped target is the barrier itself: a Lean formalization of the Razborov-Rudich theorem — constructivity and largeness as genuine definitions (largeness is already real in `NaturalProofsEvasion.lean`), the pseudorandom-generator hypothesis abstract, and the conditional conclusion as a theorem. To our knowledge no proof assistant formalization of the natural proofs barrier exists. The honest caveat: the constructivity condition and any non-abstract treatment of the PRG hypothesis require a time-bounded model of computation, which no current Lean library provides; the realistic scope is therefore the statement-level conditional theorem, with the computational model as the acknowledged gate. Formalizing a limitation theorem is a contribution that requires no claims about our own framework's power — which is exactly why we prefer it.

**What we do not claim.** No approach to separating P from NP is proposed. No evasion of any barrier is claimed. The structural observation that NP verifiers have `EvalRewriteWitness` structure survives from earlier drafts only as motivation for the limitation-theorem program above. We prefer a paper whose quantitative claims are defensible and whose speculative claims are openly labeled over a paper whose speculation is hidden.

### 12.4 Other domains

Three further directions are natural given the formalization:

**Binding theory (substitution).** Substitution in any language with variable binding is a form-changing rewrite (§8.1's lift/subst). A deeper formalization of why substitution changes form — not merely that it does in concrete cases — would sharpen the universality claim. Currently substitution appears as one instance among several; a binding-theoretic account would connect it to the structure of contexts and capture-avoiding reduction more abstractly.

**Sequent calculus.** §8's Curry-Howard route identifies beta reduction with cut elimination on natural deduction proofs. Sequent calculus is the classical alternative formulation, with cut elimination as its own primitive operation. Formalizing a sequent calculus and instantiating `NormalizationProofSystem` would provide a second proof-system instance and make the §8.6 claim concrete beyond lambda calculus.

**Type theory and dependent types.** The obstruction on beta reduction carries to polymorphic and dependently typed systems. System F and the Calculus of Constructions admit non-terminating terms (via polymorphism) that are closer analogs of Ω (§8.3). A dependently typed proof system inherits the obstruction through the same Curry-Howard route. This is low-lift follow-on work.

### 12.5 What future work does not address

The paper deliberately does not pursue:

- **P vs NP independence.** No formalization claim is made about independence of P vs NP from PA, ZFC, or bounded arithmetic. For the genuine state of that question we defer to Aaronson's survey and to Razborov's bounded-arithmetic unprovability results; our only connection is the far-horizon note that a formalized arithmetic stack (the Foundation integration path, §10) is a prerequisite for ever formalizing statements of that shape.
- **New explanations of incompleteness.** Gödel 1931 remains the source text. Our work formalizes a structural perspective that is implicit in Lawvere 1969 and makes it machine-checkable; it does not claim new mathematical content about incompleteness.
- **Replacing or reframing Haken's / Statman's / Orevkov's work.** We recover these results modulo their combinatorial inputs. The classical theorems stand; the framework provides an alternative organizing principle for viewing them.

---

## 13. Conclusion

*(Rewritten 2026-06-10 to the boundary thesis.)*

We set out to formalize a structural mechanism — a form-changing, meaning-preserving rewrite — underlying classical impossibility results, and found that the honest version of that project is a boundary theorem. An observable of a self-encoding term algebra supports a bisimulation between syntax and semantics if and only if it is extensional; the hierarchy extensional ⊊ rewrite-invariant ⊊ all observables is strict with machine-checked witnesses at both inclusions; and injective codings sit at the intensional extreme. The encoding obstruction with which the project began — no injective encoding commutes with a form-changing rewrite, one line from injectivity — is the extreme point of that boundary, not a theorem about codes failing to be clever. The classical results instantiate the intensional side six times, with the form-change condition discharged uniformly, one `simp` line per instance.

The boundary has a price tag. Compositional codings — the class containing every standard Gödel coding — pay super-polynomially for quotation along observation trajectories: doubly exponential codes against singly exponential semantic content. The matching counterexample is exact: an injective coding exists whose codes are linear in the stage, so compositionality, not injectivity, is what forces a code to pay for form. A limitation theorem with the sharpness witness for its technique-class is the structure of the classical complexity barriers, and §12.3 positions the paper's results — and its planned successors on Razborov-Rudich and Ben-Sasson-Wigderson — in exactly that genre. We propose no separation and claim no barrier evasion.

The abstractions earn their keep by surviving instantiation, and the paper reports the failures alongside the survivals: three scaffolding axioms were refutable as first stated and were repaired under a convention that now governs the project (§10.3); the over-abstracted `DiagonalTheory` admits only trivial instances (§6.5); the representability field originally demanded an equivalence no real theory satisfies and was weakened to the instance the diagonal lemma actually uses (§10.7). The surviving abstraction, `GodelSystem`, is instantiated by genuine Peano Arithmetic via the FormalizedFormalLogic Foundation library, and the instantiated diagonal lemma closes over the standard Lean axioms alone. Haken's PHP bound and Statman's blowup are recovered modulo their combinatorial inputs, with the attribution explicit.

The development is sorry-free: 5,721 lines across 17 core modules (measured at the repository head, 2026-06-10), on Mathlib and — for the real-PA instance — Foundation, pinned. Six named axioms remain at boundary points, each a satisfiable proposition over opaque data with its satisfying interpretation documented; none is load-bearing for the claims above. The prose is an interpretive account of the Lean artifact; every theorem statement in §§4-10 is quoted from source, and a skeptical reader is invited to start from `#print axioms`.

We close with the observation the formalization licenses. Classical impossibility results read as separate theorems with separate proofs; the machine-checked record shows them sharing one boundary — meaning survives rewriting, form does not, and what an encoding can track is decided by which side of the extensionality line its observables live on. The categorical kernel of this observation is Lawvere's; what the present work adds is a boundary characterized exactly, priced quantitatively, instantiated on real arithmetic, and packaged so that every claim, including the failed ones, is checkable. Whether limitation theorems of this kind can be pushed toward the breadth that gave the classical barriers their force is the open question we leave, deliberately framed as one about technique-classes rather than about separations.
