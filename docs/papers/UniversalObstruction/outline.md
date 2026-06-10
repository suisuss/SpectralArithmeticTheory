# Paper Outline: The Universal Encoding Obstruction

## Working Title

**The Encoding Obstruction: A Structural Characterization of Self-Referential Impossibility, Formalized in Lean 4**

## Target Venue

ITP (Interactive Theorem Proving) or CPP (Certified Programs and Proofs)

Both are appropriate. ITP tends to favor larger formalizations of mathematical content; CPP tends to favor formalizations with programming-language content (which our Curry-Howard work has). Either is plausible.

Backup: LMCS (Logical Methods in Computer Science) for a longer journal version.

## Thesis (One Sentence)

*(Revised 2026-06-10, after `Bisimulation.lean`.)* We characterize exactly which observations of a self-encoding term algebra are compatible with Godel encoding — an observable supports a bisimulation between syntax and semantics if and only if it is extensional — and show that the classical impossibility results (Godel incompleteness, halting, cut elimination blowup, resolution lower bounds) are instances of the intensional side of this boundary, with injective codings as the extreme case; formalized as sorry-free Lean 4.

*(Former framing, kept for reference: a form-changing, semantics-preserving rewrite unifying the impossibility results. The boundary theorem subsumes it: the rewrite-changes-form observation is the statement that `rootTag` is not even rewrite-invariant.)*

## What the Paper Claims

1. **The bisimulation boundary theorem** (`Bisimulation.lean`): the eval-quote square commutes up to bisimulation precisely for extensional observables (`supportsBisim_iff_extensional`); the observable hierarchy extensional ⊊ rewrite-invariant ⊊ all is strict with machine-checked witnesses; injectivity is maximal intensionality (`injective_no_bisim`). This is the theorem that makes the abstraction load-bearing.
2. **A precise abstraction (`EvalRewriteWitness`)** capturing the structural pattern shared across multiple impossibility results
3. **The encoding obstruction proved universally** for all term algebras with this structure (`Universal.lean`) — now positioned as the intensional extreme of the boundary
4. **Five concrete instances** machine-checked: Leibniz/eigenvalue, PA arithmetic, self-reference (diagonal), program execution (halting), beta reduction
5. **Cut elimination as the sixth instance via Curry-Howard**, recovering Statman's blowup mechanism
6. **A framework for proof complexity lower bounds** from the obstruction, demonstrated for resolution (Haken framework, modulo combinatorial axiom)
7. **GodelSystem instance scaffolding for PA**, with Phase 1 proved and Phases 2-4 as satisfiable named axioms over opaque data

## What the Paper Does NOT Claim

- A new explanation of incompleteness (Godel 1931 still does the work)
- A new proof complexity result (we recover Haken modulo his combinatorial input)
- A proof of P vs NP or its independence
- A breakthrough in mathematical logic (the structural pattern is implicit in Lawvere 1969 and Yanofsky 2003)

The contribution is **the formalization, the unification, and the framework** — not new mathematical content.

---

## Structure

### 1. Abstract (200 words)

The encoding obstruction states that no injective encoding of a term algebra can commute with a form-changing, semantics-preserving rewrite. We formalize this as a universal theorem over parameterized term algebras in Lean 4, and demonstrate it underlies six classical impossibility results: Godel's first and second incompleteness theorems (via an axiomatized GodelSystem), the halting problem, cut elimination blowup (via Curry-Howard), and proof complexity lower bounds for resolution (via Haken's framework). The unifying abstraction `EvalRewriteWitness` makes the structural pattern explicit and provides a framework for instantiating these results in concrete settings. The formalization comprises ~3,950 lines of sorry-free Lean 4 across 12 modules. We discuss the relationship to Lawvere's categorical fixed-point theorem and identify a research direction extending the framework toward proof complexity bounds and questions about P vs NP independence.

### 2. Introduction (~3 pages)

**Motivation.** Several classical impossibility results — Godel incompleteness, the halting problem, cut elimination blowup — share a common structural feature: they involve self-reference exploited through a form-changing rewrite that no encoding can faithfully track. This shared structure has been observed informally and articulated categorically (Lawvere 1969, Yanofsky 2003), but has not been formalized in a way that makes the unification machine-checkable and instance-by-instance verifiable.

**Contribution.** We provide:
- A Lean 4 abstraction `EvalRewriteWitness` capturing the structural pattern
- A universal encoding obstruction theorem proved over parameterized term algebras
- Six machine-checked instances of the pattern across logic, computation, and proof theory
- A framework connecting the obstruction to proof complexity lower bounds
- Scaffolding for instantiating the framework to PA (Godel encoding from primitives)

**Outline of the paper.** Section 2 reviews the encoding obstruction informally and positions it relative to existing work. Sections 3-7 present the formalization in stages: the universal theorem, the diagonal lemma and incompleteness, the halting problem, beta reduction and cut elimination, and proof complexity. Section 8 discusses the PA scaffolding. Section 9 reviews related work in detail. Section 10 outlines future directions and limitations.

### 3. Background and Related Work (~2 pages)

**The intension/extension distinction.** Frege, Carnap. The encoding obstruction is the formal expression of this distinction in term-rewriting systems.

**Lawvere's fixed-point theorem.** Lawvere 1969 showed that Cantor's theorem, Godel's incompleteness, and Tarski's undefinability are categorical instances of one fixed-point theorem. Our work refines this in the term-rewriting setting, with the additional structure of root-constructor changes.

**Yanofsky's universal approach.** Yanofsky 2003 unified several self-referential paradoxes via cartesian closed categories. Our `EvalRewriteWitness` is a syntactic counterpart that admits direct formalization.

**Existing Lean formalizations.** Flypitch (Han, van Doorn) formalized incompleteness in Lean 3 from PA primitives. Our work axiomatizes Phase 3 (representability) but provides a different organizing principle (the universal obstruction, with incompleteness as instance).

**Coalgebraic logic.** Rutten and others have studied bisimulation between syntactic and semantic coalgebras. Our `no_coalgebra_morphism` theorem is a related but distinct contribution.

**Proof complexity foundations.** Haken 1985 (PHP), Statman 1979 (cut elimination), Cook and Reckhow 1979. Our framework provides a structural lens; specific bounds are recovered modulo their combinatorial inputs.

### 4. The Universal Encoding Obstruction (~3 pages)

**The parameterized term algebra.** `TermF C` is parameterized over an arbitrary constant signature `C`. Structural constructors (comp, add, obs) are fixed.

```lean
inductive TermF (C : Type*) where
  | const : C -> TermF C
  | comp  : TermF C -> TermF C -> TermF C
  | add   : TermF C -> TermF C -> TermF C
  | obs   : TermF C -> TermF C
```

**The Leibniz rewrite changes root constructor.** `obsRewrite` maps `obs(comp(a,b))` to `add(comp(obs(a),b), comp(a,obs(b)))`. The root constructor changes from `obs` to `add`. Universally over all `C` and all `a, b`.

**The encoding obstruction theorem.**

```lean
theorem universal_encoding_obstruction
    (epsilon : TermF C -> N) (h : Function.Injective epsilon) (a b : TermF C) :
    epsilon (leibnizRewrite (.obs (.comp a b))) != epsilon (.obs (.comp a b))
```

**Semantic invariance.** Proved over an abstract `LeibnizAlgebra` interpretation: meaning is preserved while form changes.

**The intension/extension gap.** The combined theorem: codes differ AND meaning agrees. Universal over signatures, models, encodings, and sub-terms.

### 5. The EvalRewriteWitness Abstraction (~2 pages)

**The general principle.** Form-changing rewrite + injective encoding = obstruction. Stated as `general_obstruction` (almost trivial from the definition of injectivity).

**Why this isn't trivial.** The non-trivial content is showing that specific rewrites (Leibniz, PA's evaluation, beta) satisfy the form-change premise. We discuss in `RootConstructorChange.lean` why generic non-trivial semantics is insufficient.

**The structure.**

```lean
structure EvalRewriteWitness (T S : Type*) where
  rewrite : T -> T
  eval : T -> S
  witness : T
  changes_form : rewrite witness != witness
  preserves_meaning : eval (rewrite witness) = eval witness
```

**Multiple sufficient conditions.** Root constructor change is one (the cleanest). Commutativity, associativity, size growth — all give form change.

### 5b. The Bisimulation Boundary (~3 pages) — NEW, the load-bearing section

**The eval-quote question.** Does the Godel encoding induce a behavioral equivalence between the syntactic coalgebra (rewriting) and the semantic coalgebra (observation)? (Lawvere/Yanofsky ask about fixed points; this asks about the encoding itself.)

**Observation systems and bisimulation.** `ObsSystem X O` (step + output), `Bisim` (output agreement + step closure) — the coalgebraic notion for X ↦ O × X.

**Tier 1 (positive).** `evalGraphBisim`: the graph of eval is a bisimulation; `codeBisim`: for any code/decode retraction, code-level dynamics are bisimilar to the semantics. The square commutes up to bisimulation when observation is extensional.

**Tier 2 (the boundary).** `supportsBisim_iff_extensional`: an observable supports a bisimulation iff it factors through eval. Strict hierarchy with witnesses: `rootTag` (not rewrite-invariant — the original form-change phenomenon, relocated to the observable side), `isF₀` (rewrite-invariant, not extensional), injective ε (not extensional — `injective_no_bisim`).

**Reframing the obstruction.** `no_coalgebra_morphism` is the statement that faithful codes sit at the intensional extreme of the boundary. The impossibility instances of Sections 6-9 are readings of the intensional side.

**Tier 3 (open).** Growth-rate non-bisimilarity for primitive recursive codings on a common carrier — stated as the open conjecture, with the proof sketch from the theory docs; future work.

### 6. Self-Reference and Incompleteness (~3 pages)

**The GodelSystem abstraction.** Coding, decoding, substitution, representability of the diagonal function.

**The diagonal lemma is a theorem.** Proved from `GodelSystem` axioms via `compose_diag`. Not axiomatized at this level.

**First incompleteness.** Construct `godelSentence`, prove not provable (consistency + Sigma-1-completeness) and not refutable (consistency + Sigma-1-soundness + DNE).

**Second incompleteness.** Sketched in `Diagonal.lean` Part 8.

**The Curry-Howard alternative.** `Incompleteness.lean` axiomatizes the diagonal property directly as `DiagonalTheory`. Two paths to the same conclusion.

### 7. The Halting Problem (~1 page)

**Halting as EvalRewriteWitness.** Program execution changes program state while preserving program identity. The diagonal program `D(code(D))` exhibits the obstruction.

**`halting_undecidable`** proved sorry-free for any computation system with a halting decider and the diagonal construction.

**The same pattern.** Self-substitution `D(code(D))` corresponds to `subst(phi, fcode(phi))` in the Godel construction. Same mechanism, different application.

### 8. Beta Reduction and Curry-Howard (~3 pages)

**Beta reduction as the fifth instance.** `(lambda. 0) (lambda. 0)` reduces to `(lambda. 0)`. Root changes from `App` to `Abs`. Form changes, semantics preserved.

**The duplicator and exponential growth.** `(lambda. 0 0) t` reduces to `t t`. For `size(t) >= 5`, the reduction strictly grows size. Iterated, this gives 2^k growth.

**Cut elimination via Curry-Howard.** Proofs are programs, cut elimination is beta reduction. Statman's non-elementary blowup is the trajectory divergence theorem applied to proof terms.

**Universal proof systems via Curry-Howard.** Any proof system whose verification involves normalization-style rewriting has the obstruction (`NormalizationProofSystem`).

### 9. Proof Complexity (~3 pages)

**The dual structure.** `SizeGrowth` (size grows >= 2x per step) gives upper bounds on size after k steps. `SizeBounded` (size grows <= 2x per step) gives lower bounds on steps to reach size M.

**The proof length lower bound theorem.** For size-bounded rewrites, reaching a target of size M from initial size s requires at least log_2(M/s) steps.

**Cut elimination application.** Combined with Curry-Howard and Statman's non-elementary normal form sizes, this recovers a non-elementary lower bound on cut elimination.

**Resolution and Haken's bound.** Resolution is form-changing on clause sets. Each step adds one clause. Haken's PHP bound is recovered: GIVEN the combinatorial state-size axiom (Haken's contribution), the obstruction framework derives proof length >= 2^(n/20).

**Honest separation.** The obstruction provides the LENGTH-from-STATES framework. Haken provides the STATE-COUNT-from-COMBINATORICS argument. Together, they give the bound. The framework alone does not derive PHP.

### 10. The PA GodelSystem Instance (~2 pages)

**Phase 1 proved.** Godel encoding via prime factorization, positivity. Sorry-free.

**Phases 2-4 scaffolded.** Six precise axioms corresponding to known classical results: encoding injectivity, decoding inverse, diagonal function representability, PA provability, PA negation, compose_diag specifications.

**The instance is constructive given the axioms.** `paGodelSystem` is sorry-free modulo the axioms.

**Roadmap to full discharge.** Estimated 2-3 months of formalization work to fully discharge the axioms (Flypitch-scale effort).

### 11. Related Work, In Detail (~2 pages)

**Lawvere 1969.** Diagonal arguments and cartesian closed categories. The encoding obstruction is a refinement in the term-rewriting setting, with explicit form-change content.

**Yanofsky 2003.** A universal approach to self-referential paradoxes. Uses cartesian closed categories. Our work is more syntactic and Lean-formalized.

**Flypitch (Han, van Doorn).** Lean 3 formalization of incompleteness from PA primitives. Our work axiomatizes Phase 3 but provides a different organizing principle (universal obstruction with incompleteness as instance).

**Carneiro's Metamath formalization.** Direct axiomatic incompleteness proof. Different style; complementary approach.

**Coalgebraic logic.** Rutten, Jacobs. Bisimulation between coalgebras. Our `no_coalgebra_morphism` theorem is related but our setting is more concrete.

**Proof complexity classics.** Haken 1985, Statman 1979, Cook-Reckhow 1979. Our framework provides a structural lens; specific bounds remain open without their combinatorial inputs.

**Differential algebra.** Ritt, Kolchin. The Leibniz rule appears in our setting via the spectral framework's eigenvalue structure (Part 1 of the project, not the focus of this paper).

### 12. Future Directions (~2 pages)

**Extending the GodelSystem instance.** Discharging Phases 2-4 axioms for PA. Estimated 2-3 months of formalization work.

**New proof complexity results.** Deriving NEW resolution lower bounds from the obstruction framework (not just recovering Haken via axiomatized state-counts).

**The cut elimination connection.** Formally connecting the duplicator's exponential growth to Statman's specific non-elementary terms. Currently the connection is structural; making it quantitative requires Curry-Howard at the typed level.

**Speculative: P vs NP.** The structural argument (proof systems require arithmetic, arithmetic has the obstruction) suggests a research direction. We are explicit that this is speculative: known barriers (relativization, natural proofs, algebrization) are not addressed. The conjecture that NP-completeness forces encoding-evaluation tracking is unproved and may be false. We position this as a research program, not a deliverable.

**Other domains.** Binding theory (deeper account of why substitution changes form), sequent calculus formalization, type theory connections.

### 13. Conclusion (~1 page)

We presented a Lean 4 formalization unifying several classical impossibility results under one structural abstraction: the form-changing, semantics-preserving rewrite. The formalization is sorry-free across ~3,950 lines and 12 modules. The unification is conceptually grounded (Lawvere, Yanofsky) but the explicit machine-checked treatment is new. The framework supports proof complexity work and may inform future investigations of computational impossibility, though the path to specific complexity-theoretic results requires substantial additional work.

---

## Estimated Length

- Conference version (ITP/CPP, 16 pages): selective coverage, omit some sections
- Journal version (LMCS, 30+ pages): full coverage including PA scaffolding details

## Estimated Submission Timeline

- ITP 2026: deadline likely February 2026 (already past)
- CPP 2027: deadline likely September 2026
- ITP 2027: deadline likely February 2027

Realistic target: CPP 2027 or ITP 2027.

## Self-Critique

**Strengths:**
- Real formalization, sorry-free
- Clean abstraction
- Multiple instances showing pattern is genuine
- Honest about scope and limitations

**Weaknesses to anticipate:**
- "This is just Lawvere's theorem" -- need to articulate the refinement clearly
- "Where's the new mathematics?" -- the contribution is formalization + unification, not new theorems
- "Why these specific instances?" -- need to motivate why this collection unifies cleanly
- "The proof complexity story is incomplete" -- be upfront that we recover Haken modulo his combinatorial input, not derive it from scratch

**Anticipating reviewer 2:**
- Will compare unfavorably to Flypitch on incompleteness depth
- Will note that the universal claim is over parameterized signatures, not over all Godel-numbering-capable theories from primitives
- Will press on whether the abstraction actually does work or is just suggestive labeling

**Defensive moves in the paper:**
- Be explicit about scope: we don't prove incompleteness from PA primitives, we provide the structural framework with PA scaffolding
- Be explicit about the proof complexity gap: framework + axiomatized combinatorial input = bound
- Be explicit about future directions: P vs NP is a research direction, not a deliverable

## Next Steps for Writing

1. Draft the abstract (200 words, hardest part)
2. Draft the introduction motivation
3. Pull theorem statements directly from Lean files for technical sections
4. Write the related work section (requires careful reading of Lawvere/Yanofsky)
5. Write the future directions section honestly
6. Iterate on the framing to avoid overclaiming
7. Get feedback from someone in the formalization community before submission

## Files to Reference

When writing each section, the corresponding Lean files:

| Section | Lean File |
|---------|-----------|
| §4 Universal Obstruction | Universal.lean |
| §5 EvalRewriteWitness | EvalRewrite.lean, RootConstructorChange.lean |
| §5b Bisimulation Boundary | Bisimulation.lean |
| §6 Incompleteness | Diagonal.lean, Incompleteness.lean |
| §7 Halting | Halting.lean |
| §8 Beta + Curry-Howard | BetaReduction.lean, CurryHoward.lean |
| §9 Proof Complexity | ProofComplexity.lean, Resolution.lean |
| §9 Verification Arithmetic | VerificationArithmetic.lean |
| §10 PA GodelSystem | PAGodelSystem.lean |

Each section can use Lean snippets directly from these files, with surrounding prose explaining context.
