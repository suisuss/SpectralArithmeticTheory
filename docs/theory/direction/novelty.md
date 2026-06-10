# Novelty Assessment

**Date:** 2026-02-19
**Reassessed:** 2026-06-10 — see "Reassessment" at the end of this document. The reassessment ranks what is actually novel against the Lean tree as it exists, identifies what is NOT novel (with reasons), and adds four literatures the original survey missed. Where the two parts disagree, the reassessment wins.

---

## What exists (the individual pieces)

### Differential algebra (Ritt, Kolchin)

Studies commutative rings with derivations satisfying the Leibniz rule — exactly the algebraic structure in Path B. But this field treats derivations as tools for solving differential equations. Nobody in differential algebra has framed the eigenvalue structure of a derivation as *generating arithmetic* — the interpretation "eigenvalues are natural numbers" is not in the literature. The algebra is known; the arithmetic interpretation is not.

### Coalgebra as foundation (Rutten 2000, Jacobs & Rutten 1997)

Provides the categorical framework — bisimulation as equality, final coalgebras, coinduction as the dual of induction. Rutten explicitly considers natural numbers as initial algebras (the algebraic/inductive side). But his work doesn't connect coalgebraic structure to differential algebra or eigenvalue arithmetic. The framework is there; the connection to derivations is not.

**Key references:**
- Rutten, J.J.M.M. (2000). *Universal Coalgebra: A Theory of Systems.* Theoretical Computer Science, 249(1):3-80
- Jacobs, B. & Rutten, J.J.M.M. (1997). *A Tutorial on (Co)Algebras and (Co)Induction.* EATCS Bulletin

### Lawvere's fixed-point theorem

Generalizes Gödel diagonalization categorically — any surjection A → (A → Y) yields a fixed point of every map Y → Y. This is the categorical core of Gödel, Cantor, and Turing's arguments. But it's about *existence of fixed points*, not about bisimulation between syntactic and semantic structures.

### Bialgebras / (Ω, Ξ)-structures

Study when algebraic and coalgebraic structure coexist on the same carrier — an algebra-coalgebra pair where bisimulations are congruences. This is structurally close to what the framework does (compose is algebraic, obs is coalgebraic, they interact via Leibniz). But this work doesn't consider Gödel encoding or the specific question of whether syntactic rewriting is bisimilar to semantic observation.

### Buium's "Differential calculus with integers" (2013)

Uses Fermat quotients as arithmetic analogues of derivations. This is the closest existing work to "derivations on number theory," but it goes in a completely different direction — p-adic analysis, not eigenvalue foundations.

**Reference:** Buium, A. (2013). *Differential calculus with integers.* arXiv:1308.5194

### Abramsky's comonadic semantics (2018)

Relates structure (syntax) and power (semantics) via comonads, giving syntax-free characterizations of logical equivalences. This is about which formulas can distinguish states, not about whether Gödel encoding preserves observational behavior.

**Reference:** Abramsky, S. & Shah, N. (2018). *Relating Structure and Power: Comonadic Semantics for Computational Resources.* CMCS 2018, LNCS 11202. Also published at CSL 2018; journal version in J. Logic and Computation 31(6), 2021

### Turi & Plotkin (1997), "Towards a Mathematical Operational Semantics"

Combined algebra (syntax) and coalgebra (semantics) into a unified framework for structural operational semantics via distributive laws and bialgebras. Published at LICS 1997. Became influential precisely because it made the syntax-semantics relationship precise. The Spectral Arithmetic question is in the same spirit but more specific: not just "can algebra and coalgebra coexist?" but "is the Gödel encoding a behavioral equivalence between them?"

---

## What doesn't exist (the gaps this theory fills)

The specific question — **does the Gödel encoding of a self-representing arithmetic system create a bisimulation (or weaker behavioral equivalence) between the syntactic coalgebra (rewriting) and the semantic coalgebra (eigenvalue observation)?** — does not appear in the literature.

Three combinations are novel:

### 1. Eigenvalue structure from differential algebra → arithmetic

Differential algebra has the eigenvalue theorem. Number theory has arithmetic. Nobody has formally connected them as "eigenvalues generate the naturals via a derivation on a semiring." The algebra is Ritt and Kolchin's. The interpretation — that the eigenvalue indexing IS the natural numbers, that successor IS multiplication by the unit eigenfunction, that obs IS the abstract d/dx that reads off which number a state represents — is new.

### 2. Coalgebraic primitives as the foundation for that arithmetic

Rutten's universal coalgebra gives the framework. But applying it to differential algebra's eigenvalue structure to *derive* PA is new. The specific synthesis — State/compose/obs as coalgebraic primitives, Leibniz rule as the structural axiom, eigenvalue theorem as the bridge to arithmetic — has not been done.

### 3. Gödel encoding as a candidate coalgebra morphism

Lawvere generalized diagonalization categorically, but asking whether the *encoding itself* has coalgebraic structure (not just the fixed point it produces) is a different question that appears to be unasked. The precise formulation — two coalgebras on the same carrier (semantic: eigenvalue scaling; syntactic: rewriting simulation), prove or disprove bisimulation between them — is novel.

---

## The self-compiling compiler analogy

The syntax-semantics bisimulation question has a precise computational analogue: **bootstrapping compilers**.

### The analogy

A self-compiling compiler has exactly this structure:

| Compiler concept | Spectral Arithmetic analogue |
|---|---|
| Source code S | Term (syntax) |
| Running binary B | Eigenstate (semantics) |
| Compilation: S → B | Evaluation: Terms → State (coalgebra morphism) |
| Decompilation: B → S | Gödel encoding: State → ℕ ⊂ State (quotation) |
| Self-compilation: B(S_B) = B | Self-representation: obs applied to the code of obs reproduces obs-behavior |

A self-compiling compiler is a **fixed point** of the eval-quote cycle: the semantic object (running compiler) applied to its own syntactic description (source code) produces an equivalent semantic object (the same compiler). Fixed points are a special case of bisimulation — a state bisimilar to itself after transformation.

### Known results in computation

This self-referential property is well-understood computationally:

- **Kleene's second recursion theorem:** For any total computable function f, there exists an index e such that φ_e = φ_{f(e)}. Every computable transformation of programs has a fixed point — a program that behaves the same after the transformation.
- **Quines:** Programs that output their own source code. These are syntactic fixed points — the output (syntax) equals the input (syntax). Every Turing-complete language has quines.
- **Self-compiling compilers:** GCC compiles itself. Rust's compiler compiles itself. These are semantic fixed points — the output (running program) is functionally equivalent to the input (source code interpreted).
- **The Y combinator:** λf.(λx.f(x x))(λx.f(x x)) — a fixed-point combinator that gives every function a fixed point. The computational realization of Lawvere's theorem.

### What's known vs. what's new

| Property | Status |
|---|---|
| A language can describe a Turing machine | **Known** (universal computation) |
| That description, run through the machine, produces itself | **Known** (Kleene's recursion theorem, quines) |
| The self-reproduction preserves syntactic structure | **Known** (quines reproduce their text) |
| The self-reproduction preserves *observational behavior* | **Open** (the Spectral Arithmetic conjecture) |

The novel question: does the round-trip through Gödel encoding preserve not just the code (syntactic quine) but the **dynamics** (semantic quine)? A quine reproduces its text. A self-compiling compiler reproduces its function. The conjecture asks whether the eigenvalue framework has a "self-compiling" property where the Gödel encoding reproduces the observational behavior — a **coalgebraic quine**.

### Why this is stronger than Kleene

Kleene's theorem guarantees a fixed point exists — some program e where φ_e = φ_{f(e)}. But:

- Kleene says nothing about whether the fixed point preserves *coalgebraic* structure (observation, bisimulation)
- Kleene works in the syntactic world (indices of programs). The conjecture asks about the *semantic* world (eigenvalues, observational dynamics)
- The fixed point Kleene gives you is typically uncomputable to find and unrecognizable when you see it. The conjecture asks whether the *natural* encoding (prime factorization Gödel numbering) already has this property

If the encoding is a bisimulation, it would mean the natural Gödel encoding is not just any fixed point (Kleene guarantees one exists) but a *structurally natural* one that preserves the coalgebraic dynamics. That would be a much stronger result than Kleene — it would say the syntax/semantics relationship is not arbitrary but behaviorally coherent.

### The eval-quote diagram

The precise question in diagrammatic form:

```
        eval
Terms --------→ State
  |                |
  | ⌜·⌝            | obs_semantic
  |                |
  ↓                ↓
State --------→ State
     obs_code
```

Does this diagram commute up to bisimulation? That is:

- Starting from a term t, evaluating to an eigenstate and then observing (right-then-down)
- Starting from a term t, encoding as a Gödel number and then simulating observation on the code (down-then-right)

Do these two paths produce bisimilar results for all terms t?

Evaluation (top arrow) is a coalgebra morphism — this is known and definitional. The question is entirely about the left arrow (Gödel encoding) and whether it makes the square commute.

---

## Assessment of overall novelty

The theory is **a genuine synthesis of existing ideas that nobody has combined this way**. Each ingredient is known. The assembly is not.

| Component | Known? | Novel use? |
|---|---|---|
| Commutative semiring with derivation | Yes (differential algebra) | Yes (as arithmetic foundation) |
| Coalgebraic primitives, bisimulation | Yes (Rutten, Jacobs) | Yes (combined with derivation) |
| Eigenvalue theorem for derivations | Yes (standard) | Yes (interpreted as "numbers") |
| Gödel encoding | Yes (1931) | Yes (as candidate coalgebra morphism) |
| Self-compiling / Kleene fixed points | Yes (recursion theory) | Yes (strengthened to coalgebraic bisimulation) |
| Syntax-semantics via bialgebra | Yes (Turi-Plotkin) | Yes (specific Gödel encoding question) |

The question about bisimulation between syntactic and semantic coalgebras is the most original part of the entire project. If anything about it can be proved — positive, negative, or partial — that would be the publishable result with the highest impact. A precise impossibility theorem characterizing *where* the syntax-semantics bisimulation breaks down would itself be a significant contribution to the theory of Gödel encodings.

The right comparison is Turi and Plotkin's bialgebraic semantics, which combined algebra (syntax) and coalgebra (semantics) into a unified framework and became influential precisely because it made the syntax-semantics relationship precise. This theory asks a more specific and more ambitious question: not just "can algebra and coalgebra coexist on the same structure?" but "does the Gödel encoding create a behavioral equivalence between the algebraic (syntactic) and coalgebraic (semantic) views?"

---

## The intensional/extensional framing

The bisimulation conjecture can be reformulated using a well-known distinction in mathematical logic and type theory: extensional equality (same observable behavior) vs. intensional equality (same internal structure). This reframing connects the conjecture to established work and opens additional novel directions.

### The two coalgebras as two modes of equality

| Concept | Extensional (behavioral) | Intensional (structural) |
|---|---|---|
| **Equality notion** | Same outputs for all inputs | Same definition/syntax |
| **Coalgebra** | (State, obs_semantic) | (State, obs_code) |
| **What obs does** | Eigenvalue scaling: obs(fₙ) = n · fₙ | Syntactic rewriting: parse, apply obs as rewrite, re-encode |
| **Normal form** | Irreducible eigenstate fₙ | Canonical Gödel code |

The bisimulation conjecture asks: **do the extensional and intensional normal forms coincide?**

### What exists in this area

The extensional/intensional distinction is well-studied:

| Work | What it does | What it doesn't do |
|---|---|---|
| **Extensional vs. intensional MLTT** (Martin-Löf) | Distinguishes transparent equality (ext.) from computational equality (int.) | Doesn't connect to eigenvalue structure or arithmetic foundations |
| **Homotopy Type Theory** (Univalent Foundations Program, 2013) | Shows the int./ext. gap has topological structure (identity proofs form ∞-groupoids) | Doesn't frame this in terms of coalgebraic observation or Gödel encoding |
| **Observational Type Theory** (Altenkirch, McBride, Swierstra 2007) | Bridges ext./int. by making observation the basis of equality | Closest in spirit but doesn't connect to differential algebra or eigenvalues |
| **Denotational vs. operational semantics** (standard PL theory) | Ext. = denotational (what it means), int. = operational (how it computes) | Full abstraction results ask similar questions but not via eigenvalue structure |

### What's novel in this framing

**1. Extensional/intensional as coalgebra selection.** The choice between extensional and intensional equality becomes a choice of *which coalgebra to observe with*. This is a concrete, algebraic instantiation of a distinction that is usually treated philosophically or type-theoretically. Nobody has framed the extensional/intensional gap as "two coalgebras on the same carrier with different observation functions."

**2. Normal form coincidence as the bisimulation question.** The conjecture — do extensional and intensional normal forms agree? — is well-posed in rewriting theory (confluence asks a related question for a single rewriting system). But asking it *across* two different observation systems (eigenvalue scaling vs. syntactic rewriting) on a self-encoding arithmetic system appears to be new.

**3. The gap as structure, not obstacle.** HoTT showed that the intensional/extensional gap in type theory has rich topological structure. The analogous claim here — that the gap between obs_semantic and obs_code has characterizable coalgebraic structure — would be a new result connecting HoTT-style thinking to differential algebra. If the ways the two observations disagree can be classified (e.g., by syntactic complexity, by eigenvalue magnitude, by term depth), that classification itself would be a contribution.

### Connection to P vs NP

The intensional/extensional framing sharpens the complexity connection:

- **P** = problems where extensional normal form (verification) and intensional normal form (construction) are reachable at the same polynomial cost
- **NP** = problems where extensional normal form is efficiently checkable but intensional normal form may be exponentially expensive to construct
- **P vs NP** = does every object with an efficiently recognizable extensional normal form also have an efficiently constructible intensional normal form?

The bisimulation conjecture is the structural (cost-free) version of this question. It asks whether the two normal forms agree *at all*, before considering computational cost. This makes the structural question logically prior to the complexity question — a necessary condition, not a sufficient one.

The research program this suggests: **characterize the intensional/extensional gap in the eigenvalue framework (structural question), then ask whether the gap has complexity-theoretic content (quantitative question).** The first step is tractable with coalgebraic tools. The second would connect to existing complexity theory.

### Why this combination is novel

Each piece exists:
- Extensional/intensional equality (logic, type theory)
- Coalgebraic observation (Rutten, Jacobs)
- Eigenvalue structure of derivations (differential algebra)
- Gödel encoding (mathematical logic)
- Normal form theory (rewriting systems)
- P vs NP as verification-construction gap (complexity theory)

Nobody has assembled them into: "the extensional/intensional gap, instantiated as two coalgebras on an eigenvalue-arithmetic system, with the Gödel encoding as the map between them, and the bisimulation question as the structural analogue of P vs NP." Each connection in that chain is individually natural. The full chain is unasked.

---

## Key references

| Work | Relevance |
|---|---|
| Rutten (2000), *Universal Coalgebra* | Framework: bisimulation, final coalgebras, coinduction |
| Jacobs & Rutten (1997), *Tutorial on (Co)Algebras* | Algebra-coalgebra duality, natural numbers as initial algebra |
| Turi & Plotkin (1997), *Towards a Mathematical Operational Semantics* | Combining syntax (algebra) and semantics (coalgebra) via distributive laws |
| Lawvere (1969), *Diagonal Arguments and Cartesian Closed Categories* | Categorical Gödel diagonalization |
| Abramsky & Shah (2018), *Relating Structure and Power: Comonadic Semantics for Computational Resources*, CSL 2018 | Comonadic syntax-semantics bridge |
| Ritt (1950), *Differential Algebra* | Commutative rings with derivations |
| Buium (2013), *Differential Calculus with Integers* | Arithmetic analogues of derivations (different direction) |
| Kleene (1938), *On Notation for Ordinal Numbers* (JSL 3:150-155) | Second recursion theorem; fixed points of computable transformations |
| Staton (2009), *Relating Coalgebraic Notions of Bisimulation* | Multiple bisimulation definitions, when they coincide |
| Martin-Löf (1975), *An Intuitionistic Theory of Types: Predicative Part* | Extensional vs. intensional equality in type theory |
| The Univalent Foundations Program (2013), *Homotopy Type Theory: Univalent Foundations of Mathematics* | Identity proofs as paths; the ext./int. gap has topological structure |
| Altenkirch, McBride, Swierstra (2007), *Observational Equality, Now!* | Observation-based equality bridging ext./int. — closest in spirit |
| Cook (1971), *The Complexity of Theorem-Proving Procedures* | Cook-Levin theorem; NP-completeness as encoding preservation |

---

## Reassessment (2026-06-10)

Audit basis: the full Obstruction/ Lean tree as of the axiom repair
(branch `fix/inconsistent-axioms`), not the prose descriptions of it.
The original survey above is sound on the literature; where it errs is
in how much of the project's claimed contribution survives contact
with what the Lean files actually prove.

### What is NOT novel (and should not be claimed)

**1. The universal encoding obstruction theorem.** As formalized,
`universal_encoding_obstruction` is `Function.Injective` plus
constructor disjointness: an injective map separates distinct terms,
and the Leibniz rewrite produces a syntactically distinct term. The
file says this honestly ("logically trivial"). It is an organizing
observation, not a mathematical contribution, and no claim of novelty
should rest on it.

**2. The unification, as currently formalized.** The seven "instances"
do not derive anything from the obstruction. `Diagonal.lean` and
`Halting.lean` do not even import `EvalRewrite`; their theorems are
proved entirely from their own hypothesis-rich structures
(`GodelSystem`, `ProvabilityData`, the halting setup). The one place
the connection is stated — `obstruction_and_incompleteness` in
`Incompleteness.lean` — is a pair constructor: it conjoins two
independently proved facts. The prose claim "the obstruction is the
ENGINE of incompleteness" is not formalized as an implication anywhere
in the corpus. Until a theorem exists in which an `EvalRewriteWitness`
is a load-bearing hypothesis, the unification is suggestive labeling,
and a referee will say so.

**3. The intension/extension distinction itself.** Frege and Carnap
own the distinction; type theory has formal versions (see the original
survey); and the computational literatures below have THEOREMS about
it. The framing is good positioning, not novelty.

**4. The conservation-of-information reading of P vs NP.** The
framework's preservation results (f_0 count invariant at every
truncation depth) are facts about the framework's conservativity, not
about SAT's hardness. Any conservative system preserves information;
systems that solve problems must discard it. "Our algebra cannot
compress SAT" is a statement about the algebra's weakness. The missing
step — embedding arbitrary polynomial-time computation into a
conservative system with polynomial overhead and a preserved measure —
is the entire problem, and the framework provides no purchase on it.

### What IS novel (ranked by defensibility)

**1. The bisimulation question (the coalgebraic quine).** Still the
strongest asset, exactly as the original survey says — and as of this
writing it appears in no issue and no focus tier. The question (does
the Gödel encoding induce a behavioral equivalence between the
syntactic coalgebra and the semantic coalgebra?) is unasked in the
literature, well-posed with existing tools, and answerable in either
direction. Crucially, it is also the cure for weakness 2 above: the
current obstruction is trivial because it demands strict code equality
under an injective encoding; commutation UP TO BISIMULATION is the
version where the answer is not forced by injectivity, and a theorem
locating exactly where the bisimulation fails (or proving a partial
positive) would make the framework load-bearing. This is the highest
expected-value theory work in the project.

*Status update (2026-06-10, later the same day):* Tiers 1-2 are now
formalized in `SpectralArithmetic/Obstruction/Bisimulation.lean`
(sorry-free, zero axioms, `propext` only). Tier 1 (positive): the
eval graph is a bisimulation, and the eval-quote square commutes up
to bisimulation for any code/decode retraction — the coalgebraic
quine exists at the extensional level. Tier 2 (characterization):
`supportsBisim_iff_extensional` — an observable supports a
bisimulation relating each term to its evaluation iff it factors
through eval; strictness witnesses give
extensional ⊊ rewrite-invariant ⊊ all observables, and
`injective_no_bisim` shows injective codes are maximally intensional.
What remains open is Tier 3: the growth-rate non-bisimilarity for
primitive recursive codings on a common carrier
(`encoding-obstruction.md` Part 5). The publishable-result ranking
below should be read with item 1's partial answer in hand.

**2. Part 1, eigenvalue arithmetic.** The interpretation — naturals as
derivation eigenvalues, Peano axioms as theorems, the number tower as
concentric spectra, machine-checked — is genuinely absent from the
differential-algebra and coalgebra literatures (the original survey's
analysis stands). Modest in impact but real, self-contained, and
publishable as a formalization note independent of Part 2.

**3. The `GodelSystem`/`DiagonalTheory` packaging.** A minimal abstract
interface from which the diagonal lemma and both incompleteness
theorems fall out in ~300 clean lines. Library-grade Lean engineering.
Its novelty is bounded by the FormalizedFormalLogic Foundation library
(below), which has the deeper PA-concrete result; the abstract
interface layered over it is still a contribution, the standalone
incompleteness development is not.

**4. The f_0-indistinguishability experiments.** Encoding-independence
(CTerm/NAND vs Church/SK hitting the same wall) and total
indistinguishability under variable sharing are suggestive
experimental mathematics. Novel observations within the framework;
claimable only as experiments until connected to a measure that exists
outside the framework.

### Literatures the original survey missed

| Work | Why it matters here |
|---|---|
| N. Jones, *Computability and Complexity from a Programming Perspective* (1997); Jones optimality; Futamura projections | The "compilation cost interpretation" has an existing literature with theorems: whether self-interpretation overhead can be specialized away IS Jones optimality. CONS-free programs characterize P. Any compilation/execution-asymmetry claim must be positioned against this or it will look naive. |
| B. Jay & T. Given-Wilson, SF-calculus; Jay, pattern calculus (*Programs as Data Structures*, c. 2009-2011) | Intensional computation made formal: a calculus where term STRUCTURE is observable, with definability theorems separating intensional from extensional power. The closest formal neighbor to "obs reads syntactic form." |
| FormalizedFormalLogic **Foundation** (Lean 4) | Sorry-free Gödel I and II including representability, in the same language and era. Changes the Phase 2-4 strategy (instantiate, don't rebuild) and must anchor the paper's related-work section. |
| Ben-Sasson & Wigderson, *Short Proofs Are Narrow* (2001) | The width method is the formalization-friendly route to resolution lower bounds; PHP exponential bounds follow as a corollary. The right target for issue #37, in place of Haken's 1985 bottleneck counting. |

### Revised bottom line

The publishable-result ranking, replacing the original survey's
closing paragraph:

1. A theorem characterizing where the syntactic/semantic bisimulation
   holds or breaks for a Gödel-encoded arithmetic system (positive,
   negative, or partial — any outcome is a contribution).
2. First Lean 4 formalization of the Ben-Sasson-Wigderson width bound
   (a real, recognized proof-complexity formalization first).
3. The unification paper, IF the witness is made load-bearing (a
   theorem with `EvalRewriteWitness` as a working hypothesis, or a
   converse showing systems without the witness admit complete
   encodings); otherwise it is a formalization-experience paper and
   should be scoped as one.
4. Part 1 as a standalone formalization note.
