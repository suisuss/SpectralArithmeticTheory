# Direction

Canonical navigation for the project: where it is, where it's going, and which details live where. Agents and newcomers should start here.

---

## Read in this order

1. **[focus.md](focus.md)** — what to work on next given what's been achieved. Decision document. Read this first if you're about to start work.
2. **[progress-report.md](progress-report.md)** — 2026-04-14 delivery report since `structural-domains.md`. Most current status of the Lean corpus, issue landscape, and paper outline.
3. **[overview.md](overview.md)** — structured overview of the construction (axioms, number tower, PA/ZF equiconsistency, open conjecture). Updated with current status.
4. **[summary.md](summary.md)** — narrative summary of the same material. Shorter, prose-style.
5. **[novelty.md](novelty.md)** — literature positioning. What's known elsewhere, what's novel here, and how the intensional/extensional framing sharpens the P vs NP connection.
6. **[pvsnp-assessment.md](pvsnp-assessment.md)** — framework-internal P vs NP results (what's proved, what isn't, which path the project is pursuing).

---

## What the project is

**Research identity (2026-06-10): machine-checked limitation theorems about formalized technique-classes.** The genre is that of the classical complexity barriers — relativization, natural proofs, bounded-arithmetic unprovability: fix a precise class of techniques as a calculus (of encoding, rewriting, observation, or reasoning), prove what that class cannot do, and witness the sharpness of the class boundary. The project's discipline follows from the genre: abstractions are calibrated against real instances (a defect-finding method that caught five soundness-grade flaws in June 2026 alone), axioms are satisfiable propositions over opaque data with documented interpretations, and every claimed limitation carries either a sharpness witness or an explicit breadth caveat.

Current limitation theorems, all machine-checked in Lean 4:

- **The bisimulation boundary** (`Bisimulation.lean`, `UniversalBisimulation.lean`): an observable of a self-encoding term algebra supports a bisimulation between syntax and semantics iff it is extensional; injective codings are maximally intensional. Proved over every signature and Leibniz algebra.
- **The quotation cost pair** (`QuotationCost.lean`): every compositional Gödel coding pays super-polynomial quotation overhead along observation trajectories; an exact counterexample shows arbitrary injective codings need not. Compositionality, not injectivity, is the boundary.
- **The encoding trilemma, resolved** (`Trilemma.lean`, #68): injectivity, homomorphism, non-trivial semantics — stated as one theorem over every signature and Leibniz algebra. Non-triviality is itself a theorem (the universal witness pair), so the trilemma collapses to a dilemma: an injective homomorphism exists iff the term algebra is empty. Both non-empty cells carry witnesses, and the whole configuration is a corollary of the bisimulation boundary (homomorphic = extensional side, injective = intensional side). The kernel-order restatement makes the compression reading precise: an observable supports a bisimulation iff its kernel contains eval's kernel — iff it compresses at least as much as the semantics; homomorphic encodings are the exact semantic compression, injective ones are lossless, and the dilemma reads "no lossless compression to the semantic quotient".
- **The kernel lattice** (`KernelLattice.lean`, #68): the intensionality preorder on observables (kernel inclusion), poles characterized (injective = top, constant = bottom), pairing as join, the boundary as a position (bisimulation support = at or below eval). Sharpening: the rewrite-invariant middle is order-incomparable with eval (`eval_not_kerLE_isConstF`) — the observable hierarchy is a class between two down-sets, not a chain — and the strict-middle witness now lives at the universal TermF level (`isConstF` over `natSuccAlgebra`), closing the gap UniversalBisimulation.lean conceded to the concrete model.
- **The framework-internal DynSemiring impossibility** (narrow class; breadth — whether recognized techniques embed — is the stated open question).

Two formalization threads carry the program:

**Part 1 — Eigenvalue arithmetic** (settled). A commutative semiring with a Leibniz derivation produces ℕ as eigenvalues; Peano axioms are theorems; the number tower ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ emerges as concentric spectra. PA-equiconsistent at A1–B5; ZF-equiconsistent at A1–F5. See `Core/`, `Verification/`. Standalone formalization note planned.

**Part 2 — The boundary program** (active; flagship paper for CPP/ITP 2027). The encoding obstruction and its instances (Gödel incompleteness, halting, cut elimination, resolution) positioned as the intensional side of the bisimulation boundary; `GodelSystem` instantiated by genuine PA via the Foundation library on standard Lean axioms. `Obstruction/` is sorry-free with 6 named axioms (each satisfiable, none load-bearing for the headline claims). Planned successors in the same genre: a Razborov-Rudich formalization (#39) and the Ben-Sasson-Wigderson width bound (#37).

---

## Current state (one-line facts)

- **105 Lean files** on main: Core 6, Verification 4, Lambda 6, Obstruction 28, Rotation 59.
- **`Obstruction/*` is sorry-free.** Rotation/* has 6 residual sorries in 4 files — not paper-critical.
- **6 named axioms** (2026-06-10 census): PAGodelSystem 2, HakenBottleneck 2, Resolution 1, NaturalProofsEvasion 1, Complexity 0. The Phase 1 arithmetic axioms were discharged as theorems (#35). Unspecified *data* (decode, provability, negation, clause counts) is `opaque` rather than axiomatized; only genuine propositions are axioms, each satisfiable. Three scaffolding axioms that were inconsistent as stated (`phase2_decode_inverse`, `obstruction_property_not_large` over a `True`-placeholder `IsLarge`, `haken_bottleneck_exists` with a placeholder hypothesis) were repaired 2026-06-10.
- **46 GitHub issues**, 32 open / 14 closed. Closed cluster is the pre-obstruction SAT-solver / tree-arrangement exploration.
- **Paper outline** at `docs/papers/UniversalObstruction/outline.md`.

---

## Lean layout

```
SpectralArithmetic/
├── Core/              Part 1. Axiom tower.
│   ├── Basic.lean         A1–A7, Peano P1–P5
│   ├── Semiring.lean      B1–B5, eigenvalue theorem, A8 as theorem
│   ├── IntegralDomain.lean C1–C3, A7 as theorem, power rule
│   ├── Rational.lean      D1–D2, eigenvalue 1/q
│   ├── Complete.lean      E1 (axiomatized)
│   └── Complex.lean       G1, j⁴ = f₀
├── Verification/      Part 1. ZF and model.
│   ├── PeanoTest.lean     PA1–PA9
│   ├── ZFTest.lean        ZF from abstract Ens (F1–F5)
│   ├── Model.lean         Forward model (AddMonoidAlgebra R R)
│   └── Countermodels.lean F1/F2/F3 non-triviality
├── Lambda/            Part 2 substrate. Lambda/SK embedding.
├── Obstruction/       Part 2. 28 files, sorry-free.
│                       Seven EvalRewriteWitness instances:
│                       term algebras (Universal), PA arithmetic (EvalRewrite),
│                       diagonal (Diagonal), halting (Halting),
│                       beta reduction (BetaReduction),
│                       cut elimination (CurryHoward), resolution (Resolution).
│                       Plus PAGodelSystem, HakenBottleneck,
│                       NaturalProofsEvasion, VerificationArithmetic,
│                       ProofComplexity, RootConstructorChange,
│                       Incompleteness, and earlier material.
└── Rotation/          Exploratory. SAT solvers, CDCL, width trajectories.
                       Not linked to the paper thesis; see issue #21.
```

Build: `lake build` (Lean 4 v4.28.0 + Mathlib v4.28.0).

---

## Theory detail docs (outside direction/)

Used by the direction docs as citations; read only when you need the detail.

### Core theory

- [../axioms.md](../axioms.md) — formal axiom set
- [../layers.md](../layers.md) — the seven levels A–G
- [../spectral-arithmetic-complete.md](../spectral-arithmetic-complete.md) — unified exposition
- [../pa-equiconsistency.md](../pa-equiconsistency.md) — PA equiconsistency with countermodels
- [../zf-equiconsistency.md](../zf-equiconsistency.md) — ZF equiconsistency
- [../zf-test-suite.md](../zf-test-suite.md) — ZF axioms verified
- [../path-b-obs-structure.md](../path-b-obs-structure.md) — the structural-obs axioms
- [../a4-bisimulation.md](../a4-bisimulation.md) — bisimulation as identity
- [../role-of-x.md](../role-of-x.md) — x as observation parameter
- [../transfinite-ordinals.md](../transfinite-ordinals.md) — ω through ε₀
- [../set-constructor-and-deriving-e.md](../set-constructor-and-deriving-e.md)
- [../extending-the-number-systems.md](../extending-the-number-systems.md)
- [../integer-extension.md](../integer-extension.md), [../rational-extension.md](../rational-extension.md), [../real-extension.md](../real-extension.md), [../complex-extension.md](../complex-extension.md)
- [../eulers-number-and-differentials.md](../eulers-number-and-differentials.md)
- [../spectral-arithmetic.md](../spectral-arithmetic.md) — original construction

### Computation / obstruction detail

- [../computation/encoding-obstruction.md](../computation/encoding-obstruction.md) — the core obstruction theory
- [../computation/impossibility-hierarchy.md](../computation/impossibility-hierarchy.md) — four levels, one impossibility
- [../computation/structural-domains.md](../computation/structural-domains.md) — binding, cut elimination, Curry-Howard
- [../computation/self-representation.md](../computation/self-representation.md) — Gödel encoding and triple identity
- [../computation/confluence.md](../computation/confluence.md) — rewriting system
- [../computation/information-domain.md](../computation/information-domain.md) — ⊕ obstruction across domains
- [../computation/addition-non-locality.md](../computation/addition-non-locality.md) — carry propagation forces state
- [../computation/computing-as-external-state.md](../computation/computing-as-external-state.md)
- [../computation/observer-as-register.md](../computation/observer-as-register.md)
- [../computation/framework-independence.md](../computation/framework-independence.md)
- [../computation/obs-of-and.md](../computation/obs-of-and.md)
- [../computation/diffusion-analysis.md](../computation/diffusion-analysis.md)
- [../computation/derivation-barrier.md](../computation/derivation-barrier.md)
- [../computation/vector-observation.md](../computation/vector-observation.md)
- [../computation/convergence.md](../computation/convergence.md), [../computation/convergence-conjecture.md](../computation/convergence-conjecture.md)
- [../computation/normalization-vs-variation.md](../computation/normalization-vs-variation.md)
- [../computation/pvsnp/obstruction-independence.md](../computation/pvsnp/obstruction-independence.md) — P vs NP independence argument
- [../computation/pvsnp/barrier-analysis.md](../computation/pvsnp/barrier-analysis.md)

### Rotation Calculus (exploratory, not paper-critical)

- [../computation/pvsnp/reconstituted/Rotation Calculus/](../computation/pvsnp/reconstituted/Rotation%20Calculus/) — full subtree
- [../computation/pvsnp/reconstituted/](../computation/pvsnp/reconstituted/) — tree decomposition, DAG solvers, compositional proof calculus

---

## Labels and conventions

See [../../../CLAUDE.md](../../../CLAUDE.md) for project-level agent instructions and labelling / commit / PR conventions.

Quick reference:

- **Functional labels** (one per issue): `theory`, `research`, `infra`, `docs`.
- **Focus tier** (one per issue, optional but recommended): `critical-path`, `medium-term`, `deferred`, `parked`, `stale`. Tier corresponds to the bins in [focus.md](focus.md).
- **Commit prefixes**: `feat:`, `fix:`, `docs:`, `refactor:`, `test:`, `chore:` (see git log).
- **Issue references**: use `(#N)` in commit messages and PR titles for traceability.
