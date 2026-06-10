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

Two threads, both machine-checked in Lean 4.

**Part 1 — Eigenvalue arithmetic.** A commutative semiring with a Leibniz derivation produces ℕ as eigenvalues. Peano axioms are theorems, not assumptions. The number tower ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ emerges as concentric eigenvalue spectra; axioms at lower levels become theorems at higher ones. PA-equiconsistent at A1–B5; ZF-equiconsistent at A1–F5 (Infinity, Separation, Replacement, Power Set, Union). See `Core/`, `Verification/` (10 files total).

**Part 2 — Universal encoding obstruction.** A form-changing, semantics-preserving rewrite (`EvalRewriteWitness`) unifies Gödel incompleteness, the halting problem, cut elimination blowup, beta reduction, and resolution proof-complexity lower bounds as seven machine-checked instances. `Obstruction/` (26 files) is sorry-free; remaining technical debt is 20 named axioms concentrated in five files. This is the current primary thesis and the target of the upcoming paper (CPP/ITP 2027).

---

## Current state (one-line facts)

- **103 Lean files** on main: Core 6, Verification 4, Lambda 6, Obstruction 26, Rotation 59.
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
├── Obstruction/       Part 2. 26 files, sorry-free.
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
