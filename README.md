# Spectral Arithmetic

Machine-checked Lean 4 development around two related results.

**Part 1 — Eigenvalue arithmetic.** A commutative semiring with a Leibniz derivation produces ℕ as eigenvalues. The Peano axioms are theorems, not assumptions, and the number tower ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ emerges as concentric eigenvalue spectra within a single algebraic structure. PA-equiconsistent at A1–B5; ZF-equiconsistent at A1–F5.

**Part 2 — The bisimulation boundary.** An observable of a self-encoding term algebra supports a bisimulation between syntax and semantics iff it is extensional, over every signature and Leibniz algebra (`Obstruction/UniversalBisimulation.lean`). In compression form (`Obstruction/Trilemma.lean`): semantics is a lossy compressor whose loss is forced by the Leibniz rule; simulating semantics requires compressing at least that much; a faithful (injective) code compresses nothing; therefore no faithful code simulates semantics. The encoding obstruction is the boundary's intensional extreme, the quotation cost pair its quantitative companion, and Gödel incompleteness, halting, cut elimination, beta reduction, and resolution are machine-checked instances on the intensional side. The `Obstruction/` directory (27 files) is sorry-free; 6 named axioms remain, concentrated in four files. This is the project's current primary thesis and the target of an upcoming paper (CPP/ITP 2027).

## Entry point

Navigation and status live in [`docs/theory/direction/`](docs/theory/direction/). Read the docs there in this order:

1. [`direction/README.md`](docs/theory/direction/README.md) — canonical index
2. [`direction/focus.md`](docs/theory/direction/focus.md) — what to work on next
3. [`direction/progress-report.md`](docs/theory/direction/progress-report.md) — most recent delivery report
4. [`direction/overview.md`](docs/theory/direction/overview.md), [`summary.md`](docs/theory/direction/summary.md) — two views of the construction
5. [`direction/novelty.md`](docs/theory/direction/novelty.md), [`pvsnp-assessment.md`](docs/theory/direction/pvsnp-assessment.md) — positioning

Agent conventions (labels, commits, PRs) live in [`CLAUDE.md`](CLAUDE.md).

## Build

```
lake build
```

Requires Lean 4 v4.28.0 + Mathlib v4.28.0.

## Layout

```
SpectralArithmetic/
├── Core/           Axiom tower (Part 1)
├── Verification/   ZF and model (Part 1)
├── Lambda/         Lambda/SK embedding (Part 2 substrate)
├── Obstruction/    Universal encoding obstruction (Part 2, sorry-free)
└── Rotation/       Exploratory SAT solvers, CDCL, width trajectories
docs/
├── theory/direction/   Navigation and current state — start here
├── theory/             Detail docs (axioms, extensions, ZF, etc.)
├── theory/computation/ Obstruction theory detail
└── papers/             Paper drafts and outlines
```
