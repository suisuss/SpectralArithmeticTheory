# Focus

**Date:** 2026-04-15

Decision document. What to work on next given what's been achieved. Derived from the code, git log, and GitHub issue state — not from the pre-edit copies in this folder.

---

## Where the project actually is

The thesis has stabilised on the **universal encoding obstruction**: a form-changing, semantics-preserving rewrite (`EvalRewriteWitness`) that unifies Gödel incompleteness, the halting problem, cut elimination blowup, and resolution lower bounds as seven machine-checked instances. Paper targets CPP 2027 (~Sep 2026) or ITP 2027 (~Feb 2027).

Everything else — eigenvalue arithmetic, number tower through ℂ, ZF verification, Rotation Calculus SAT solvers — is either settled (Core/, Verification/, Lambda/) or deprioritised (Rotation/ as exploratory substrate, no formal link to the main thesis).

## Ground truth

- **103 Lean files on main** (Core 6, Verification 4, Lambda 6, Obstruction 26, Rotation 59).
- **`Obstruction/*` is sorry-free** (0 sorries across 26 files).
- **Rotation/* has 6 residual sorries** in 4 files (InterRepresentation, GeneratorFixedPoint, FormalProofs, CSPEquivalence) — not paper-critical.
- **20 named axioms**, all concentrated in five Obstruction files. This is the entire outstanding technical debt of the thesis:

  | File | Axioms | Character |
  |---|---|---|
  | `PAGodelSystem.lean` | 14 | 7 small arithmetic (Phase 1) + 7 representability (Phases 2–4) |
  | `HakenBottleneck.lean` | 3 | Haken's combinatorial core |
  | `Resolution.lean` | 1 | Shared w/ Haken |
  | `NaturalProofsEvasion.lean` | 1 | `obstruction_property_not_large` |
  | `Complexity.lean` | 1 | — |

- **46 GitHub issues**, 32 open / 14 closed. Closed cluster is the old SAT-solver / tree-arrangement work.

## Recommended focus

### Immediate — weeks, paper-critical

- **`PAGodelSystem.lean` Phase 1.** Discharge the 7 small arithmetic axioms: `three_not_dvd_pow_two`, `seven_not_dvd_pow_two`, `seven_not_dvd_3pow_5pow`, `three_not_dvd_7pow_11pow`, `pow_two_injective`, `plus_pairing_injective`, `times_pairing_injective`. Pure Mathlib, estimated ~1 week. Highest leverage / clearest scope item in the project. (Issue #35)
- **Start drafting the paper.** Use `docs/papers/UniversalObstruction/outline.md`. The 5k-line sorry-free core already supports the thesis; drafting clarifies what the remaining axioms actually cost.

### Medium-term — 3–6 months, pick one

- **#37 full Haken discharge.** Three axioms in `HakenBottleneck.lean`. Turns the framework from "recovers Haken modulo his axiom" into "derives Haken." Highest scientific upside among open issues.
- **#39 natural proofs evasion.** Single `obstruction_property_not_large` axiom. Converts the barrier-evasion claim from speculation to theorem. Directly addresses the reviewer objection anticipated in the outline.

### Alongside the paper — cheap

- **#21 bridge document** — rotation calculus ↔ spectral arithmetic. Forces clarity on Rotation/'s role and ensures that branch is either linked up or honestly described as experimental.

## Triage

### Close as stale or de-scope

Pre-obstruction tree-arrangement / constructor research. Not on the critical path; keeping them open dilutes the issue landscape.

- **#6** k-ary tree arrangements (Fuss-Catalan)
- **#8** unordered tree arrangements
- **#9** forest arrangements
- **#10** triple constructor (ternary)
- **#11** sequence constructor
- **#15** state machine constructor
- **#16** meta-rewriting with runtime complexity tracking

### Defer without closing

"New bound from the framework" directions. Interesting but non-critical; the paper's publication will re-sharpen priorities.

- **#38** prove a NEW proof complexity lower bound
- **#40** Flypitch-scale PA discharge (Phases 2–4)
- **#41** trajectory-structure-based bounds
- **#42** multiplicative-to-additive transformation as complexity measure
- **#43** obstruction ↔ Craig interpolation
- **#44** proof system separations via fine-grained obstruction analysis
- **#45** concrete SAT bounds via Rotation Calculus

### Park

Rotation/SAT engineering. Genuinely interesting, orthogonal to the thesis.

- **#20** ExtRes UNSAT certification
- **#29** smaller-than-resolution learning certificate families
- **#30** cascade-degree equivalence under BCP — formal bound
- **#31** UNSAT certificates via interleaved representation
- **#32** non-BCP propagation

## What not to optimise

- Don't refactor or extend `Obstruction/*` to new domains before the 20 axioms above are addressed and the paper is drafted.
- Don't start Phases 2–4 of `PAGodelSystem` (issue #40). Each is Flypitch-scale (months). The paper's right framing is "Phase 1 discharged, Phases 2–4 are future work" — not "we got stuck trying to do Gödel's representability result from scratch."
- Don't pursue P vs NP independence as a deliverable. Keep it as speculation in the paper's future directions, as already framed in the outline.

## Related

- [progress-report.md](progress-report.md) — 2026-04-14 report against `structural-domains.md`
- [../../papers/UniversalObstruction/outline.md](../../papers/UniversalObstruction/outline.md) — paper outline (ITP/CPP 2027)
- GitHub issues #33–#45 — the research program
