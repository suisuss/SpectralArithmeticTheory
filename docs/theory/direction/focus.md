# Focus

**Date:** 2026-06-10 (supersedes 2026-04-15)

Decision document. What to work on next given what's been achieved. Derived from the code, git log, and GitHub issue state — not from the pre-edit copies in this folder.

---

## Where the project actually is

The thesis is the **universal encoding obstruction**: a form-changing, semantics-preserving rewrite (`EvalRewriteWitness`) observed across Gödel incompleteness, the halting problem, cut elimination blowup, and resolution lower bounds. Paper targets CPP 2027 (~Sep 2026) or ITP 2027 (~Feb 2027).

Two facts established by the 2026-06-10 audit reshape the priorities (see `novelty.md`, Reassessment section):

1. **The unification is currently structural, not deductive.** The instance theorems (diagonal lemma, incompleteness, halting) are proved from their own structures; no theorem in the corpus uses an `EvalRewriteWitness` as a load-bearing hypothesis (`obstruction_and_incompleteness` is a pair constructor). The paper's value hinges on either fixing this or scoping the paper honestly as formalization + observed pattern.
2. **Three scaffolding axioms were inconsistent as stated** (repaired on `fix/inconsistent-axioms`; axiom census now 6, all satisfiable, data is `opaque`). Lesson encoded in the repair: never state an axiom about a non-opaque placeholder definition.

The 2026-04-15 immediate item (Phase 1 arithmetic discharge, #35) is DONE (commit 4d7c80e). The other immediate item — start the paper — was not started and is now the schedule risk: CPP 2027's deadline is ~3 months out.

Everything else — eigenvalue arithmetic, number tower through ℂ, ZF verification, Rotation Calculus SAT solvers — is either settled (Core/, Verification/, Lambda/) or deprioritised (Rotation/ as exploratory substrate, no formal link to the main thesis). Note: the most recent main commit (3abb13a) is deferred-tier #45 work; actual activity drifting off the stated critical path is the failure mode to watch.

## Ground truth

- **103 Lean files on main** (Core 6, Verification 4, Lambda 6, Obstruction 26, Rotation 59).
- **`Obstruction/*` is sorry-free** (0 sorries across 26 files).
- **Rotation/* has 6 residual sorries** in 4 files (InterRepresentation, GeneratorFixedPoint, FormalProofs, CSPEquivalence) — not paper-critical.
- **6 named axioms** (2026-06-10 census), concentrated in four Obstruction files. This is the entire outstanding propositional debt of the thesis; unspecified data (decode, provability, negation, counts) is `opaque`, not axiomatized:

  | File | Axioms | Character |
  |---|---|---|
  | `PAGodelSystem.lean` | 2 | `decodeFormula_code` (Phase 2), `compose_diag_apply` (Phase 3). Phase 1 arithmetic discharged as theorems (#35); the formerly inconsistent `phase2_decode_inverse` replaced by a theorem on `CodedFormula` (2026-06-10) |
  | `HakenBottleneck.lean` | 2 | Haken's combinatorial core, restated over valid refutations (2026-06-10) |
  | `Resolution.lean` | 1 | Shared w/ Haken |
  | `NaturalProofsEvasion.lean` | 1 | `obstruction_property_not_large`, now over a real largeness definition (2026-06-10) |
  | `Complexity.lean` | 0 | — |

- **46 GitHub issues**, 32 open / 14 closed. Closed cluster is the old SAT-solver / tree-arrangement work.

## Recommended focus

### Immediate — days to weeks

1. **Merge the axiom repair.** Build-verify `fix/inconsistent-axioms`, merge. Nothing else should land on the old, inconsistent base.
2. **Foundation library spike: DONE (2026-06-10), verdict GREEN.** Foundation@066bfa6 (their last v4.28-line rev, pre-module-system) builds its full incompleteness stack (`FirstOrder.Incompleteness.First`, 1175 jobs incl. the Bootstrapping/representability chain) on our exact toolchain in an isolated project — from source, cache not even needed. Two engineering facts learned the hard way: (a) integration must adopt Foundation's coherent lock-set (its mathlib `58d8468`, same v4.28 line as our tag) rather than adding a require next to our pin — naive `lake update` upgrades shared transitive deps incoherently; (b) NEVER run `lake update` in a worktree sharing `.lake` — it mutates the shared package store and breaks every checkout (restored 2026-06-10). Next step is now an integration project, not a spike: dedicated worktree with isolated build dir, move the mathlib pin to `58d8468`, full rebuild, then instantiate `DiagonalTheory` (their `diagonal` theorem matches its key field) and `paGodelSystem` (their `substNumeral` machinery is `compose_diag_apply` made concrete) — turning PAGodelSystem's two axioms into theorems. #40 drops from months to weeks.
3. **Start the paper draft NOW.** Use `docs/papers/UniversalObstruction/outline.md`, with the thesis reframed per `novelty.md` (Reassessment): the contribution is the formalization, the abstract `GodelSystem` interface, and the observed structural pattern — NOT "the obstruction explains incompleteness," unless item 4 lands first. Drop the P vs NP independence framing entirely (keep barrier discussion as future work). CPP 2027 deadline ~Sep 2026.

### Critical path — the theory question (weeks to months)

4. **Make the witness load-bearing: the bisimulation theorem.** Tiers 1-2 DONE (2026-06-10, `Obstruction/Bisimulation.lean`, sorry-free, zero axioms): the eval-quote square commutes up to bisimulation exactly for extensional observables (`supportsBisim_iff_extensional`); strictness witnesses establish extensional ⊊ rewrite-invariant ⊊ all observables; injective codes are maximally intensional (`injective_no_bisim`). This is the boundary theorem the paper's "is the abstraction doing work?" objection needed. Tier 3 is ALSO done for the compositional class (same day, `Obstruction/QuotationCost.lean`): closed form t_{2m} = dup^m(f₂), compositional codes doubly exponential vs singly exponential semantic content, `quotation_overhead_superpolynomial`. The original conjecture's quantification over all primitive recursive injections was corrected: injectivity alone cannot force trajectory code growth (sparse-trajectory compression); compositionality is necessary and sufficient for the sketched argument. Tracked by issue #55. The TermF C lift is DONE (`Obstruction/UniversalBisimulation.lean`): the boundary theorem holds over every signature and every Leibniz algebra, with the universal witness pair (a term and its Leibniz rewrite) replacing the model-specific one. The non-compositional Tier 3 case is now CLOSED in its quantitative reading (`compression_exists`, `compositionality_necessary` in `QuotationCost.lean`): an injective coding exists with linear codes along the trajectory, so the growth separation provably requires compositionality. Issue #55's formal program is complete.

### Medium-term — 3–6 months, pick one, after the paper is drafted

- **#37, re-targeted at Ben-Sasson–Wigderson.** Formalize the width method ("Short Proofs Are Narrow", 2001) instead of Haken's 1985 bottleneck counting: a clean width induction, far more tractable in Lean, with the PHP exponential bound as a corollary — and a recognized formalization first. Prerequisite either way: extend `Resolution.lean` so refutations (derive-the-empty-clause, `ValidFrom`) are first-class; the current model never states them.
- **#39, re-scoped (2026-06-10): formalize Razborov-Rudich itself.** The evasion framing is withdrawn — it conjectured a property of an opaque predicate and is not what the formalization supports. New target: the natural proofs barrier as a Lean theorem — constructivity and largeness as genuine definitions (largeness already real in `NaturalProofsEvasion.lean`), PRG hypothesis abstract, conditional conclusion proved. To our knowledge a proof-assistant first. Honest gate: the constructivity condition needs a time-bounded computation model, which no Lean library provides; scope is the statement-level conditional theorem. The `obstruction_property_not_large` axiom stays as consistent scaffolding until this lands, then gets retired.

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
- **#40** PA discharge Phases 2–4 — HELD pending the Foundation spike (immediate item 2), which may collapse it from months to weeks or kill the from-scratch plan entirely. Do not start from-scratch work before the spike reports.
- **#41** trajectory-structure-based bounds
- **#42** multiplicative-to-additive transformation as complexity measure
- **#43** obstruction ↔ Craig interpolation
- **#44** proof system separations via fine-grained obstruction analysis
- **#45** concrete SAT bounds via Rotation Calculus — note: 3abb13a already spent effort here against the 2026-04-15 focus; stop until the immediate items are done

### Park

Rotation/SAT engineering. Genuinely interesting, orthogonal to the thesis.

- **#20** ExtRes UNSAT certification
- **#29** smaller-than-resolution learning certificate families
- **#30** cascade-degree equivalence under BCP — formal bound
- **#31** UNSAT certificates via interleaved representation
- **#32** non-BCP propagation

## What not to optimise

- Don't refactor or extend `Obstruction/*` to new domains before the remaining 6 axioms are addressed and the paper is drafted.
- Don't add more `EvalRewriteWitness` instances. Seven instances of a pattern that does no deductive work add bulk, not evidence. The marginal instance is worth ~nothing next to one theorem where the witness is a working hypothesis (critical-path item 4).
- Don't start from-scratch Phases 2–4 of `PAGodelSystem` (issue #40) before the Foundation spike reports. If the spike fails, the paper's right framing remains "Phase 1 discharged, Phases 2–4 are future work."
- Don't pursue P vs NP independence as a deliverable, and don't include the independence argument in the paper at all — it pattern-matches to a genre that will color review of the legitimate work. Barrier discussion belongs in future work, clearly labeled speculation.
- Don't state an axiom about a non-opaque placeholder definition. That is how all three 2026-06-10 inconsistencies arose. Unspecified data is `opaque`; axioms are reserved for satisfiable propositions.
- Don't trust the direction docs for counts — grep (`grep -cE "^axiom " SpectralArithmetic/Obstruction/*.lean`). They drifted by 8 axioms between April and June.

## Related

- [novelty.md](novelty.md) — literature positioning; the 2026-06-10 Reassessment section is the basis for this focus revision
- [progress-report.md](progress-report.md) — 2026-04-14 report against `structural-domains.md`
- [../../papers/UniversalObstruction/outline.md](../../papers/UniversalObstruction/outline.md) — paper outline (ITP/CPP 2027); thesis framing to be revised per item 3
- GitHub issues #33–#45 — the research program; the bisimulation theorem (critical-path item 4) and the Foundation spike (immediate item 2) need new issues
