# Project agent instructions

You are working on SpectralArithmeticTheory: a Lean 4 formalization plus accompanying theory docs. The research identity (2026-06-10): **machine-checked limitation theorems about formalized technique-classes** — the genre of the classical complexity barriers. Fix a precise technique-class as a calculus, prove what it cannot do, witness the sharpness of the boundary; calibrate every abstraction against a real instance, and never claim a limitation without either a sharpness witness or a breadth caveat. Two threads carry this: eigenvalue arithmetic (Part 1, settled) and the bisimulation-boundary program around the encoding obstruction (Part 2, the current thesis and flagship paper).

## The philosophical reading (2026-07-23, calibrated)

What the trilemma/boundary results (`Obstruction/Trilemma.lean`, `Obstruction/UniversalBisimulation.lean`) license philosophically, and where the crux lies. Recorded verbatim from the 2026-07-23 session; treat the calibration paragraphs as binding when writing about this material.

**The strongest reading: Frege's sense/reference distinction becomes an order, not a dichotomy.** Sense is what a lossless representation keeps; reference is what survives semantic compression. The kernel order (`Ker (eval A) ≤ Ker o`) puts every possible observable of syntax on a graded spectrum between those poles — and the boundary theorem says something non-obvious about that spectrum: *the capacity to co-vary with execution begins exactly at the semantic pole*. Intensionality isn't a defect of a representation; it's storage of distinctions. But stored distinctions are precisely what disqualify a representation from tracking dynamics. That's a genuine sharpening of the classical picture, because the classical picture never said where on the spectrum simulation becomes possible. The hyperintensionality literature (structured propositions, Cresswell-style) has wanted a principled graded notion between syntactic identity and logical equivalence for decades; a kernel lattice with an *operational* criterion — which grades support bisimulation — is a candidate answer.

**Quine's opacity of quotation gets a mechanism.** Quotation is the canonical referentially opaque context; philosophers mostly treat that as a datum. The compression reading says *why*: quotation is lossless, evaluation is lossy, and a lossless context cannot commute with a lossy dynamics. Opacity is injectivity — nothing more mysterious than that.

**The most distinctive claim: the loss is *forced*.** `nontrivialSemantics_of_term` says you don't get to choose a lossless semantics — any semantics that validates a single evaluation step (the Leibniz rule is PA's own rule `S(a)×b → a×b + b` in disguise) already identifies distinct syntax. So "understanding," in the sense of assigning computation-invariant meanings, is inherently lossy relative to form. Chaitin's slogan "comprehension is compression" was quantitative and empirical; this is a structural version with a proof: to comprehend is to discard *at least* what evaluation discards. The consequence for self-representation: the naming role and the understanding role of a representation are jointly unsatisfiable by one map, so any self-modeling system must maintain (at least) two representations of itself and pay the translation cost between them — which is what `QuotationCost` prices.

**Calibration — the crux lives here.** The formal results are about term algebras carrying a specific structure: a composition, an addition, an observation, and the Leibniz law tying them together. The step from "systems with this structure" to "self-referential systems as such" — minds, agents, sciences of themselves — rests on the informal chain in `Universal.lean` Part 10 (self-reference needs PA, PA has multiplication, evaluation of multiplication *is* the Leibniz rule). That chain is plausible and each link is defensible, but it is not machine-checked, and the June audit's discipline applies: the philosophical claim currently carries a breadth caveat, not a sharpness witness. So the honest form of the philosophical thesis is conditional: **any system whose semantics respects its own internal dynamics faces the naming/understanding trade; whether every philosophically interesting self-representer is such a system is open.**

The crux: is the Leibniz structure *essential* to the trade, or just the instance we can prove? If someone exhibited a self-evaluating system with genuinely trivial semantic kernel — no two distinct expressions ever meaning the same thing, yet non-degenerate computation — the philosophical reading collapses to a fact about our algebras. The suspicion is that's impossible for any system with a nontrivial evaluation step (evaluation that changes form while preserving meaning *is* a kernel element), and that suspicion is itself close to a formalizable statement: "every non-identity, meaning-preserving rewrite generates semantic loss" is nearly a tautology once stated, which suggests the deep content is that *computation just is meaning-preserving form-change* — and that's the premise doing all the philosophical work.

Three threads follow from this: the sense/reference kernel lattice (most novel, possibly paper-adjacent), the forced-loss/comprehension-is-compression claim (deepest, needs the breadth argument), and the self-modeling consequence (most speculative, closest to the territory the focus doc warns about).

### Addendum (2026-07-23, post-investigation — supersedes the above where they conflict)

The three threads were investigated the same day (formalizations: `ForcedLoss.lean` PR #71, `KernelLattice.lean` PR #70; literature review in the session record). Four corrections are now binding:

1. **The crux is answered: the Leibniz structure is NOT essential.** `exists_injective_equivariant` (ForcedLoss.lean) proves an injective *equivariant* semantics exists over any dynamics whatsoever — reversible computation with trajectory semantics is a genuine counterexample to the morning's formulation. The load-bearing premise is *stable answers*: the escape closes exactly when the semantics must produce verdicts stable under further computation (`Equivariant.meaningPreserving_of_stable`). The defensible thesis is a disjunction: **every semantics of a moving system is either non-injective or answer-free.** The answer-free branch is genuinely inhabited (trajectory, game, trace semantics), so it is a fork, not a strawman. Note the internal relevance: Tier 1 (`evalGraphBisimF`) is an equivariance statement; the invariance/equivariance distinction matters inside the project, not just in the philosophy.
2. **The slogan pair is a tautology, proved as such.** `injective_iff_meaningPreserving_frozen` shows "faithful semantics freezes computation" and "moving meaning-preserving rewrites force loss" are jointly a restatement of injectivity. All content lives in the premises (evaluation produces stable answers; something is not yet an answer) — the `StepEval` layer derives forced loss from those premises without assuming meaning-preservation.
3. **The spectrum is not a line.** `eval_not_kerLE_isConstF` (KernelLattice.lean) proves the rewrite-invariant middle witness is order-incomparable with eval: the observable hierarchy is a partial order with the bisimulation class as a down-set, not a chain. Intensionality is not one-dimensional — there are incommensurable ways of being intensional. Do not draw the section 5b hierarchy as a chain.
4. **Novelty verdicts (verified literature review, 2026-07-23).** Opacity-as-injectivity is the strongest claim (quotation literature treats opacity as a datum; nearest formal neighbor is Kavvos's exposures — categorical, one-directional, no trilemma, no machine-check). The sense/reference kernel order survives only as the specific bisimulation threshold plus non-linearity (the spectrum idea is van Glabbeek's linear-time/branching-time spectrum; sense-as-procedure is Moschovakis's program). The comprehension-is-compression claim is **preempted by Myhill–Nerode / minimal realization theory**, which is already a structure-only compression obligation — the paragraph above claiming a first is wrong; what survives is that the loss is unconditional (forced by the dynamics) and folded into the disjunction. Relatedly: `extensionalF_iff_ker_le` is the standard factorization lemma — always present the application, not the lemma, as the contribution.

Disposition: in the flagship, the philosophy is one calibrated discussion passage plus defensive citations (Kavvos, van Glabbeek, Myhill–Nerode — the first two are section 11 gaps regardless of the philosophy program). A standalone philosophy paper (Synthese / Minds and Machines, opacity-as-injectivity as spine) is viable only after the flagship ships and is a months-scale writing project. The one formal task that strengthens the philosophy: the real-PA `MeaningPreserving` lemma on the Foundation bridge (days-scale) — it replaces Universal.lean Part 10's weakest informal link with a machine-checked instance; note also Part 10's link 1 should say Robinson Q, not PA, and "multiplication's recursion IS the Leibniz rule" is a family resemblance requiring a generalized unfolding-rule schema, not an identity.

## Before you start work

Always read, in order:

1. **`docs/theory/direction/README.md`** — canonical index. Tells you where everything is.
2. **`docs/theory/direction/focus.md`** — the decision document. What to work on, what not to work on, what to triage. If a task isn't on the critical path there, ask before starting.
3. **`docs/theory/direction/progress-report.md`** — most recent delivery report (2026-04-14). What was done in the last session, what's scaffolded, what's open.
4. **`git log --oneline -30`** — recent commits. The project moves in phases; the git log is the most accurate record of what's been tried and what shipped.

Then read whichever of these is relevant to your task:

- **`docs/theory/direction/overview.md`** or **`summary.md`** for the construction itself.
- **`docs/theory/direction/novelty.md`** for literature positioning.
- **`docs/theory/direction/pvsnp-assessment.md`** for framework-internal P vs NP results.
- A specific detail doc from `docs/theory/*.md` or `docs/theory/computation/*.md` only when you need that specific content. Direction docs cite them; don't read them speculatively.

## Evidence > inference

The direction docs are maintained by hand and drift. When status claims matter (axiom counts, sorry counts, file lists, what's proved), verify with the code and `git log`, not by quoting a doc. The Lean tree and commits are authoritative. Direction docs are organized interpretation.

Common checks:

- `grep -cE "^axiom " SpectralArithmetic/Obstruction/*.lean` — named axioms per file
- `grep -rE "\bsorry\b" SpectralArithmetic/ --include="*.lean"` — actual sorries
- `gh issue list --state all --limit 50` — issue landscape

## Labels

### Functional label (required, one per issue/PR)

- `theory` — formal proofs, formalization, mathematical arguments. Axiom discharge, new theorems, Lean engineering on `Core/`, `Verification/`, `Obstruction/`.
- `research` — exploratory investigation with uncertain outcome. New bound directions, speculative extensions, experiments on `Rotation/`.
- `infra` — solver, tooling, substrate code, measurement, test harness. Build system, CI, developer tooling.
- `docs` — documentation, papers, bridge/positioning documents, direction/ folder work.

### Focus tier (recommended, one per issue/PR)

Mirrors the bins in `docs/theory/direction/focus.md`. Apply the tier that reflects where the issue sits relative to the current thesis and paper critical path.

- `critical-path` — paper-critical, weeks-scale, clear scope. Currently: paper drafting, the Foundation library spike, and the bisimulation theorem (see `docs/theory/direction/focus.md`, 2026-06-10).
- `medium-term` — 3–6 months, substantive scientific contribution on the paper's critical path. Currently: `#37` (full Haken), `#39` (formalize the Razborov-Rudich barrier; re-scoped 2026-06-10).
- `deferred` — interesting and aligned with the thesis but not needed to ship the paper. Revisit after publication. Currently: `#38`, `#40`, `#41`–`#45`.
- `parked` — genuinely interesting but orthogonal to the thesis. Currently: `Rotation/` engineering (`#20`, `#29`–`#32`).
- `stale` — pre-obstruction era, not actively being worked. Kept open for reference only. Currently: `#6`, `#8`, `#9`, `#10`, `#11`, `#15`, `#16`.

When creating a new issue, apply one functional label and (unless it's obviously scope-zero) one tier label. When opening a PR, apply the same labels as the issue it closes.

## Commit and PR conventions

Follow the existing git log style. Both commit messages and PR titles use conventional prefixes:

```
<type>: <short description> (#N)

<optional body explaining the why>
```

Types in use: `feat`, `fix`, `docs`, `refactor`, `test`, `chore`. Pick the one that matches the primary intent.

- Reference the issue number `(#N)` when one exists. If no issue exists and the change is non-trivial, open one first.
- Keep commit messages focused on WHY, not WHAT (the diff shows what).
- Multi-commit PRs are fine; squash only when the individual commits aren't meaningful.
- Do not push or open PRs without explicit user confirmation (per `/home/suisuss/.programming/CLAUDE.md`).
- Never use `--no-verify`, `--amend`, or `--force` without explicit authorization.

## Worktree policy

Per `/home/suisuss/.programming/CLAUDE.md`:

- The main repo directory stays on `main`. Never commit feature work to main in the main directory.
- Create worktrees: `git worktree add .worktrees/<branch-name> -b <branch-name>`.
- All editing, committing, and pushing happens inside the worktree.

Build cache: worktrees should symlink `.lake` to the main directory's `.lake` so Mathlib doesn't get rebuilt:

```
ln -s /home/suisuss/.programming/sandbox/SpectralArithmeticTheory/.lake .worktrees/<name>/.lake
```

**NEVER run `lake update` in a worktree that shares `.lake`.** It mutates the shared package store (upgrading transitive deps incoherently against the pinned mathlib) and breaks every checkout that uses it — this happened 2026-06-10 and required restoring eight packages by hand. Dependency changes belong in a dedicated worktree with its own isolated `.lake` directory (no symlink), accepting the one-time full rebuild.

## When writing Lean

- `Obstruction/*` is sorry-free. Do not introduce `sorry` into it. If you need a temporary hole, use a named `axiom` with a precise claim; this is the convention in `PAGodelSystem.lean`, `HakenBottleneck.lean`, and `NaturalProofsEvasion.lean`. Axioms are counted and tracked; sorries are not allowed in `Obstruction/`.
- Axioms are for satisfiable PROPOSITIONS only. Unspecified data (functions, predicates, constants) must be `opaque`, never a concrete placeholder definition constrained by axioms — three axioms became inconsistent that way and were repaired 2026-06-10. Before adding an axiom, exhibit (at least in a comment) an interpretation satisfying it together with the existing ones.
- Comments in proofs: default to none. Only write a comment if the reason is non-obvious (a hidden invariant, a workaround, a subtle constraint). Never narrate the user's prompt or the current task.
- Don't refactor or extend `Obstruction/*` to new domains before the remaining named axioms are addressed and the paper is drafted (run the axiom grep for the current count). See `docs/theory/direction/focus.md` for the rationale.

## When writing docs

- The `docs/theory/direction/` folder is the canonical navigation. Keep it accurate. If you learn something that makes a direction doc stale, update the doc in the same PR.
- Don't create new top-level `docs/theory/*.md` documents without flagging the need first (per `/home/suisuss/.programming/CLAUDE.md`).
- Detail docs in `docs/theory/` and `docs/theory/computation/` are allowed to drift; treat them as snapshots with dates. Don't trust status claims in undated or old docs without verifying against the code.
- No emojis in docs, commits, or code unless explicitly requested.

## When responding to the user

- Be direct. Short responses beat long ones. State the key finding first.
- Challenge premises. Disagreement is more valuable than agreement.
- Flag weak evidence explicitly ("this is a single data point", "I haven't verified X").
- Don't soften critique to be polite. Per `/home/suisuss/.claude/CLAUDE.md`: your role is clear-eyed analysis, not validation.

## What not to do

- Don't pursue P vs NP independence as a deliverable. Keep it as speculation in paper future directions.
- Don't start `PAGodelSystem` Phases 2–4 (issue #40) without explicit scoping — each is Flypitch-scale (months).
- Don't chase elegance-driven rewrites of `Obstruction/*` before the remaining axioms are discharged.
- Don't close GitHub issues without explicit user confirmation; closure is shared-state visible to collaborators.
- Don't create markdown files under `docs/` as a substitute for conversation (summaries, plans, decisions). Use direction/ for durable records only; use conversation for ephemeral ones.
