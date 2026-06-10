# Project agent instructions

You are working on SpectralArithmeticTheory: a Lean 4 formalization plus accompanying theory docs. The research identity (2026-06-10): **machine-checked limitation theorems about formalized technique-classes** — the genre of the classical complexity barriers. Fix a precise technique-class as a calculus, prove what it cannot do, witness the sharpness of the boundary; calibrate every abstraction against a real instance, and never claim a limitation without either a sharpness witness or a breadth caveat. Two threads carry this: eigenvalue arithmetic (Part 1, settled) and the bisimulation-boundary program around the encoding obstruction (Part 2, the current thesis and flagship paper).

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
