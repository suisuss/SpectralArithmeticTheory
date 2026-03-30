# Plan: Meta-Rewriting — Constraint Evolution with Complexity Trajectories (#16)

## Context

The rotation calculus pipeline (UP → ExtRes → UP → CDCL) already modifies the formula during search — CDCL learns clauses, UP removes satisfied clauses, ExtRes creates abstractions. But these modifications are invisible: the pipeline reports only final cost. There's no record of *how* the constraint changed, *when* it changed, or whether it got easier or harder.

Meta-rewriting makes constraint evolution a **first-class observable**. The trajectory — a time series of complexity snapshots paired with modification events — is the new data structure. This lets the language express things it currently can't: "the formula grew before it shrank," "free inference ran out after step 3," "density crossed the phase transition mid-search."

**Honest framing:** This is instrumentation, not a new algorithm. The solver doesn't get faster. The solver's behavior becomes measurable over time. The genuinely new contribution is the trajectory as a structured proof artifact.

## Implementation: One new file

**File:** `SpectralArithmetic/Rotation/MetaRewriting.lean`
**Import:** `SpectralArithmetic.Rotation.Pipeline`
**Also modify:** `SpectralArithmetic.lean` (add import line)

## Types

```lean
structure ComplexitySnapshot where
  clauseCount  : ℕ    -- |F|
  varCount     : ℕ    -- unassigned variables remaining
  assignCount  : ℕ    -- assignments made so far
  unitCount    : ℕ    -- available unit clauses (free inference potential)
  pureCount    : ℕ    -- available pure literals
  density      : ℕ    -- clauseCount * 1000 / max(varCount, 1) — milliths, no Float

inductive MetaEvent where
  | learn     : SATClause → MetaEvent
  | abstract  : ℕ → List ℕ → MetaEvent
  | simplify  : ℕ → MetaEvent          -- UP/pure eliminated n clauses
  | cascade   : ℕ → MetaEvent          -- UP cascade forced n assignments
  | decide    : ℕ → Bool → MetaEvent

structure TrajectoryPoint where
  event : MetaEvent
  pre   : ComplexitySnapshot
  post  : ComplexitySnapshot

structure MetaState where
  tactic     : TacticState
  trajectory : List TrajectoryPoint

abbrev MetaTactic := MetaState → MetaState
```

## Functions

### Core
- `takeSnapshot : TacticState → ComplexitySnapshot` — measure current state (calls `findUnits`, `findPureLiterals`)
- `MetaTactic.seq : MetaTactic → MetaTactic → MetaTactic` — composition

### Instrumented tactics (wrap existing TracedTactics)
- `metaUp : MetaTactic` — wraps `upFixpoint`, emits `cascade` events
- `metaExtRes : ℕ → MetaTactic` — wraps `extResTraced`, emits `abstract` events
- `metaCDCL : MetaTactic` — wraps `cdclTraced`, emits `learn`/`decide` events
- `metaPipeline : ℕ → MetaTactic` — `metaUp.seq (metaExtRes.seq (metaUp.seq metaCDCL))`
- `runMeta : SATFormula → ℕ → ℕ → MetaState` — entry point

### Analysis
- `Trajectory.summary : List TrajectoryPoint → String` — human-readable printout
- `Trajectory.clausePath : List TrajectoryPoint → List ℕ` — clause count over time
- `Trajectory.densityPath : List TrajectoryPoint → List ℕ` — density over time
- `Trajectory.freeInferencePotential : List TrajectoryPoint → List (ℕ × ℕ)` — (units, pures) over time
- `Trajectory.eventCounts : List TrajectoryPoint → String` — count by event type
- `Trajectory.formulaGrew : List TrajectoryPoint → Bool` — did clause count ever increase?

### CDCL granularity note
The current `cdclSearch` returns all learned clauses at once. Rather than modifying it, post-process: emit one `learn` event per returned learned clause with the pre-snapshot from before CDCL and post-snapshot from after. This is approximate (individual clause pre/post aren't measured) but avoids invasive changes to existing code.

## `#eval` Demonstrations

1. **Structured (reachInstance 10 3)** — expect: one large cascade, zero decisions, trajectory length ~1-2
2. **Random 3-SAT (n=8 m=32 seed=42)** — expect: short cascade then decisions, mixed trajectory
3. **PHP(3,2) UNSAT** — expect: formula GROWS (learned clauses), density increases, `formulaGrew = true`
4. **Cross-instance comparison** — structured vs random vs UNSAT side-by-side: events, clauseΔ, varΔ, formulaGrew
5. **Phase transition sweep** — vary clause density, show trajectory length peaking near transition

## What the trajectory reveals

| Observable | Structured | Random SAT | UNSAT |
|-----------|-----------|-----------|-------|
| Formula direction | shrinks | shrinks | **grows** |
| Free inference | dominates | partial | absent |
| Density path | drops fast | stays near transition | rises |
| Trajectory length | short (1-2) | medium | long |
| Events | cascade only | cascade + decide | learn + decide |

The SAT/UNSAT qualitative difference (shrink vs grow) is invisible in the current pipeline output. The trajectory makes it a measurable structural signature.

## What this does NOT do

- Does not make the solver faster (adds O(events x |formula|) overhead)
- Complexity snapshots are heuristic proxies, not formal complexity measures
- Trajectory depends on execution path (different variable orderings -> different trajectories)
- Does not prove anything about P vs NP

## Verification

1. `lake build` — must compile with zero errors
2. All five `#eval` blocks must produce output
3. Structured instances should show cascade-dominated trajectories
4. PHP should show `formulaGrew = true`
5. Existing tests unaffected (no modifications to existing files except one import line)
