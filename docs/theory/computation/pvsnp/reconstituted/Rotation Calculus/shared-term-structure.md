# Shared Term Structure: Beyond SAT Solving

## Date: 2026-03-31

## Summary

The rotation calculus is not a SAT solver. It is a term language in which SAT solving, UNSAT proving, proof compression, constraint evolution, and trajectory analysis are all the same structural operation — contraction toward ground — applied to terms at different layers.

The shared term structure means techniques compose across layers without ad-hoc interfaces. Subsumption checks clause redundancy, proof step redundancy, and trajectory event redundancy using the same structural test. Resolution composes clauses and composes proof steps using the same operation. Contraction toward ground drives SAT verification, UNSAT derivation, and proof compression using the same rewrite rule.

This document records what was built, what the data shows, and where the structural leverage exists.

---

## Part 1: The Layer Architecture

Every component of the system operates on the same term type: `pair`/`ground`/`observe`. The terms represent different objects at different layers, but the operations are structurally identical.

| Layer | Terms represent | Operation | Contracts toward |
|---|---|---|---|
| Data | Literals, arrangements | Constrained rotation | Ground (all checks pass) |
| Clauses | Disjunctions of literals | Resolution composition | Empty clause |
| Strategy | Pivot order / selector | Strategy execution | Refutation |
| Constraint | Accepted pairs | Evolution (learned clauses) | Stronger constraint |
| Proof | Derivation steps | Compression | Minimal proof |
| Trajectory | Solver events | Meta-rewrite | Contracted trace |

Each layer's contraction is the same pattern:

```
observe(pair(a, b))  →  pair(b, observe(a))     if constraint(a, b)
observe(pair(a, b))  →  stuck                    if ¬constraint(a, b)
observe(ground)      →  ground                   (contraction complete)
```

The constraint changes at each layer:
- Data layer: does this literal assignment satisfy the clause?
- Clause layer: do these two clauses share a resolvable variable?
- Strategy layer: does eliminating this variable make progress?
- Proof layer: is this step necessary for the final derivation?

---

## Part 2: What Was Built

### Infrastructure fixes (enabling the investigation)

| File | Change | Why |
|---|---|---|
| `Random3SAT.lean` | Replaced LCG with xorshift32 | LCG produced only odd variables and negative polarities. Phase transition invisible. |
| `CompositionTheory.lean` | Added `ProofStep.conflict` and `ProofStep.backtrack` | CDCL search tree was invisible. |
| `Pipeline.lean` | `cdclSearchTraced` replaces brute-force re-enumeration | Decisions/conflicts/backtracks now recorded during actual search. |

### Meta-rewrite systems

| File | System | What it does |
|---|---|---|
| `MetaRewrite0.lean` | #0 (rotation-level) | Traces rotation steps and tree-fold checks. Two execution models: rotation (list traversal) vs tree fold (catamorphism). Bridges to #1 via `rotationToMeta`. |
| `MetaRewriting.lean` | #1 (solver-trace) | Complexity snapshots + meta-events (CASCADE, SEARCH, CONFLICT_CYCLE, ABSTRACTION). Contraction ratio = raw trace / meta trajectory. |
| `TrajectoryAnalysis.lean` | Trajectory metrics | `TraceProfile`, `maxCascade`, `phaseStructure`, `freePre`, `formulaGrowth`. Hypothesis testing infrastructure. |
| `TrajectoryLargeScale.lean` | Scaling tests | Structured n=8..50, random density sweeps, UP-then-CDCL decomposition. |

### Rotation calculus extensions

| File | Extension | What it adds |
|---|---|---|
| `RotationIndex.lean` | Rule family | 8 rules indexed by observe target and swap. 4 terminating rules. Catalan numbers. Tamari lattice connection. |
| `SelfContained.lean` | A: Rule selection | `Selector` chooses dive-left vs dive-right at each node. Traversal order = search object. `selectorSearch` finds valid direction sequences. |
| `SelfContained.lean` | C: Constraint as term | `TermConstraint` — constraint encoded as rotation calculus term. Checking IS a term operation. `RotationProblem` = constraint + data + selector, all terms. |

### UNSAT proof systems

| File | System | What it does |
|---|---|---|
| `UNSATProof.lean` | Exhaustive + refutation tree | Brute-force verification that all arrangements fail. `Refutation` inductive type records WHY. |
| `Resolution.lean` | Basic resolution | `resolveClauses`, `greedyResolution`, `unitResolution`. Resolution as contraction toward empty clause. |
| `ResolutionContraction.lean` | Subsumption + UP bridge + ExtRes | `eliminateSubsumed`, `unitCascadeAsResolution`, `Extension` + `applyExtension`. |
| `StrategyAsTerm.lean` | Head-tape unification | Variable elimination order as arrangement term. `executeStrategy`, `strategyRefutes`, `searchStrategy`. SAT and UNSAT both as arrangement problems. |
| `ConstraintEvolution.lean` | Living constraints | `EvolvingState`, `evolvingResolution`, `evolutionTrajectory`. Clause database grows during search. |
| `SymmetryBreaking.lean` | Orbit detection + breaking | `areSymmetric`, `symmetryOrbits`, `generalSymmetryBreakers`, `orbitResolution`. |
| `Interpolation.lean` | Craig interpolation | `splitFormula`, `extractInterpolant`, `InterpolantMetrics`. Interpolant size = proof treewidth. |
| `ProofCompression.lean` | Dead step + dedup + collapse | `eliminateDeadSteps`, `deduplicateSteps`, `collapseSubsumedChains`. Combined pipeline. |

---

## Part 3: Empirical Results

### Trajectory signatures (with fixed PRNG and CDCL trace)

| Instance class | Free% | Cascade | Decisions | Conflicts | Backtracks |
|---|---|---|---|---|---|
| Structured n=50 | 100% | 84 | 0 | 0 | 0 |
| Random m/n=1 | 70% | 7 | 3 | 0 | 0 |
| Random m/n=2 | 0-37% | 0-6 | 5-13 | 1-3 | 1-3 |
| Random m/n=4.2 | 0% | 0 | 0-13 | 1-3 | 0-3 |
| PHP UNSAT | 0% | 0 | 0 | 1 | 0 |

### Meta-rewrite #1 contraction

| Instance | Raw trace | Meta events | Contraction |
|---|---|---|---|
| Structured n=30 | 49 | 1 | 49x |
| Random m/n=2 | 16-26 | 7-14 | 1.6-2.3x |
| UNSAT | 4-6 | 2-4 | 1.5x |

### Phase transition (CDCL cost vs density, n=12)

| m/n | Avg cost | Avg learned | SAT rate |
|---|---|---|---|
| 1.0 | 15 | 1 | 5/5 |
| 3.0 | 78 | 34 | 5/5 |
| 4.2 | 193 | 93 | 4/5 |
| 5.0 | 348 | 173 | 2/5 |
| 6.0 | 293 | 145 | 2/5 |

### Resolution proof compression

| Formula | Basic proof | Compressed | Ratio |
|---|---|---|---|
| (x0)(NOT x0) | 1 | 1 | 1.0x |
| chain-3 | 2 | 1 | 2.0x |
| chain-5 | 5 | 1 | 5.0x |
| PHP(3,2) | 6 | 2 | 3.0x |
| PHP(4,3) | 10 | 2 | 5.0x |

### Interpolation (UNSAT proof factorization)

Chain formula (treewidth 1): 1 shared variable at every split point. Interpolant size 1-2. Proof factorizes perfectly.

PHP(3,2): 3-4 shared variables. Interpolant size 4-6. Proof does not factorize.

---

## Part 4: The Structural Parallel

SAT and UNSAT are both arrangement problems in the rotation calculus:

| | SAT | UNSAT |
|---|---|---|
| Elements | Literals | Pivot variables |
| Arrangement | Assignment | Elimination order |
| Constraint | Clause satisfaction | Resolution possible |
| Ground | All satisfied | Empty clause derived |
| Certificate | Satisfying assignment | Refuting derivation |
| Verification | O(m) clause checks | O(m) resolution steps |
| Search | 2^n assignments | n! orderings |

Both use the same term language. Both contract toward ground. Both verify in linear time given the certificate. Both search exponential spaces.

The difference: SAT contracts DATA (the arrangement) under a STATIC constraint. UNSAT contracts CONSTRAINTS (the clause database) through EVOLVING resolution. The constraint at step k depends on what was derived at steps 1..k-1.

---

## Part 5: Where the Structural Leverage Exists

### Cross-layer contraction

The same structural operation applies at multiple layers:

**Subsumption** (is X a sub-term of Y?):
- Clause layer: clause C subsumes D if C's literals are a subset of D's. Remove D.
- Proof layer: step k's resolvent subsumes step j's parent. Remove step j.
- Trajectory layer: a cascade of n UP steps subsumes n individual UP events. Contract to CASCADE(n).

**Resolution** (compose two objects on a shared element):
- Clause layer: resolve C1 and C2 on pivot variable x. Produce resolvent.
- Proof layer: combine two sub-derivations that share a lemma. Produce shorter derivation.
- Strategy layer: combine two elimination orders that share a prefix. Produce merged strategy.

**Dead elimination** (remove objects that don't contribute to the conclusion):
- Clause layer: remove clauses not on any resolution path to empty clause.
- Proof layer: remove steps whose resolvents are never used.
- Trajectory layer: remove search events that were undone by backtracking (the "failed" branch).

Each of these is implemented once and applies at every layer because the structure is the same.

### What SAT solvers cannot express

A conventional SAT solver has:
- A clause database (data structure, language-specific)
- A search procedure (algorithm, implementation-specific)
- A proof logger (output format, tool-specific)
- A restart policy (heuristic, tuning-specific)

These are separate systems with ad-hoc interfaces. The clause database doesn't know about the proof logger. The search procedure doesn't know about the restart policy's interaction with learned clauses. Improvements in one system require manual integration with others.

In the rotation calculus:
- The clause database IS a term
- The search procedure IS a rotation with a selector
- The proof IS a sequence of term compositions
- The restart IS a meta-rewrite contraction

They compose because they're the same structural operation. A contraction technique discovered at the proof layer (e.g., dead step elimination) automatically applies at the clause layer (dead clause elimination) because both are the same check on the same term type.

### The specific leverage found

Proof compression on PHP(4,3) achieves 5x contraction (10 steps to 2). This contraction is discovered at the proof layer but could not be discovered at the clause layer alone — it requires seeing the WHOLE derivation to identify that 8 of the 10 steps are dead (their resolvents are never used in the final path to empty clause).

The meta-rewrite #1 on structured instances achieves 49x contraction (49 steps to 1 CASCADE event). This is discovered at the trajectory layer but corresponds exactly to cascade absorption at the clause layer — 49 unit resolutions that are individually necessary but collectively form a single deterministic sweep.

Both contractions are instances of the same pattern: recognizing that a sequence of operations is redundant when viewed from a higher layer.

---

## Part 6: What Does Not Work Yet

### Symmetry detection for PHP

The `areSymmetric` function tests single variable swaps. PHP's symmetry involves grouped permutations (swapping entire pigeon variable blocks). The machinery is in place but the detector needs to handle block permutations. Practical symmetry tools (saucy, bliss) work on the clause-variable incidence graph.

### Evolving resolution on PHP

The greedy evolving resolver accumulates ALL possible resolvents, flooding the database (59 clauses at fuel 50, none empty). The basic greedy resolver solves PHP(3,2) in 6 steps by picking good clause pairs. The evolution mechanism is correct but needs strategy guidance — which brings the strategy and evolution layers into contact.

### Variable elimination as UNSAT strategy

The `executeStrategy` function eliminates variables in order, resolving all pairs on each pivot. For PHP, 0/720 orderings derive empty clause. Variable elimination order is too coarse — the strategy needs to specify clause pairs, not just pivots. This is a known limitation of variable elimination (DP algorithm) vs. clause-pair resolution.

### Extended resolution benefit

Extended resolution (introducing abbreviation variables) adds 3 definition clauses per abbreviation. On small instances, this overhead outweighs the compression. The benefit is exponential and only appears at scale — PHP(n, n-1) has polynomial extended resolution proofs but requires exponential basic resolution.

---

## Part 7: Open Directions

### Combining strategy with evolution

The strategy tells the resolver WHAT to do. Evolution tells it what BECAME POSSIBLE. Combining them: the strategy guides evolution (only derive useful resolvents), and evolution informs strategy (newly derived clauses open new elimination paths). This is what CDCL does implicitly. Making it explicit in the rotation calculus would unify items 1 and 2.

### Quantifier structure

SAT is existential (there exists an arrangement). UNSAT is universal (all arrangements fail). The rotation calculus has no quantifier — it has arrangements (existential) and derivations (universal by exhaustion). A native quantifier over arrangements would make UNSAT expressible without exhaustive search. This connects to the descriptive complexity characterization: NP = existential second-order logic, coNP = universal second-order logic.

### Proof complexity measures in the rotation calculus

The compression ratio (original / compressed) is a proof complexity measure. The interpolant size is another. These are computable structural properties of terms. Whether they connect to standard proof complexity measures (resolution width, depth, space) is open and would bridge the rotation calculus to the proof complexity literature.

### Self-application to harder instances

All results are on instances with n <= 12. The structural findings (contraction ratios, factorization, compression) may or may not scale. Testing on n=20..50 random instances near the phase transition would reveal whether the cross-layer leverage persists at scale or is an artifact of small instances.

---

## Related

- [trajectory-analysis.md](trajectory-analysis.md) -- Empirical trajectory analysis, PRNG fix, CDCL trace fix
- [conception.md](conception.md) -- Rotation calculus design principles
- [04-complexity.md](04-complexity.md) -- P vs NP in the rotation calculus
- [00-overview.md](00-overview.md) -- Overview of the rotation calculus
- [../../nand-jit-obs-placement.md](../../nand-jit-obs-placement.md) -- JIT obs placement, certificates as pruning
- [../../encoding-complexity.md](../../encoding-complexity.md) -- P vs NP as encoding execution
- [../../assessments/pvsnp-framework-assessment.md](../../../assessments/pvsnp-framework-assessment.md) -- Framework assessment
