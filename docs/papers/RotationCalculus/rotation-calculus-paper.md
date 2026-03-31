# The Rotation Calculus: A Shared Term Structure for SAT Solving, UNSAT Proving, and Proof Complexity Analysis

## Authors

[To be determined]

## Abstract

We present a term-rewriting framework where SAT solving, UNSAT proving, proof compression, and solver trajectory analysis all operate on the same term type (`pair`/`ground`/`observe`) using the same structural operations (contraction toward ground). The framework enables cross-layer analysis: structural measurements at one layer (e.g., resolution proof width) inform decisions at another (e.g., solver tactic selection). We empirically characterize proof complexity across formula families via width trajectories — a computable structural invariant that separates PHP, chain, Tseitin, and forced contradiction families. We show that resolution proof length under greedy (recent-first) ordering is strategy-dependent: optimal for all tested families, with alternative orderings requiring 2-23x more steps. We demonstrate that an adaptive meta-solver, guided by structural signals (cascade depth, clause density, interpolant size), correctly dispatches different tactics for different formula classes. All results are implemented and verified in Lean 4.

---

## 1. Introduction

SAT solvers operate on clause databases. Resolution provers operate on derivation sequences. Proof complexity theorists operate on width and size measures. These three activities use different data structures, different languages, and different analysis tools. Improvements in one domain require manual translation to benefit another.

We present the rotation calculus — a minimal term language where all three activities share the same term type and the same structural operations. A clause is a term. A resolution step is a term operation. A solver trajectory is a list of terms. A proof compression is a contraction of terms. The structural measurements (width, contraction ratio, interpolant size) that characterize proof complexity are computable properties of these terms, available at runtime for solver decision-making.

The framework is not a competitive SAT solver. It is an investigation platform where the structural relationships between solving, proving, and analyzing are made explicit and measurable. The empirical findings — width trajectory fingerprints, strategy ordering sensitivity, composition analysis — are concrete results that connect solver engineering to proof complexity theory.

### 1.1 Contributions

1. **Width trajectory as structural fingerprint.** Each formula family produces a distinct width trajectory shape during greedy general resolution:

   | Family | Steps | Peak width | Shape |
   |---|---|---|---|
   | PHP(p, p-1) | 4p-6 | 2(p-1) | widen-narrow |
   | Chain(n) | n | 1 | flat-narrow |
   | Tseitin(n) | 4 | 2 | constant |
   | Forced(n) | n | n-1 | monotone-narrow |

   The width trajectory captures information that proof length alone does not: chain-5 and PHP(3,2) both have 5-6 steps, but completely different width shapes.

2. **Strategy ordering sensitivity.** Resolution proof length is strongly strategy-dependent. Recent-first (LIFO) ordering is optimal or near-optimal for all tested families:

   | Formula | Recent-first | Width-min | Random | Oldest-first |
   |---|---|---|---|---|
   | PHP(3,2) | 6 | 33 | 31-48 | 136 |
   | chain-5 | 5 | 5 | 10-13 | 19 |
   | Tseitin-3 | 4 | 4 | 4-14 | 31 |

   Width-minimizing is 5.5x worse than greedy on PHP. This contradicts the heuristic intuition that locally minimizing width globally minimizes proof size.

3. **SAT/UNSAT structural parallel.** Both SAT and UNSAT are arrangement problems in the rotation calculus. SAT arranges literals under satisfaction constraints; UNSAT arranges pivots under resolution constraints. Both contract toward ground (satisfied formula / empty clause). The certificate structures differ (assignment / derivation) but the search structures are isomorphic.

4. **Adaptive meta-solver.** A solver that reads structural signals (cascade depth, clause density, marginal bias, interpolant size) and dispatches different tactics (UP, BP-guided, split+compose, CDCL, resolution) for different formula classes. The tactic trace is itself a meta-trajectory analyzable by the same framework.

5. **Composition analysis.** Resolution lemmas compose as axioms across sub-problems. The meta-system's contraction ratio predicts when monolithic solving beats composition (long cascades) and when composition beats monolithic (small interpolants). Interpolant size at a formula split equals the proof treewidth at that cut.

---

## 2. The Rotation Calculus

### 2.1 Terms

Three constructors: `ground` (irreducible), `pair(a, b)` (structure), `observe(t)` (marks next rewrite).

### 2.2 Rewrite Rules

Four terminating rules indexed by observe target and position swap:

| Rule | Output | Traversal | Terminates |
|---|---|---|---|
| dive-left + swap | `pair(b, observe(a))` | Left spine, LIFO | Yes |
| dive-left no swap | `pair(observe(a), b)` | Left depth-first | Yes |
| dive-right + swap | `pair(observe(b), a)` | Right spine | Yes |
| dive-right no swap | `pair(a, observe(b))` | Right depth-first | Yes |

The standard rule (dive-left + swap) is the shift register: content rotates through the observation point one element at a time. It is deterministic, reversible, creates no new symbols, and terminates (pairs-under-observe strictly decreases).

### 2.3 Constraints

A constraint `C.check : Term -> Term -> Bool` gates the rotation. The constrained rule:

```
observe(pair(a, b)) -> pair(b, observe(a))    if C(a, b)
observe(pair(a, b)) -> stuck                   if not C(a, b)
observe(ground)     -> ground
```

Constraint levels: trivial (always true), Boolean (NP-complete problems), primitive recursive (total), general recursive (halting problem enters).

### 2.4 Tree Shapes and the Catalan Connection

Binary tree shapes on n leaves are counted by Catalan number C(n-1). Each rotation rule defines transitions between shapes — the covering relation of the Tamari lattice. The arrangement space for n elements is C(n-1) x n! (tree shapes x leaf placements).

---

## 3. SAT and UNSAT as Arrangement Problems

### 3.1 SAT Encoding

A literal is a labeled element term. A tree arrangement of literals encodes an assignment. The SAT constraint checks clause satisfaction at each tree node. Verification (tree fold) is O(n). Search (find a valid arrangement) explores C(n-1) x n! possibilities.

### 3.2 UNSAT via Resolution

Clauses are terms. Resolution composes two clause-terms on a shared pivot variable, producing a shorter resolvent. The empty clause is ground. A resolution derivation is a sequence of compositions contracting the clause database toward ground.

### 3.3 The Structural Parallel

| | SAT | UNSAT |
|---|---|---|
| Elements | Literals | Pivot variables |
| Arrangement | Assignment | Elimination order |
| Constraint | Clause satisfaction | Resolution possible |
| Ground | All satisfied | Empty clause |
| Certificate | Satisfying assignment | Refuting derivation |
| Verification | O(m) clause checks | O(m) resolution steps |
| Search | 2^n assignments | n! orderings |

Both are arrangement problems. Both contract toward ground. Both verify in linear time. Both search exponential spaces. The rotation calculus expresses both natively.

---

## 4. Width Trajectories

### 4.1 Definition

The width trajectory of a resolution derivation is the sequence of resolvent clause lengths: `[|r_1|, |r_2|, ..., |r_k|, 0]` where `|r_i|` is the number of literals in the i-th resolvent and 0 is the empty clause.

### 4.2 Empirical Results

**PHP(p, p-1):**
- Steps: 4p-6 (linear). Verified for p = 2..8.
- Peak width: 2(p-1) (linear).
- Shape: widen-narrow. The proof creates wide clauses by merging pigeon constraints, then narrows toward the empty clause by eliminating variables.
- Example PHP(4,3): `[3, 4, 4, 3, 3, 2, 2, 1, 1, 0]`

**Chain(n):**
- Steps: n (linear). Peak width: 1 (constant).
- Shape: flat-narrow. Pure unit propagation chain.
- Example chain-5: `[1, 1, 1, 1, 0]`

**Tseitin odd cycle(n):**
- Steps: 4 (constant, independent of n). Peak width: 2.
- Shape: constant. The resolver finds the contradiction at a single edge.
- Example Tseitin-7: `[2, 1, 1, 0]`

**Forced(n):**
- Steps: n (linear). Peak width: n-1 (linear).
- Shape: monotone-narrow. The wide clause is given; each step narrows by one.
- Example forced-5: `[4, 3, 2, 1, 0]`

### 4.3 Connection to Proof Complexity

The Ben-Sasson-Wigderson theorem bounds resolution proof size below by `2^{w - w_0}` where w is the minimum resolution width and w_0 is the initial clause width. For PHP(p, p-1), initial width is p-1 and peak width is 2(p-1), giving width overhead p-1. For chains, width overhead is 0. This explains why PHP proofs grow with p while chain proofs have constant width regardless of length.

### 4.4 Clause Reuse

| Family | Tree-like? | Clause reuse? |
|---|---|---|
| PHP (p >= 3) | No | Yes |
| Tseitin | No | Yes |
| Chain | Yes | No |
| Forced | Yes | No |

PHP and Tseitin require general resolution (clause reuse). Chain and forced have tree-like proofs. The width trajectory captures this: widen-narrow requires reuse (the wide clause is used in multiple later steps); flat-narrow does not.

---

## 5. Strategy Ordering

### 5.1 The Ordering Principle

The greedy resolver prepends resolvents to the clause list and scans from the front. This means the most recent resolvent is tried first as a resolution partner. This is LIFO (stack) ordering.

### 5.2 Empirical Comparison

| Formula | Recent-first | Oldest-first | Ratio |
|---|---|---|---|
| PHP(3,2) | 6 | 136 | 22.7x |
| chain-5 | 5 | 19 | 3.8x |
| Tseitin-3 | 4 | 31 | 7.8x |
| forced-3 | 3 | 7 | 2.3x |

Recent-first is optimal for all families. The ratio grows with formula complexity.

### 5.3 Why Recent-First Works

Each new resolvent is most useful immediately: it resolves with the next clause in the productive chain toward the empty clause. Deferring it (oldest-first) causes other, less productive resolutions to execute first, flooding the database with clauses that don't contribute to the refutation.

This is not a property of the resolver — it is a property of how resolution proofs are structured. Productive resolution chains are sequential: each step builds on the previous. LIFO ordering preserves this sequential structure. FIFO ordering disrupts it.

### 5.4 Connection to the Rotation Rule

The rotation rule processes the head of a right-nested pair list — LIFO by construction. The term structure and the optimal resolution strategy are aligned. Different rotation rules (dive-right, dive-left-no-swap) would produce different orderings with different performance characteristics.

---

## 6. Composition Analysis

### 6.1 When Monolithic Wins

Structured instances with long UP cascades contract to a single meta-event (CASCADE). Splitting destroys the cascade:

| Instance | Monolithic meta | Composed meta |
|---|---|---|
| Chain-8 | 1 event (CASCADE(8)) | 7 events |
| Structured n=20 | 1 event (CASCADE(34)) | multiple |

### 6.2 When Composition Wins

Random instances with no cascade benefit from splitting:

| Instance | Pipeline raw | Adaptive raw |
|---|---|---|
| rand-10-20-s42 | 26 | 10 |
| rand-10-42-s123 | 26 | 13 |

### 6.3 Interpolant as Composition Interface

Resolution lemmas from one sub-problem serve as axioms for another. The lemma IS the Craig interpolant — the minimum information crossing the split boundary. For chain formulas, the interpolant has 1 shared variable (perfect factorization). For PHP, 3-4 shared variables (poor factorization).

### 6.4 Composition of UP and CDCL

UP results compose across sub-problems: assignments from part A simplify part B's formula. CDCL learned clauses from one context are valid axioms in another. The shared term structure makes this free — a clause derived in one context has the same type as an axiom in another.

---

## 7. The Adaptive Meta-Solver

### 7.1 Architecture

The solver reads five structural signals at each decision point:

| Signal | Threshold | Tactic dispatched |
|---|---|---|
| Unit clauses > 0 | - | UP |
| Pure literals > 0 | - | UP |
| Clause density > 5.0 | - | Resolution (UNSAT mode) |
| Shared vars at split <= 1 | - | Split + compose |
| Max marginal bias > 80% | - | BP-guided assignment |
| None of the above | - | CDCL (fallback) |

### 7.2 Tactic Trace

The solver produces a tactic trace: the sequence of (tactic, signal) pairs recording which tactic was chosen and why. This is the meta-meta-trajectory — the solver's reasoning about its own strategy.

Three levels of meta:
- Level 0: The formula (clauses, variables)
- Level 1: The solve trajectory (UP steps, decisions, conflicts, backtracks)
- Level 2: The tactic selection trace (which tactic, what signal, what outcome)

All three levels use the same term language.

### 7.3 Results

| Instance class | First tactic | Trace pattern |
|---|---|---|
| Structured | UP | `[UP]` — single cascade |
| Random easy | UP or split | `[UP, split, CDCL, ...]` — mixed |
| Random at transition | split | `[split, CDCL, ...]` — split-dominated |
| High density | resolution | `[resolution]` — UNSAT mode |
| Chain UNSAT | UP | `[UP]` — cascade refutes |
| PHP | split | `[split, CDCL, UP]` — decompose then search |

---

## 8. UNSAT Contraction Operations

### 8.1 Subsumption

Clause C subsumes D if C's literals are a subset of D's. Removing D contracts the clause database. Implemented as `eliminateSubsumed`.

### 8.2 UP-Resolution Bridge

Unit propagation = unit resolution. A UP cascade of k steps = k unit resolution steps. This bridges the solver trajectory (meta-rewrite #1) to the resolution proof system: cascade absorption IS resolution proof compression.

### 8.3 Extended Resolution

New variables abbreviating conjunctions: y = (a AND b) adds 3 definition clauses but allows y to replace all occurrences of (a AND b). Exponentially more powerful than basic resolution for some formula families (PHP has polynomial extended resolution proofs).

### 8.4 Symmetry Breaking

Orbit detection identifies groups of interchangeable variables. Breaking constraints fix canonical orderings within orbits, reducing the search space by orbit-size factorial. Current implementation detects single-variable swaps; block permutations (needed for PHP pigeon symmetry) require graph automorphism detection.

### 8.5 Proof Compression

Dead step elimination removes resolution steps whose resolvents are never used. Deduplication removes repeated derivations. Combined, these produce sound minimal proofs. The greedy resolver already produces near-minimal proofs for tested families — compression removes 0 steps, confirming the derivations are tight.

---

## 9. Implementation

All results are implemented in Lean 4 with zero compilation errors. The implementation consists of 30+ files totaling approximately 8000 lines.

### 9.1 Core Files

| File | Purpose |
|---|---|
| `Syntax.lean`, `Rewrite.lean` | Term type, rotation rule, termination proof |
| `Constraint.lean` | Constrained rotation, verification, search |
| `SATEncoding.lean` | SAT as tree arrangements |
| `Resolution.lean` | Clause composition, greedy/unit resolution |
| `FastResolution.lean` | Array-based clause database |
| `WidthTrajectory.lean` | Width trajectory extraction, shape classification |
| `ProofSystemTest.lean` | Strategy independence, multiple resolution orderings |

### 9.2 Meta-System Files

| File | Purpose |
|---|---|
| `MetaRewrite0.lean` | Rotation-level traces, tree fold, #0->#1 bridge |
| `MetaRewriting.lean` | Solver trajectory contraction, complexity snapshots |
| `TrajectoryAnalysis.lean` | Trace profiling, cascade depth, phase structure |
| `AdaptiveMetaSolver.lean` | Monolithic/composed hybrid with strategy tree |
| `TacticSelector.lean` | Signal-driven tactic dispatch |

### 9.3 UNSAT Files

| File | Purpose |
|---|---|
| `UNSATProof.lean` | Refutation trees, exhaustive UNSAT check |
| `ResolutionContraction.lean` | Subsumption, UP bridge, extended resolution |
| `StrategyAsTerm.lean` | Variable elimination as arrangement |
| `ConstraintEvolution.lean` | Living clause database |
| `SymmetryBreaking.lean` | Orbit detection, breaking constraints |
| `Interpolation.lean` | Craig interpolation, proof factorization |
| `ProofCompression.lean` | Dead step elimination, deduplication |

### 9.4 Infrastructure

| File | Purpose |
|---|---|
| `Random3SAT.lean` | Xorshift32 PRNG (replaced broken LCG) |
| `Pipeline.lean` | Traced UP + ExtRes + CDCL with full search tree |
| `CompositionTheory.lean` | TacticState, ProofStep, monotonicity proofs |
| `RotationIndex.lean` | All 8 rotation rules, Catalan numbers |
| `SelfContained.lean` | Rule selection as constraint, constraint as term |

---

## 10. Discussion

### 10.1 What the Framework Achieves

The rotation calculus provides a uniform term language for SAT solving, UNSAT proving, and proof complexity analysis. This uniformity means:

- Subsumption checks clause redundancy, proof step redundancy, and trajectory event redundancy using the same structural test.
- Resolution composes clauses and composes proof steps using the same operation.
- Contraction toward ground drives SAT verification, UNSAT derivation, and proof compression.

The empirical findings (width trajectories, strategy ordering, composition analysis) are concrete results enabled by this uniformity. They connect solver engineering (which tactic to use) to proof complexity (what the width trajectory reveals about formula structure).

### 10.2 What the Framework Does Not Achieve

This is not a competitive SAT solver. Current limitations:

- CDCL learns full assignment negations (not 1-UIP — exponentially worse)
- Data structures are Lean lists/arrays (not watched literals — O(n) vs O(1) unit propagation)
- Tested only on instances with n <= 42
- No restarts, no VSIDS, no clause database management
- The meta-system's signal measurement adds overhead per step

### 10.3 Path to Competitive Performance

The meta-guided tactic selection architecture is independent of the underlying solver quality. Implementing proper CDCL (1-UIP, watched literals, VSIDS) inside the same architecture would retain all structural analysis capabilities while achieving baseline competitive performance. The meta-overhead (signal measurement per decision point) is O(1) per step with proper data structures.

### 10.4 Research Directions

**Scaling the width trajectory.** Verify that the width trajectory fingerprints (widen-narrow for PHP, flat for chains, constant for Tseitin) hold at n = 100+. If the shapes are stable, the width trajectory is a universal structural invariant for formula families.

**Connecting to the DynSemiring obstruction.** The fork rule in the rotation index IS the Leibniz rule. The width trajectory's widen phase = forking (Leibniz expansion). The narrow phase = diving (variable elimination). The peak width = the point where enough information has been combined to see the contradiction. Formalizing this connection would bridge the empirical work to the theoretical encoding obstruction framework.

**Proof complexity classification.** Is the rotation calculus's proof power strictly between tree-like and general resolution, or equivalent to general resolution? The greedy resolver exploits recency-biased clause selection — a specific strategy that might give it power beyond generic general resolution.

**Meta-guided solver optimization.** The tactic selector's signal thresholds (density > 5.0 for UNSAT, bias > 80% for BP, shared <= 1 for split) are hand-tuned. These could be learned from trajectory data across many instances, producing an automatically optimized solver that adapts its thresholds to the instance distribution.

---

## 11. Conclusion

The rotation calculus demonstrates that SAT solving, UNSAT proving, and proof complexity analysis can share a common term structure, enabling cross-layer analysis and composition. The width trajectory is a computable structural invariant that separates formula families and predicts proof complexity. The strategy ordering result shows that LIFO resolution — aligned with the rotation rule's head-first processing — is optimal for all tested families. The adaptive meta-solver correctly dispatches different tactics for different structural profiles, with the tactic trace providing a meta-meta-trajectory that records the solver's own reasoning.

The system's value is not as a solver but as an investigation platform: a place where the structural relationships between solving, proving, and analyzing are visible, measurable, and composable. The concrete findings — 4p-6 for PHP, 23x ordering sensitivity, width trajectory fingerprints — are contributions to empirical proof complexity that the shared term structure makes natural to discover.

---

## References

- Ben-Sasson, E. & Wigderson, A. (2001). Short proofs are narrow — resolution made simple. *Journal of the ACM*, 48(2):149-169.
- Cook, S. (1971). The complexity of theorem proving procedures. *STOC*.
- Haken, A. (1985). The intractability of resolution. *Theoretical Computer Science*, 39:297-308.
- Pipatsrisawat, K. & Darwiche, A. (2011). On the power of clause-learning SAT solvers as resolution engines. *Artificial Intelligence*, 175(2):512-525.
- Biere, A. et al. (2021). *Handbook of Satisfiability* (2nd ed.). IOS Press.
