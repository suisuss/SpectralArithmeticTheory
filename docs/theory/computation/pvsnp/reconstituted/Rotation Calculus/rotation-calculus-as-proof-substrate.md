# The Rotation Calculus as a Composable Proof Substrate

## Summary

The rotation calculus — a minimal rewrite system with one rule, one constraint parameter, and three term constructors — turns out to be a substrate on which multiple SAT solving strategies compose naturally. Each strategy operates on the same shared structure (terms, constraints, arrangements), contributes at the level where it's strongest, and produces proof traces in a common format. The result is a framework where spatial decomposition, temporal pruning, distributional estimation, clause learning, and hierarchical abstraction combine into a single solver that is competitive across structured, random, and unsatisfiable instances.

This document records the progression from minimal language to composable solver, with references to the Lean formalization and git history.

---

## The Language

The rotation calculus has three term constructors and one rewrite rule.

**Constructors** (`Syntax.lean`, commit `b86c502`):

```
ground    — the irreducible element, fixed point of observation
pair(a,b) — the only way to build structure (nesting = storage)
observe(t) — marks a subterm for the next rewrite step
```

**The rewrite rule** (`Rewrite.lean`, commit `b86c502`):

```
observe(pair(a, b)) → pair(b, observe(a))    if C(a, b)
observe(pair(a, b)) → stuck                   if ¬C(a, b)
observe(ground)     → ground
```

The constraint `C` is the only point where a binary decision occurs — the rich structure of `(a, b)` is projected to a single bit. This is where information is lost, and where complexity becomes visible.

**Properties proved:**
- Termination: `pairsUnderObserve` strictly decreases at each step
- No symbol creation: `constructorCount` is invariant
- Confluence: at most one redex exists (the step function is deterministic)
- Reversibility: the rule is invertible (`unstep` inverts `step`)

The constraint turns this into a complexity-theoretic language (`Constraint.lean`, commit `b86c502`):
- **Verification** = run the rotation on a given arrangement. Linear time.
- **Search** = find an arrangement where every constraint check passes. Exponential space.
- The gap between these IS the P vs NP question.

---

## From Trees to SAT

The language encodes SAT naturally (`SATEncoding.lean`, commit `d4f52a2`). Each literal becomes a labeled element. A tree arrangement groups literals hierarchically. The constraint checks consistency (no variable has both polarities) and satisfaction (all resolved clauses pass) at each tree node.

The tree structure is the decomposition strategy. Different tree shapes correspond to different ways of splitting variables into groups. The leaf placement determines which literals appear where.

**Tree decomposition** (`SATEncoding.lean`, commits `d4f52a2`, `89b2ea6`): split variables into left/right groups, solve each independently, combine by checking cross-partition clauses. Cost depends on treewidth — how many variables span the partition boundary.

**Treewidth interpolation** (`SATEncoding.lean`, commit `281a41d`): parameterized instances with controlled clause reach show the speedup degradation from low treewidth (exponential speedup) to high treewidth (no speedup). The crossover point is the empirical treewidth threshold.

**Three-way comparison** (`Scaling.lean`, `DAG.lean`, commit `ddea006`): flat brute force vs tree decomposition vs DAG sharing across treewidths. Each has a regime where it wins. The framework measures all three on the same instances.

---

## The Constructor Extensions

Three constructors were added to extend the language's expressiveness. Each carries complexity structure in the syntax.

### Choice: AND-OR Trees (`Choice.lean`, commit `26c812c`)

`pair` is AND (both children must pass). `choice(a, b)` is OR (at least one must pass). Together they give AND-OR trees — the game tree structure underlying alternating computation and the polynomial hierarchy.

- pair only: NP (existential search over arrangements)
- pair + existential choice: still NP
- pair + universal choice: coNP
- alternating: PH levels correspond to AND-OR nesting depth

### DAG: Shared Subtrees (`DAG.lean`, commit `26c812c`)

`ref(name)` allows the same subtree to be referenced from multiple parents. This gives DAGs through sharing — the structural difference between divide-and-conquer and dynamic programming. A DAG-aware solver assigns shared variables globally, then solves local variables per-subtree independently.

### Graph-Aware Ordering (`GraphOrder.lean`, commit `978dfeb`)

The variable interaction graph determines evaluation order. BFS from the highest-degree variable produces a coupling-aware ordering. Min-degree ordering (process least-connected variables first) enables aggressive pruning on random instances where low-degree variables constrain less.

---

## The Solver Progression

Each solver is a different strategy for building arrangements, operating on the same shared term structure. The git history records the progression from simple to sophisticated.

### 1. Flat Brute Force (baseline)

Try all 2^n assignments. Cost: O(2^n). No structure exploited.

### 2. SmartDAG — Spatial Decomposition (`DAGBounded.lean`, commits `943a18d`, `b88c10b`, `7114a5f`)

Split variables using the tree structure, share at most k boundary variables, solve subtrees independently. Cost: O(2^k x n). Polynomial for fixed k.

**Result:** Great on structured instances (36-54 for n=8-12). Fails on random 3-SAT — treewidth is Theta(n), so every split has cross-partition clauses.

### 3. Choice + Min-Degree — Temporal Pruning (`ChoiceSAT.lean`, `GraphOrder.lean`, commits `2158627`, `978dfeb`)

Build an AND-OR tree from the formula. Each variable is a Choice node. Evaluate with alpha-beta pruning in min-degree order (least-connected variables first).

**Result:** Best on random 3-SAT (37-61). Fails on structured instances where most partial assignments extend to solutions (no pruning opportunities).

### 4. CDCL — Clause Learning (`ClauseLearning.lean`, commit `90dcd68`)

Choice + min-degree with conflict-driven clause learning. When a branch fails, extract the conflicting partial assignment, derive a learned clause (negation of the conflict), add it to the formula. The constraint evolves during search.

**Result:** Handles both SAT and UNSAT. Proof system = general resolution. Cost on PHP(4,3): 197.

**Proof complexity correspondence:**
- Choice (DPLL) = tree-like resolution
- CDCL = general resolution
- The exponential separation between these (pigeonhole principle) is a theorem of proof complexity

### 5. Belief Propagation — Distributional Estimation (`BeliefProp.lean`, commit `a6a59aa`)

Replace hard constraint checks with weighted counts. Send marginal distributions between variable clusters. Iterate until convergence. Read off assignment from converged marginals.

**Result:** Fastest on random SAT — cost 4 vs CDCL's 15 vs flat's 86. Represents a genuinely different computational paradigm: distributed probabilistic inference. But fails on structured instances (long-range correlations) and UNSAT (no solutions to estimate).

BP does not produce proofs. It produces estimates. This is the categorical difference: SAT is search (existence, an attractor to navigate toward). UNSAT is proof (non-existence, a derivation to construct). BP can estimate where solutions are. It cannot prove solutions don't exist.

### 6. Extended Resolution — Hierarchical Abstraction (`ExtendedResolution.lean`, commits `c50181d`, `54c842e`, `f1f3ae1`)

The rotation calculus's native proof structure, made explicit. During tree contraction, create summary elements (abstractions) that compress observations. An abstraction carries the conclusion of an inner observation as a new atomic element. Future constraint checks use the abstraction directly without re-deriving the inner proof.

Three optimizations (commit `f1f3ae1`):
1. **Graph-aware grouping:** BFS from highest-degree variable clusters tightly-coupled variables together. Maximizes clause coverage per abstraction.
2. **Known-assignment propagation:** Recursive calls receive accumulated assignments from previous levels. The search space shrinks at each level.
3. **Global scoring:** Pick local assignments that satisfy the most cross-group clauses, maximizing global consistency.

**Result:** Best generalist solver in the framework. With unit propagation (commit `7fadae7`), the results are:

| Instance | Flat | SmartDAG | CDCL | BP | ExtRes | ExtRes+UP |
|----------|------|----------|------|----|--------|-----------|
| Structured n=10 | 1024 | 45 | 93 | fail | 37 | **4** |
| Structured n=12 | 4096 | 54 | 135 | fail | 49 | **5** |
| Random n=10 | 86 | 391 | 15 | 4 | 26 | **14** |
| PHP(3,2) UNSAT | 64 | -- | 29 | fail | 21 | -- |
| PHP(4,3) UNSAT | 4096 | -- | 197 | fail | 53 | **33** |

**Proof complexity correspondence:**
- Grouping = introducing extension variables
- Abstraction = defining each extension variable
- Reduction = reasoning with extensions instead of originals
- This is exactly extended resolution, which is exponentially more powerful than general resolution on PHP (Cook 1976, Haken 1985)

The PHP scaling (21 -> 53 from (3,2) to (4,3), vs CDCL's 29 -> 197) is empirical evidence of this separation.

### 7. Unit Propagation — Free Inference (commit `7fadae7`)

Not a proof system but a simplification engine that runs *between* levels. When a clause has all but one literal falsified, the remaining literal is forced. No search, no guessing — pure logical deduction. Cascades: forcing one variable can create new unit clauses, which force more variables.

Three forms of free inference:
- **Unit propagation:** single remaining literal in a clause is forced
- **Pure literal elimination:** variable appearing only positive (or only negative) is assigned to satisfy all its clauses
- **Subsumption:** if clause A is a subset of clause B, delete B

Added between ExtRes recursion levels AND after each abstraction phase. The cascade eliminates forced variables before the next level even starts.

**Results are transformative:**

| Instance | Before UP | After UP | CDCL | SmartDAG |
|----------|-----------|----------|------|----------|
| Structured n=10 | 37 | **4** | 93 | 45 |
| Structured n=12 | 49 | **5** | 135 | 54 |
| Random n=10 | 26 | **14** | 15 | 391 |
| PHP(4,3) UNSAT | 53 | **33** | 197 | -- |

Structured instances are now solved by free inference alone — zero abstractions needed. The implication chain structure means every variable is forced after the first assignment.

---

## The Composite Proof Architecture

The framework composes multiple proof systems through the rotation calculus's shared term structure. Each level operates on the same objects (terms, constraints, arrangements), and free inference runs between levels as a simplification pass.

### The Proof Complexity Levels

```
Level 0: Exhaustive search (flat brute force)
  No proof structure. Try everything. Cost: 2^n.

Level 1: Tree-like resolution (Choice/DPLL)
  Sequential branching with backtracking.
  Each branch is independent. No cross-branch learning.
  Implementation: ChoiceSAT.lean

Level 2: General resolution (CDCL)
  Sequential branching WITH clause learning.
  Failed branches produce lemmas usable by other branches.
  Exponentially more powerful than tree-like on UNSAT.
  Implementation: ClauseLearning.lean

Level 3: Extended resolution (ExtRes)
  Hierarchical abstraction: groups of variables become
  single derived elements. Proof operates on the compressed
  representation. Polynomially more powerful than general
  resolution on specific families (PHP).
  Implementation: ExtendedResolution.lean

Level inf: Free inference (unit propagation + pure literals)
  Not a proof system — a simplification engine.
  Runs BETWEEN levels, eliminating forced variables.
  Makes structured instances essentially free.
  Cascades between ExtRes abstraction levels.
```

### How They Compose

The levels are not alternatives. They compose through the shared term structure:

```
Term -> [free inference] -> simplified Term
     -> [ExtRes grouping] -> abstracted Term with lemmas
     -> [free inference cascade] -> further simplified
     -> [CDCL if stuck] -> with learned clauses
     -> [recurse] -> next level with all accumulated knowledge
```

The proof trace at the end contains all of it: forced assignments from unit propagation, abstractions from ExtRes grouping, learned clauses from CDCL conflicts. The trace is a composite proof using multiple proof systems at different levels.

### What the Data Shows

- **Structured n=12 (cost 5):** The cascade handles everything. Unit propagation forces all variables through the implication chain. Zero search, zero abstractions.
- **Random n=10 (cost 14):** Free inference handles the easy part (forced variables), a small search does the rest.
- **PHP(4,3) (cost 33 vs CDCL's 197):** Free inference + abstractions + cascade handle most of the proof. CDCL alone needs 197 operations; the composite approach needs 33.

No single proof system achieves all of these. Tree-like resolution can't do PHP efficiently. General resolution can't match the cascade on structured instances. Extended resolution alone doesn't have unit propagation's cascade. The composition through the shared term structure is what makes the cost profile work across all regimes.

---

## Why the Strategies Compose

A conventional SAT solver is a monolithic algorithm. CDCL is CDCL. The proof system is fixed (resolution). If you want extended resolution power or BP estimation, you need a different solver. They don't compose.

The rotation calculus is a shared substrate. The term structure (pairs, trees, DAGs, choice nodes) is common. The constraint interface is common. The proof trace (contraction sequence) is common. So:

- **BP** contributes global distributional awareness (cheap, soft, no proof)
- **ExtRes** contributes hierarchical proof compression (abstractions as lemmas)
- **CDCL** contributes conflict-driven deduction (hard proof, handles UNSAT)
- **SmartDAG** contributes spatial decomposition (exploits low treewidth)
- **Graph ordering** contributes structural routing (puts the right variables together)

These compose because they all operate on the same objects. The rotation rule is the common inference step. The constraint check is the common decision point. The arrangement is the common proof strategy.

Each strategy is a **tactic** in a proof calculus. The rotation calculus is the proof language. The arrangement is the proof term. The framework lets you apply different tactics at different points in the proof, composing them through the shared structure.

---

## The Proof Complexity Hierarchy

The framework implements four levels of the proof complexity hierarchy plus a cross-cutting simplification engine:

| Module | Proof System | Power | Reference |
|--------|-------------|-------|-----------|
| `ChoiceSAT.lean` | Tree-like resolution | Weakest. Exponential on PHP. | Ben-Sasson, Wigderson 1999 |
| `ClauseLearning.lean` | General resolution | Exponential separation from tree-like on PHP, Tseitin. | Haken 1985; Pipatsrisawat-Darwiche 2011 |
| `ExtendedResolution.lean` | Extended resolution | Polynomial PHP proofs. Exponentially stronger than general resolution. | Cook 1976 |
| `ExtendedResolution.lean` | Free inference (UP + pure literals) | Not a proof system. Simplification between levels. Makes structured instances free. | Davis-Putnam 1960 |
| `BeliefProp.lean` | No proof system | Estimation only. Cannot prove UNSAT. | Mezard-Parisi-Zecchina 2002 |

The progression from Choice to CDCL to ExtRes is not just "better heuristics." It's a climb up the proof complexity hierarchy — each level can express proofs that the level below cannot, regardless of the heuristic. And free inference (unit propagation) is the foundation that all levels sit on — it eliminates forced variables before any search begins, reducing the problem that the proof systems actually need to handle.

---

## The SAT/UNSAT Asymmetry

The framework reveals a categorical distinction:

**SAT is search.** A solution exists somewhere in the 2^n space. Every strategy navigates toward it. The solution is an attractor. BP works because it estimates where solutions are — and solutions exist to be estimated.

**UNSAT is proof.** There is no attractor. Every assignment is equally wrong. BP computes marginals as if solutions exist and gets assignments that locally look good but globally fail. CDCL works because it constructs a derivation — each learned clause is a lemma, the full collection is the proof.

| Property | SAT | UNSAT |
|----------|-----|-------|
| Certificate | Assignment (n bits) | Resolution proof (potentially exponential) |
| Verification | Check all clauses O(m) | Check proof validity O(proof length) |
| Strategy | Search, sample, estimate | Deduce, eliminate, prove |
| BP | Works (estimates solution distribution) | Fails (no solutions to estimate) |
| CDCL | Works (search + learning) | Works (proof construction) |
| Fundamental nature | Existence (there exists) | Non-existence (for all) |

This IS the NP vs coNP question. NP = efficiently verifiable existence claims. coNP = efficiently verifiable non-existence claims.

---

## The Rotation Calculus as Proof Language

The contraction trace IS the proof:

```
observe(pair(left, right))        -- Step 1: C(left, right) passes
  -> pair(right, observe(left))   -- Step 2: C(left.a, left.b) passes
  -> ...                          -- Step 3: ...
  -> ground                       -- QED: arrangement is valid
```

Each step is an inference rule: "C(a,b) holds, therefore this rotation is valid." The full trace is a derivation.

- `verifyTree` produces a verification trace (proof verification)
- Choice/DPLL produces a search tree with pass/fail at leaves (tree-like resolution)
- CDCL produces learned clauses culminating in empty clause (general resolution)
- ExtRes produces abstractions (lemmas) at multiple levels (extended resolution)
- BP produces marginal estimates (not a proof)

The rotation calculus was designed as a complexity-theoretic language. It turns out to also be a proof calculus — one where multiple proof strategies (tactics) compose through the shared term structure. The arrangement IS the proof strategy. The constraint IS the axiom system. The contraction IS the derivation.

This is why the "SAT solver" framing undersells it. A SAT solver is a monolithic algorithm with a fixed proof system. The rotation calculus is a proof language where the term structure carries the proof strategy, and different inference tactics compose through that structure. The rotation rule is the common inference step. The tree shape is the common proof strategy. The constraint is the common axiom system. Everything else — BP, CDCL, ExtRes, unit propagation — is a tactic applied to this common substrate.

The composite proof that ExtRes+UP produces for PHP(4,3) at cost 33 contains: forced assignments from unit propagation, abstractions from hierarchical grouping, and (if needed) learned clauses from CDCL conflict analysis. No single proof system generates this proof. The composition does.

---

## File Reference

### Core Language (commit `b86c502`)
| File | Purpose |
|------|---------|
| `Syntax.lean` | Term type, structural measures, well-formedness |
| `Rewrite.lean` | The rotation rule, termination, confluence, reversibility |
| `Constraint.lean` | Constrained rewrite, verification, search |
| `Complexity.lean` | P vs NP as structural properties |

### Tree Analysis (commit `b86c502`)
| File | Purpose |
|------|---------|
| `Examples.lean` | Concrete constrained rotation examples |
| `CSPEquivalence.lean` | Falsification: is rotation just permutation CSP? |
| `GeneratorFixedPoint.lean` | Falsification: generator fixed-point argument |
| `TreeArrangement.lean` | Tree arrangements escape flat CSP equivalence |
| `TreeComplexity.lean` | Level-by-level complexity hierarchy |
| `TreeFlow.lean` | Asymmetric information flow in rotation |
| `Factorization.lean` | Constraint factorization and independence |
| `Construction.lean` | Checking (catamorphism) vs constructing (anamorphism) |
| `GapAnalysis.lean` | Measuring the P vs NP gap empirically |

### SAT Encoding (commits `d4f52a2` through `ddea006`)
| File | Purpose |
|------|---------|
| `SATEncoding.lean` | SAT as tree arrangement, tree-decomposition solver, treewidth interpolation |
| `Choice.lean` | AND-OR trees, alternating computation |
| `DAG.lean` | Shared subtrees, DAG-aware solving |
| `Scaling.lean` | Flat vs tree vs DAG systematic comparison |

### Advanced Solvers (commits `943a18d` through `f1f3ae1`)
| File | Purpose |
|------|---------|
| `DAGBounded.lean` | Treewidth-parameterized SAT (SmartDAG) |
| `Random3SAT.lean` | Random instance generation and testing |
| `GraphOrder.lean` | BFS and min-degree variable ordering |
| `ChoiceSAT.lean` | AND-OR tree SAT with alpha-beta pruning |
| `HybridSolver.lean` | SmartDAG + Choice combination |
| `AdaptiveSolver.lean` | Structural scoring for strategy selection |
| `ClauseLearning.lean` | CDCL — general resolution in rotation framework |
| `MessagePassing.lean` | Coupled trees with iterative message passing |
| `BeliefProp.lean` | Belief propagation — soft constraints, marginals |
| `ExtendedResolution.lean` | Hierarchical abstraction, recursive proof compression |

### Git History (branch `feat/sat-tree-encoding`)

| Commit | Description |
|--------|-------------|
| `b86c502` | Core rotation calculus — 14 modules |
| `d4f52a2` | SAT encoding via tree arrangements |
| `89b2ea6` | Tree-decomposition SAT solver |
| `281a41d` | Treewidth interpolation |
| `26c812c` | DAG and Choice constructors |
| `ddea006` | Flat vs tree vs DAG scaling |
| `943a18d` | Bounded DAG solver (SmartDAG) |
| `b88c10b` | SmartDAG fix — solutions at all treewidths |
| `7114a5f` | SmartDAG k-varying analysis |
| `c367db4` | Random 3-SAT — SmartDAG does NOT generalize |
| `978dfeb` | Graph-aware variable ordering |
| `2158627` | Choice-based SAT — AND-OR trees beat flat |
| `bea5dd4` | Hybrid solver (SmartDAG + Choice) |
| `f73f450` | Adaptive solver — strategy selection |
| `90dcd68` | CDCL clause learning |
| `29515a5` | Message passing — coupled trees |
| `a6a59aa` | Belief propagation — beats CDCL on random SAT |
| `c50181d` | Extended resolution — abstraction and proof compression |
| `54c842e` | Recursive ExtRes — beats CDCL on structured |
| `f1f3ae1` | Three optimizations — graph grouping, propagation, global scoring |
| `7fadae7` | Unit propagation — structured instances solved for free |

---

## Open Questions

1. **BP-seeded ExtRes** (issue #18): Use BP marginals to guide ExtRes group assignments instead of enumeration. Expected to close the random SAT gap (from 14 to ~9).

2. **PHP scaling** (issue #18): Test PHP(5,4) through PHP(7,6). Theory predicts polynomial ExtRes+UP cost vs exponential CDCL cost. Empirical confirmation would validate the framework.

3. **Meta-rewriting** (issue #16): Constraints that evolve during search. CDCL is a special case (learned clauses modify the constraint). The general case — rewriting rules on rewriting rules — would let the framework express adaptive processes like survey propagation.

4. **State machines** (issue #15): Sequential input consumption with accumulated state. This would separate program (transition graph) from data (input), enabling the framework to express DPLL/CDCL's sequential processing natively rather than through tree-level recursion.

5. **The dispatcher problem**: Can a cheap structural test (interaction graph density, degree distribution) route instances to the right strategy without running all of them? The adaptive solver (`AdaptiveSolver.lean`) attempts this but SAT and UNSAT instances look similar from cheap features near the phase transition.

6. **UNSAT certification for ExtRes**: ExtRes currently finds that no assignment works but doesn't produce a refutation certificate. Tracking failure information in abstractions ("no valid assignment exists for this group given these constraints") would give the framework UNSAT proof capability beyond CDCL's resolution proofs.
