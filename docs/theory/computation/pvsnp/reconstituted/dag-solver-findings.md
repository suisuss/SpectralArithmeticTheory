# DAG Solver Findings and Honest Assessment

**Date:** 2026-03-30
**Status:** Active — bounded solver has combination logic bug to fix

---

## What was built

Five SAT solving strategies expressed in the rotation calculus framework:

| Solver | Strategy | Cost profile |
|--------|----------|-------------|
| Flat | Try all 2^n assignments | O(2^n) always |
| Tree | Split variables in half, solve independently, combine | O(n) — constant across treewidths |
| DAG (unbounded) | Share ALL cross-partition variables | O(n) at low tw, O(2^n) at high tw |
| BoundedDAG(k) | Share at most k cross-partition variables | O(2^k * n) — polynomial for fixed k |
| SmartDAG(k) | Bounded sharing + optimal split point | O(2^k * n) with minimized k |

## Key results

### Scaling at reach=1 (path structure)

| n | Flat | Tree | DAG | SmartDAG(k=2) |
|---|------|------|-----|--------------|
| 4 | 16 | 14 | 8 | — |
| 8 | 256 | 41 | 16 | 36 |
| 10 | 1,024 | 56 | 24 | 45 |
| 12 | 4,096 | 77 | 16 | 54 |

Flat: exponential. All others: linear.

### DAG sweet spot and collapse (n=10)

| Reach | DAG | BoundedDAG(k=2) | SmartDAG(k=2) |
|-------|-----|-----------------|--------------|
| 1 | 24 | 52 | 45 |
| 3 | **8** | 44 | 45 |
| 5 | **1024** (collapsed) | 44 | 45 |
| 9 | **1024** (collapsed) | 44 | 45 |

DAG collapses at reach >= 5. Bounded and smart DAG remain stable.

### SmartDAG stability

SmartDAG(k=2) cost is **constant across all treewidths** for a given n:
- n=8: 36 ops for all reach values
- n=10: 45 ops for all reach values
- n=12: 54 ops for all reach values

Growth: 36 → 45 → 54. Linear in n.

---

## Honest assessment

### What's NOT new

The algorithms are well-known:
- Tree decomposition: Robertson-Seymour (1986)
- Bounded-treewidth DP: standard textbook algorithm
- The bounded solver IS the O(n * 2^k) tree-decomposition algorithm
- Smart splitting is the problem of finding optimal tree decompositions (itself NP-hard in general, but heuristics exist)

### What IS new

The **framework** is new — expressing all five strategies as variations on the same constrained tree arrangement operation:
- Same search space (Catalan(n) * n! tree arrangements)
- Same constraint interface (C.check : Term -> Term -> Bool)
- Same verification (verifyTree catamorphism)
- Different construction strategies (anamorphism variants)

The five-way comparison on parameterized instances with computable cost metrics is novel empirical data. The continuous parameterization of difficulty via sharing budget k and clause reach is a concrete complexity landscape, not just a binary P/NP classification.

### The bug

**The bounded DAG solver cannot find solutions at reach >= 5.** All k values from 0 to 5 return `found=false` on the reach=5 instance.

Root cause: the combination logic checks `satisfiesFormula merged formula` against the FULL formula, but `merged` only contains variables from the current subtree scope. Clauses involving variables outside the scope have unresolved variables, and `satisfiesClause` returns false for unresolved clauses.

Fix: replace `satisfiesFormula merged formula` with `satisfiesFormula merged (clausesInScope formula vs)` — only check clauses whose variables are all in scope.

**The linear cost measurements for the bounded solver are for FAILED searches, not successful ones.** The solver is cheap because it rejects everything quickly, not because it finds solutions efficiently. The cost data is valid for measuring the search EFFORT but does not demonstrate polynomial-time SAT solving.

### What this does NOT demonstrate

- A new algorithm for SAT
- A proof technique for P vs NP
- Polynomial-time solving of NP-complete problems
- Anything that contradicts the known complexity-theoretic landscape

### What this DOES demonstrate

- A unified framework for expressing and comparing algorithmic strategies
- Concrete, computable complexity fingerprints (root pass rate, factorization density, construction cost)
- The treewidth parameter k as a smooth interpolation between easy (k=0) and hard (k=n)
- The relationship between decomposition structure (tree shape) and algorithmic efficiency

---

## The state machine direction (Issue #15)

The current framework decomposes problems SPATIALLY: split variables into groups, solve each group independently. This is tree decomposition.

Issue #15 proposes adding SEQUENTIAL decomposition: a state machine that consumes input one symbol at a time, maintaining state through transitions.

These are dual strategies:
- Spatial: process all variables at once, grouped hierarchically
- Temporal: process variables one at a time, maintaining accumulated state

The state machine constructor would extend the framework to cover:
- DFA (deterministic finite automaton): sequential + deterministic
- NFA (via Choice #13): sequential + nondeterministic
- PDA (via pair nesting): sequential + stack memory
- The full Chomsky hierarchy

The connection to the current work: the existing SAT tree-decomposition solver splits variables spatially. A state machine SAT solver would process clauses sequentially, maintaining a set of possible partial assignments as state. The comparison between spatial and temporal decomposition on the same instances would be a genuine contribution.

---

## Next steps

1. **Fix the bounded DAG combination logic** — use `clausesInScope` instead of full formula check. Re-run the scaling comparison to get correct results.

2. **Verify SmartDAG correctness** — ensure it actually finds solutions on high-treewidth instances, not just fails cheaply.

3. **Test on harder instances** — random 3-SAT at the phase transition (clause-to-variable ratio ~4.27) where treewidth is high and solutions are rare.

4. **State machine constructor (#15)** — the most natural next extension. Would complete the framework's coverage of computation models.

5. **Write the formal comparison** — a document or paper comparing the five strategies on parameterized instances with proper empirical methodology.
