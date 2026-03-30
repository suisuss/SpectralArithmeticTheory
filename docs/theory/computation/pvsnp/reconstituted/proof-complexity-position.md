# Position in the Proof Complexity Landscape

**Date:** 2026-03-30
**Status:** Assessment after systematic investigation

---

## Where the rotation calculus sits

The framework implements the first two rows of the proof complexity hierarchy:

| Algorithm | Proof System | Our implementation | Status |
|-----------|-------------|-------------------|--------|
| DPLL | Tree-like Resolution | Choice+mindeg | Working, measured |
| CDCL | General Resolution | Meta-rewriting (#16) | **Next step** |
| LP relaxation | Sherali-Adams | — | Not expressible currently |
| SDP relaxation | Sum-of-Squares/Lasserre | — | Not expressible currently |
| Groebner bases | Polynomial Calculus | — | Not expressible currently |

Additionally, SmartDAG implements bounded-treewidth tree decomposition, which is a spatial organization strategy within tree-like resolution.

## What was demonstrated

### Strategies implemented and tested

| Strategy | Mechanism | Best regime | Measured cost |
|----------|-----------|-------------|---------------|
| Flat brute force | Enumerate all 2^n | Lucky instances | 1-16384 |
| SmartDAG(k=2) | Spatial decomposition | Structured/low tw | 36-63 (linear in n) |
| Choice+mindeg | DPLL backtracking | Random 3-SAT | 37-120 (best on random) |
| DAG (unbounded) | Share all cross-vars | Low tw sweet spot | 8-1024 (collapses) |
| BoundedDAG(k) | Share ≤ k cross-vars | All treewidths | 44-72 (stable) |
| Split-then-search | One split + Choice | Neither regime | 558 (interference) |
| Hybrid (recursive) | SmartDAG + Choice at every level | Neither | 515-2051 (worst of both) |

### Key findings

1. **SmartDAG scales linearly on structured instances:** 36 → 45 → 54 → 63 for n=8,10,12,14 at reach=3. This is the bounded-treewidth algorithm working as theory predicts. 260x speedup over flat at n=14.

2. **Choice+mindeg beats flat on random 3-SAT:** 37 vs 86 at n=10 seed=42. 52 vs 274 at n=12. First tree-based strategy to beat flat on random instances in our framework. This is DPLL with min-degree ordering.

3. **Spatial and temporal strategies interfere, don't combine:** The hybrid (SmartDAG at every level + Choice in subproblems) gets the worst of both worlds. Spatial decomposition breaks temporal pruning's ability to short-circuit globally.

4. **Variable ordering matters enormously for Choice:** Default order: 177. BFS order: 967. Min-degree: 37. Same algorithm, same instance, 26x range in cost.

5. **Graph-aware ordering helps SmartDAG marginally:** BFS and min-degree improve SmartDAG by 5-25% on random instances but don't close the gap with flat brute force.

6. **The LCG "random" instances are actually structured:** Variables {1,3,5,7} form a clique, {0,2,4,6} are isolated. Graph density is only 22%. A better PRNG would give harder instances.

## What the framework cannot do

### Clause learning (General Resolution / CDCL)

When DPLL (our Choice evaluator) fails on a branch, it learns nothing. It backtracks and tries the next branch independently. CDCL analyzes the failure, derives a learned clause that prevents the same conflict pattern in other branches, and adds it to the formula.

This is an exponential improvement on structured unsatisfiable instances (pigeonhole, Tseitin formulas). Ben-Sasson & Wigderson (2001) showed that short proofs require narrow clauses — learned clauses provide this narrowness.

In our framework, clause learning would mean the constraint CHANGES during search. Currently the constraint is static: `C.check : Term → Term → Bool` is fixed. Meta-rewriting (#16) would allow the evaluator to modify C based on encountered failures. This is the step from tree-like to general resolution.

### Message passing (Statistical Physics)

Survey propagation treats the solution space as a distribution, passing probabilistic messages between variables on a factor graph. It accounts for the cluster structure of the solution landscape — not just "does a solution exist?" but "what does the typical solution look like?"

Our framework operates on individual terms. It has no notion of distribution, cluster, or message. Reaching the statistical physics regime would require treating arrangements probabilistically — asking "what fraction of arrangements near this one are valid?" rather than "is this specific arrangement valid?"

The root pass rate (from Factorization.lean) is a crude density measure. Real message passing needs the factor graph structure and cavity equations.

### The Overlap Gap Property wall

Gamarnik (2017+): any "stable" algorithm (where small input perturbations cause small output changes) fails when OGP is present in the solution landscape. DPLL, local search, tree decomposition, and our entire framework are stable.

OGP predicts our failure on hard random instances — which is exactly what we observed. This is not a failure of the implementation but a fundamental barrier for this class of algorithms.

## The path forward

### Immediate: Meta-rewriting / Clause Learning (#16)

Move from tree-like to general resolution. When the Choice evaluator hits a failed branch:
1. Analyze the conflict (which variable assignments caused the failure)
2. Derive a learned clause (a new constraint that prevents this pattern)
3. Add it to the formula for remaining branches

This would:
- Match CDCL's power (general resolution)
- Give exponential improvement on structured UNSAT instances
- Still fail on hard random instances (general resolution has exponential lower bounds for random 3-SAT near threshold)

Implementation: extend the Choice evaluator to return failure reasons (the conflicting partial assignment), derive learned clauses, and thread an evolving constraint through the search.

### Medium-term: Distributional reasoning

Instead of evaluating individual arrangements, compute statistics over the arrangement space:
- What fraction of arrangements pass at each tree level?
- How are valid arrangements clustered?
- Can we propagate these statistics through the tree?

This would connect to belief propagation (BP) on factor graphs — the replica-symmetric version of survey propagation. BP works below the clustering transition and could extend the framework's reach to the easy-random regime more efficiently.

### Long-term: The clustering boundary

The hard regime (between clustering and threshold) is where all known polynomial-time algorithms fail. Reaching this regime would require either:
- A fundamentally new algorithmic idea (beyond stable algorithms)
- A proof that no polynomial algorithm exists (P ≠ NP)
- Understanding the OGP barrier well enough to design algorithms that circumvent it

The rotation calculus framework doesn't provide tools for this regime. But it provides a clean, measurable setting in which to study the boundary between tractable and intractable — which is itself valuable for understanding what makes problems hard.

## Connection to the original research program

The rotation calculus began as a "formal language for complexity" (conception.md). After systematic investigation:

- **Direction 3 (generator fixed-point): killed.** P ≠ NP restated.
- **Direction 4 (new formal language): partially realized.** The tree/DAG/Choice framework is a clean complexity language, but it implements known algorithms rather than transcending them.
- **Direction 5 (Leibniz ↔ NP-verification): unexplored.** The Leibniz rule's branching (doubling term size) corresponds to resolution's branching (exploring both values of a variable). The connection is structural but hasn't been formalized.

The framework's genuine contribution is OPERATIONAL: expressing multiple algorithmic strategies in a single language with comparable cost metrics. This is a practical tool for studying the proof complexity landscape, not a theoretical breakthrough.
