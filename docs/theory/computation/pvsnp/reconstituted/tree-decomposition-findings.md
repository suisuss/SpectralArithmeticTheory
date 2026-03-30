# Tree Decomposition Findings

**Date:** 2026-03-27 to 2026-03-30
**Status:** Active research — SAT encoding working, treewidth interpolation measured

---

## Summary

The rotation calculus, extended from flat lists to tree arrangements, provides a unified framework where:

- **The tree shape is the algorithm.** A decomposition strategy for a problem IS a tree arrangement. Finding a good tree = designing a good algorithm.
- **The leaf placement is the solution.** Which elements go where in the tree IS the assignment / permutation / partition.
- **The constraint gates each level.** The same constraint fires at every internal node, checking local compatibility.
- **Factorization is the complexity measure.** Whether subtrees can be solved independently determines whether the problem is easy or hard.

---

## What was built

### Falsification (directions killed)

| File | Finding |
|------|---------|
| `CSPEquivalence.lean` | Flat-list rotation = permutation CSP. All rotation properties (termination, confluence, conservation, reversibility) are trivially available in any sequential checker. |
| `GeneratorFixedPoint.lean` | Direction 3 (generator fixed-point argument) = P != NP restated. `compression_scheme_iff_solver` proves the equivalence in one line each direction. |

### Discovery (tree arrangements)

| File | Finding |
|------|---------|
| `TreeArrangement.lean` | Tree arrangements escape CSP equivalence. The balanced partition constraint is vacuous on flat lists but substantive on trees. |
| `TreeComplexity.lean` | Level-by-level analysis is mostly D&C restated, but the rotation traversal creates asymmetric information flow. |
| `TreeFlow.lean` | Context-aware verification produces 18 disagreements with symmetric verification on 4 elements. Traversal order is computationally significant. |
| `Factorization.lean` | Subtree independence formalized. Root pass rate: sorted = 100% (factorable), balanced = 0% at equal split (non-factorable). |
| `Construction.lean` | Brute force vs factorized vs heuristic construction. Scaling: 36 → 17,725 → 10,218,781 (brute) vs 3 → 5 → 7 (heuristic). |
| `GapAnalysis.lean` | Density does NOT determine findability. Sorted: 4.2% density, trivially findable. Balanced: 87% density, NP-hard. |

### SAT encoding

| File | Finding |
|------|---------|
| `SATEncoding.lean` | SAT encoded as tree arrangements. Tree-decomposition solver vs flat brute force. Exponential speedup on treewidth-0 instances (1024 vs 29 for 10 vars). Treewidth interpolation shows tree decomp wins when constraints are TIGHT. |

---

## Key results

### 1. Checking vs constructing

Checking (verification) is a **catamorphism** — fold the tree, check each node, O(n).

Constructing (search) is either:
- An **anamorphism** (when the constraint factorizes) — unfold top-down with local splits, polynomial
- A **search** (when it doesn't factorize) — enumerate arrangement space, exponential

P = checkable AND factorizable (catamorphism has a polynomial anamorphism).
NP = checkable (catamorphism exists but no polynomial anamorphism known).

### 2. The factorization speedup is real

On SAT instances with treewidth 0 (independent clauses):

| Variables | Flat brute force | Tree decomposition | Speedup |
|-----------|-----------------|-------------------|---------|
| 6 | 64 | 17 | 3.8x |
| 8 | 256 | 23 | 11x |
| 10 | 1,024 | 29 | 35x |

Flat brute force: 2^n (exponential). Tree decomposition: ~3n (linear).

### 3. Tree decomposition helps HARD instances, not easy ones

Treewidth interpolation with restrictive XOR-like cross-links (10 variables):

| Cross-links | Flat brute | Tree decomp | Winner |
|-------------|-----------|-------------|--------|
| 0 (loose) | 1 | 1,140 | Flat (1140x) |
| 4 (medium) | 321 | 148 | Tree (2x) |
| 9 (tight) | 342 | 56 | Tree (6x) |

Counterintuitive: more constraints = tree decomposition gets CHEAPER, not more expensive. Tight constraints prune the partial solution space at each subtree level, reducing combination work. Loose constraints give tree decomposition nothing to prune.

### 4. Density does not determine findability

| Constraint | Density (n=4) | Findability |
|------------|---------------|-------------|
| Sorted | 4.2% (5/120) | Trivial (sort+split, O(n log n)) |
| Balanced partition | 87% (104/120) | NP-hard |

The gap between density and findability IS the P vs NP gap. It lives in the STRUCTURE of solutions, not their count.

### 5. The root pass rate is the fingerprint

The root pass rate measures how cooperative the constraint is with tree decomposition:

| Constraint | Root pass rate (equal split) | Meaning |
|------------|------------------------------|---------|
| Sorted | 100% at all splits | Fully cooperative — any split preserves sortedness |
| Balanced | 0% for sequential elements | Fully uncooperative — finding equal-sum splits IS the hard problem |

### 6. The asymmetric information flow is genuine

The rotation rule's left-first descent creates context-sensitive verification that differs from symmetric (independent subtree) verification:

- 18 disagreements on 4 elements with budget constraint
- 16 cases where context makes constraints stricter
- 2 cases where context makes constraints more lenient
- No analog in standard tree-CSP or treewidth theory

---

## Trees are fundamental to complexity

A flat list has one structural dimension: **order** (permutations, S_n).
A tree has two: **shape** (Catalan space) and **placement** (S_n within the shape).

These dimensions interact. The tree shape determines WHICH pairs of elements the constraint compares. Different shapes create different constraint-check patterns. The shape is a strategy for decomposing the problem.

For flat lists, the constraint fires on a fixed adjacency pattern (always a path graph). For trees, the constraint fires on pairs determined by the shape — the "constraint graph" is part of the search space, not given in advance.

This makes the rotation calculus on trees closer to algorithm design than constraint satisfaction: choosing a tree shape IS choosing a divide-and-conquer strategy. P problems have polynomial strategies (the heuristic column in the scaling table is never blank). NP-hard problems don't.

The verification structure matches the problem structure: the catamorphism descends the tree, checking each level independently. If the problem decomposes hierarchically, the tree captures it natively. Flat lists force hierarchical problems into sequential encodings that destroy factorizability.

---

## Limitations and honest assessment

1. **The tree framework is tree decomposition in rotation calculus clothing.** The SAT solver IS the standard tree-decomposition DP algorithm. The framework provides a new ENCODING, not a new algorithm.

2. **The framework cannot prove P != NP.** It can MEASURE the factorizability gap (root pass rate, construction cost ratio, speedup interpolation) but proving the gap exists asymptotically would require proving P != NP.

3. **The treewidth interpolation was inverted.** The prediction was: more cross-links → harder for tree decomp. The reality: more cross-links → easier for tree decomp (tighter pruning). This shows the framework's measures can surprise — the relationship between constraint structure and factorizability is non-trivial.

4. **The split strategy is naive.** The current implementation always splits variables at the midpoint. An optimal split (minimizing cross-partition clauses) would match the problem's actual tree decomposition. Finding the optimal split is itself computationally interesting.

---

## Next directions

### Immediate (issues #7 and #13)

**DAG arrangements (#7, #14 Ref constructor):** Trees enforce independent subtrees. DAGs allow shared sub-computations (memoization). This is the gap between divide-and-conquer and dynamic programming. A Ref constructor would let arrangements reuse structure, potentially turning exponential tree-search into polynomial DAG-search for problems with overlapping subproblems.

**Choice constructor (#13):** `pair` is AND (both children present). `choice` is OR (one branch selected). Together they give AND-OR trees — the structure underlying alternating computation and the polynomial hierarchy. The depth of choice nesting characterizes Sigma_k / Pi_k levels.

### Structural alternatives (#6, #8, #9, #10, #11, #12)

- k-ary trees (Fuss-Catalan space)
- Unordered trees (does left/right asymmetry help or hurt?)
- Forests (independent parallel decompositions)
- Triple constructor (ternary splits)
- Sequence constructor (variable-arity nodes)
- Graph constructor (named references)

### Analysis

- Optimal split strategy (minimize cross-partition clauses)
- Phase transition in SAT treewidth interpolation
- Connection to circuit complexity (DAGs = circuits, trees = formulas)
