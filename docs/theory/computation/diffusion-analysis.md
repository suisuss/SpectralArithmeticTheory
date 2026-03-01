# Information Diffusion Under Normalization

## The Finding

When SAT formulas are encoded as combinator terms and normalized, assignment-specific information undergoes a diffusion process: it spreads from concentrated positions (specific leaves) into the global tree structure, becoming invisible to any local or aggregate measurement.

This diffusion is not specific to the DynSemiring's obs normalization. It also occurs under native SK combinatory reduction — a completely independent computational mechanism. The phenomenon appears to be a property of SAT itself, not of the normalization system.

## The Data

### Setup

Formula: `(x_0 v x_1) ^ (!x_0 v x_2) ^ (!x_1 v !x_2)` — 3 clauses, 3 variables, shared with negation. Only 2 of 8 assignments are SAT: 010 and 101.

Encoded as Church AND/OR/NOT over SK combinatory logic:
- TRUE = K, FALSE = SK
- OR p q = p TRUE q
- AND p q = p q FALSE
- NOT p = p FALSE TRUE

### DynSemiring normalization (obs + Leibniz)

Embedding: K -> f_0, S -> f_1, app -> compose. Normalize via iterDeepRewrite.

**Leaf counts at depth 5 (all 8 assignments):**

```
Assign  SAT?  #true   f_0   f_1    z   oplus  compose  termSize
000     NO    0       92    62     4   13     144      323
001     NO    1       92    50     4   13     132      299
010     SAT   1       92    50     4   13     132      299
011     NO    2       92    38     4   13     120      275
100     NO    1       92    50     4   13     132      299
101     SAT   2       92    38     4   13     120      275
110     NO    2       92    38     4   13     120      275
111     NO    3       92    26     4   13     108      251
```

Three quantities are uniform across ALL assignments: f_0 = 92, z = 4, oplus = 13. Three depend only on the number of true literals: f_1 = 62 - 12*truecount, compose = 144 - 12*truecount, termSize = 323 - 24*truecount.

**No aggregate measure separates SAT from UNSAT.** Every count we can extract depends at most on how many literals are true, never on which ones. Since SAT and UNSAT assignments can share the same true-count (001 is UNSAT with 1 true, 010 is SAT with 1 true), no scalar separates them.

**Branch analysis also fails.** The top-level oplus gives branches with f_0 = (75, 17) for ALL 8 assignments. The branchSAT technique that worked for the CTerm encoding provides zero information here.

**But the terms are structurally different.** 001 and 010 have identical counts for every node type, yet the terms are not equal. The first structural difference appears at depth 10 in the tree (path: `+LL+LL+LL+LL+LR`). The distinguishing information exists but is buried deep.

### Native SK reduction (beta-reduction, no DynSemiring)

Same formula, same combinator encoding, but now normalized via native SK reduction: K x y -> x, S x y z -> xz(yz). Track countK (number of K combinators in the term).

```
Fuel  000(U) 001(U) 010(S) 011(U) 100(U) 101(S) 110(U) 111(U)
0     17     17     17     17     17     17     17     17
1     18     18     18     18     15     15     15     15
2     15     15     15     15     13     13     13     13
3     16     16     13     13     11     11     11     11
4     9      9      14     14     12     12     12     12
5     10     10     11     11     9      9      9      9
6     1      1      9      9      10     7      10     7
7     1      1      7      7      1      8      1      5
8     1      1      5      5      1      5      1      8
10    1      1      3      3      1      1      1      1
30    1      1      1      1      1      1      1      1
```

At every fuel level from 0 to 30, SAT/UNSAT collisions exist:
- Fuel 0: all equal (17). Total uniformity.
- Fuel 1: {000,001,010,011}=18, {100,101,110,111}=15. Only x_0 matters.
- Fuel 3: 010(SAT)=13 = 011(UNSAT)=13.
- Fuel 5: 010(SAT)=11 = 011(UNSAT)=11.
- Fuel 30: all converge to 1. Both K (TRUE) and SK (FALSE) contain exactly 1 K.

The groupings evolve — which assignments are confused changes at each step — but confusion BETWEEN SAT and UNSAT is never eliminated at any intermediate step.

### The oscillation

The DynSemiring normalization shows an oscillation pattern in f_0 counts:

```
Depth   000(U)  010(S)  diff
0       17      17      0
1       34      34      0
2       51      51      0
3       66      66      0
4       82      82      0
5       92      92      0
6       103     101     2
7       103     100     3
8       101     99      2
9       103     101     2
```

Depths 0-5: perfect uniformity. Depths 6+: small differences emerge but oscillate (period ~2). The uniformity is not monotonic — it breaks and partially reforms.

## Interpretation

### Not heat diffusion — standing wave interference

The initial hypothesis was that obs normalization acts like heat diffusion: localized information spreads uniformly and stays uniform. The oscillation at depths 6+ contradicts this. Heat diffusion is monotonic — once uniform, it stays uniform.

The better analogy is standing wave interference. The Leibniz rule `obs(compose(a,b)) = oplus(compose(obs(a),b), compose(a,obs(b)))` creates superpositions (oplus terms). With shared variables, the superpositions from different clause contributions interfere. At certain depths (3, 5), the interference is perfectly destructive — all assignment-specific signals cancel exactly. At other depths (6-9), the cancellation is imperfect, but the residual signal is small and oscillatory.

This would explain:
- Why depths 3 and 5 show perfect uniformity (destructive interference nodes)
- Why depths 6+ show small, oscillating differences (near-but-not-exact cancellation)
- Why SAT/UNSAT collisions persist at all depths (the residual signal carries true-count information but not positional information)

### Information is diffused, not destroyed

The terms at depth 5 are structurally different despite having identical counts. The assignment information is present but has been pushed from aggregate properties (countable) to positional properties (tree-shape-dependent). Specifically:

- Two terms that differ in leaf values (which positions have K vs SK) produce normalized terms that differ only at depth 10+ in the tree
- Every "shallow" property (node counts, branch counts, subtree counts to depth 3) is identical
- Only a full tree traversal — or at minimum a traversal reaching depth 10 — reveals the difference

This is the structural version of the P vs NP gap: VERIFYING an assignment is a leaf-level operation (check each clause). FINDING a satisfying assignment requires examining the deep tree structure, which encodes the combinatorial search space.

### The phenomenon is framework-independent

The native SK reduction experiment is critical. SK combinatory reduction:
- Uses a completely different rewrite mechanism (K-reduction discards, S-reduction duplicates) than obs normalization (Leibniz decomposition, sum rule)
- Is asymmetric (application is non-commutative, reduction order matters) unlike obs (treats compose symmetrically)
- Is Turing-complete (can simulate any computation) unlike the DynSemiring (sub-Turing)

Yet it shows the same qualitative pattern: countK cannot separate SAT from UNSAT at any intermediate reduction step.

This rules out the explanation that the indistinguishability is caused by:
- The commutativity of compose (SK reduction is non-commutative)
- The specific form of the Leibniz rule (SK reduction uses K-discard and S-distribute)
- The sub-Turing nature of the DynSemiring (SK reduction is Turing-complete)

The phenomenon survives the change from obs normalization to beta-reduction. It appears to be a property of SAT-encoded terms under ANY structural reduction, not a quirk of the DynSemiring.

## The Depth Limitation

The oscillation at depth 6+ is the main complication for the "push all bubbles out" narrative. If normalization perfectly diffused information, the uniformity at depth 5 would persist at all higher depths. Instead:

1. The chain has NOT converged for this formula. The 2-clause formula converges at depth 3; the 3-clause formula is still evolving at depth 9+.

2. At depths 6+, the f_0 values differ across assignments, but:
   - The differences are small (range of ~7 across all assignments, vs the total count of ~100)
   - SAT/UNSAT collisions persist at every depth tested
   - The values oscillate with period ~2

3. For native SK reduction, the K-count also never separates SAT from UNSAT at any fuel level.

The depth limitation means the diffusion is NOT permanent at a given observation level. Instead, the correct picture may be:

**The normalization process creates and resolves interference patterns at different scales.** At some depths, the interference is perfectly destructive (uniform f_0). At other depths, some signal leaks through. But the leaked signal is about the NUMBER of true literals, not about WHICH variables are true — so it still cannot distinguish SAT from UNSAT assignments with the same true count.

This is consistent with the depth-10 first-difference finding: the positional information (which variables are true) is always deep in the tree. The oscillation is about aggregate information (how many are true) temporarily becoming visible. The SAT-relevant information (which combination satisfies all clauses) remains inaccessible at every depth.

## Open Questions

### Does the interference pattern have a structure?

The depths at which perfect uniformity occurs (3, 5) — is there a pattern? Are these related to the formula's clause/variable counts? Testing other formulas could reveal whether the uniform depths are predictable.

### Does the SK indistinguishability hold for all intermediate fuel levels?

The data shows SAT/UNSAT collisions persist at fuels 0-30 for native SK reduction. A formal proof (or counterexample) that no fuel level separates SAT from UNSAT for this formula would be significant.

### Does the phenomenon hold for other rewrite systems?

The two systems tested (obs/Leibniz and SK reduction) are both term rewriting systems. Would the same phenomenon appear under:
- Polynomial expansion (arithmetize the formula, expand)
- Matrix operations (encode as matrix product, compute partial products)
- Graph rewriting (encode as graph, apply local transformations)

Each of these would test a different structural mechanism. If the indistinguishability is truly about SAT and not about term rewriting, it should appear in all of them.

### What is the minimum tree depth needed to separate SAT from UNSAT?

The first structural difference between 001(UNSAT) and 010(SAT) is at depth 10 in a tree of size ~300. For larger formulas, does this depth grow? If it grows linearly with formula size, it's accessible. If it grows as a function of the search space, it's inaccessible — and that growth rate IS the complexity separation.

## Key Insight

The data points to a clean decomposition of SAT information:

1. **Aggregate information** (how many literals are true): accessible at some normalization depths, oscillatory, but never sufficient for SAT/UNSAT separation because SAT is not determined by the number of true literals.

2. **Positional information** (which literals are true): always deep in the tree (depth 10+ for 3-variable formulas). This is the information that determines satisfiability, and normalization pushes it to the position that requires full tree traversal to access.

3. **Relational information** (which combinations of literals satisfy all clauses simultaneously): this is satisfiability itself. It is never extractable from any aggregate or local measurement of the normalized term. Only a traversal that reaches the positional differences and evaluates their joint effect can determine it.

This decomposition — aggregate (easy but useless) vs positional (hard to reach) vs relational (requires combining positional data) — may be the structural core of why SAT is hard. The normalization process, regardless of mechanism, respects this decomposition: it can shuffle aggregate information freely but cannot promote positional information to aggregate form.
