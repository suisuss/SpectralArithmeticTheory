# Framework Independence Analysis

## Goal

Test whether the SAT indistinguishability phenomenon — no scalar measure of intermediate terms separates SAT from UNSAT assignments — is specific to the DynSemiring, or a deeper property of SAT itself.

## Formula Under Test

All frameworks test the same 3-clause shared-variable CNF formula:

```
(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂)
```

SAT assignments: 010 and 101. Six UNSAT assignments.

## Frameworks Tested

### 1. DynSemiring obs normalization

**Type**: Algebraic, commutative, sub-Turing.

**Encoding**: K → f₀, S → f₁, app → compose. Booleans are Church-encoded: TRUE = K = f₀, FALSE = SK = compose(f₁, f₀).

**Reduction**: obs applies the Leibniz rule: obs(compose(a,b)) = oplus(compose(obs(a),b), compose(a,obs(b))). Iterated via iterDeepRewrite at increasing depth.

**Measurement**: countF₀ (number of f₀ leaves in the normalized term).

**Result**: At depth 5, countF₀ = 92 for ALL 8 assignments. Total indistinguishability. Every scalar measure (f₀, f₁, z, oplus, compose counts, term size) either is uniform across all assignments or depends only on the number of true literals — never on which variables are true, never on satisfiability.

**Key property**: Leibniz normalization CREATES structure. Each obs application duplicates the tree via oplus, expanding term size.

### 2. Native SK combinatory reduction

**Type**: Term rewriting, non-commutative, Turing-complete.

**Encoding**: Same Church booleans (TRUE = K, FALSE = SK). SAT formula built with combinatory AND/OR/NOT.

**Reduction**: Standard SK reduction rules: K x y → x, S x y z → xz(yz). Fuel-bounded multi-step reduction.

**Measurements**: countK (number of K combinators) and countS (number of S combinators).

**Result (countK)**: SAT/UNSAT collisions persist at EVERY fuel level tested (0 through 30). At convergence, both SAT (→ K) and UNSAT (→ SK) contain exactly 1 K. countK cannot separate.

**Result (countS)**: SEPARATION ACHIEVED at fuel 10. TRUE = K has countS = 0, FALSE = SK has countS = 1. At fuel 10, SAT assignments have countS ∈ {0, 2}, UNSAT all have countS = 1. At convergence, SAT → 0, UNSAT → 1.

**Critical implication**: The SK "indistinguishability" under countK was an artifact of choosing a measure where TRUE and FALSE happen to have the same value (both have 1 K). countS, where TRUE and FALSE differ (0 vs 1), separates. The SK result was measure-specific, not framework-deep.

**Key property**: S-reduction DUPLICATES subterms. S x y z → xz(yz) copies z, creating structural proliferation.

### 2b. BCKW combinatory reduction

**Type**: Term rewriting, non-commutative, Turing-complete (different basis).

**Encoding**: Same Church booleans but FALSE = K(WK) instead of SK. B x y z → x(yz), C x y z → xzy, K x y → x, W x y → xyy.

**Measurement**: countK.

**Result**: SEPARATION ACHIEVED at fuel 7+. TRUE = K has countK = 1, FALSE = K(WK) has countK = 2. Transient collisions at fuel 0-3 and fuel 5, but stable separation from fuel 7 onward. At convergence, SAT = 1, UNSAT = 2.

**Key property**: W duplicates (W x y → x y y) but doesn't distribute like S. Different reduction dynamics, but same Church encoding. The different FALSE encoding (K(WK) vs SK) creates asymmetric K-counts that enable separation.

### 3. Boolean Expr ADT with pattern matching

**Type**: Typed, semantics-aware, sub-Turing.

**Encoding**: Constructors T, F, not, and, or. Booleans are T and F directly. Formula built as nested expression tree.

**Reduction**: Two strategies tested:
- **Eager** (innermost-first): reduce deepest redexes first.
- **Lazy** (outermost-first): reduce topmost redex first, short-circuits.

Both use pattern matching: `and T F → F`, `or T _ → T`, `not T → F`, etc.

**Measurement**: countT (number of T constructors in the term).

**Result**: SEPARATION ACHIEVED.
- Eager: separates at fuel 2. SAT assignments both have countT = 3; no UNSAT assignment has countT = 3.
- Lazy: separates at fuel 3. SAT assignments both have countT = 2; no UNSAT assignment has countT = 2.

**Key property**: Pattern matching ELIMINATES structure. Terms shrink monotonically toward T or F. No structural proliferation.

## The Type Distinction

The ADT result initially appeared to refute the indistinguishability hypothesis. But the comparison is not fair.

The Expr ADT is fundamentally different from SK and DynSemiring in a way that explains the separation:

| Property | DynSemiring | SK Combinators | Expr ADT |
|----------|-------------|----------------|----------|
| Typed | No | No | Yes |
| Reduction knows about booleans | No | No | Yes |
| Truth tables in reduction rules | No | No | Yes |
| Structure during reduction | Grows (Leibniz) | Grows (S-dup) | Shrinks |

The pattern-matching rules `and T F → F`, `not T → F`, etc. ARE the boolean truth tables. The reduction mechanism literally encodes the semantics of the formula. The type constructors (T, F, and, or, not) carry meaning, and the reduction rules respect that meaning.

In SK combinators, K and S are generic rewriting rules. `K x y → x` doesn't "know" it's computing TRUE — it's a structural operation (discard second argument) that happens to implement boolean selection when used in a Church encoding. The boolean semantics emerges from the encoding, not from the reduction mechanism.

In DynSemiring, the Leibniz rule is a generic differential operator with no awareness of booleans.

The real distinction is **typed/semantic** vs **untyped/generic**:
- **Untyped/generic**: reduction rules are semantics-blind. They operate on structure without knowing what it represents. Both DynSemiring and SK are in this category. Both show indistinguishability.
- **Typed/semantic**: reduction rules encode domain semantics. Pattern matching on T/F/and/or/not directly implements boolean evaluation. The Expr ADT is in this category. It separates easily.

Of course a system that has the answer baked into its reduction rules can extract the answer quickly. The interesting question is what happens when the reduction mechanism doesn't know what the terms mean.

### 4. Untyped S-expression rewriting (stripped ADT)

**Type**: Untyped, semantics-aware (rules encode truth tables), sub-Turing.

**Encoding**: Tagged binary tree nodes. Tag 0 = "true", tag 1 = "false", tag 2 = "not", tag 3 = "and", tag 4 = "or". No type distinctions — all terms are `UTerm`.

**Reduction**: Same two strategies (eager and lazy). Rewrite rules match on tag values: `node 3 (leaf 1) _ → leaf 1` (and false _ → false), etc. Structurally identical rules to the typed Expr version, but without type information.

**Measurement**: countTag0 (count of leaves with tag 0).

**Result**: SEPARATION ACHIEVED, same as typed version.
- Eager: separates at fuel 3. SAT={010:5, 101:5}, no UNSAT=5.
- Lazy: separates at fuel 3. SAT={010:4, 101:4}, no UNSAT=4.

Interesting detail: eager separation is **transient** — it holds at fuels 3-4 but at fuel 5, 000(U)=2 = 010(S)=2, and the collision returns. This is an artifact of filler nodes in the unary `not` encoding.

**Conclusion**: Removing types did NOT restore indistinguishability. The separation comes from the rewrite rules themselves, not from the type system.

## The Measure Distinction (Revised)

The initial hypothesis — that indistinguishability correlates with "semantics-blind rules" — was too broad. The BCKW and SK countS results show that **even semantics-blind frameworks can separate** when the right measure is chosen.

The revised picture:

| Framework | Measure | TRUE value | FALSE value | Separates? |
|-----------|---------|------------|-------------|------------|
| DynSemiring obs | countF₀ | 92 (all) | 92 (all) | NO |
| DynSemiring obs | countF₁ | 62-12c | 62-12c | NO (depends on truecount) |
| SK combinators | countK | 1 | 1 | NO (TRUE ≡ FALSE under measure) |
| SK combinators | countS | 0 | 1 | Yes, fuel 10 |
| BCKW | countK | 1 | 2 | Yes, fuel 7 |
| Typed Expr ADT | countT | 1 | 0 | Yes, fuel 2/3 |
| Untyped S-expr | countTag0 | 1 | 0 | Yes, fuel 3 |

A pattern emerges: **separation requires a measure where TRUE and FALSE have different values at convergence.** When the measure assigns the same value to TRUE and FALSE (SK countK, DynSemiring countF₀), separation is impossible even in principle. When they differ (SK countS, BCKW countK, all ADT measures), separation is achievable.

The SK "indistinguishability" under countK was not a deep property of semantics-blind reduction. It was an artifact of choosing countK — a measure that happens to be identical on K and SK (both contain exactly 1 K).

## What Makes the DynSemiring Special

The DynSemiring result is uniquely strong because **every** scalar measure shows indistinguishability, not just one:
- countF₀ = 92 for ALL assignments (total uniformity)
- countF₁ = 62 - 12 * truecount (depends only on truecount)
- z, oplus counts are uniform
- compose count = 144 - 12 * truecount
- termSize = 323 - 24 * truecount

Every measure either is uniform or depends only on the number of true literals. Since SAT/UNSAT assignments can share the same truecount (001 is UNSAT with 1 true, 010 is SAT with 1 true), no measure separates.

This is NOT because the rules are semantics-blind — SK rules are also semantics-blind and countS separates. The likely cause is **commutativity**: compose(a, b) = compose(b, a) in the DynSemiring. This symmetry erases directional information. In SK, application is non-commutative: `app K (app S K)` ≠ `app (app S K) K`. In the DynSemiring embedding, both map to the same compose term. The commutativity collapses distinctions that non-commutative frameworks preserve.

## Revised Hypothesis

Total indistinguishability under ALL scalar measures is a property of **commutative** algebraic frameworks, not of semantics-blind reduction in general.

In non-commutative frameworks (SK, BCKW), there always exists some measure that separates — you just need to choose one where TRUE and FALSE have different values. The indistinguishability under a specific measure (e.g., SK countK) is an accident of the measure, not a property of the framework.

In the DynSemiring, commutativity ensures that ALL measures depend only on symmetric properties of the input (like truecount). No measure can access the asymmetric information (which variables are true) that determines satisfiability.

## The Design Problem for Further Tests

### Why naive string rewriting doesn't work

The obvious next test — flatten SK combinator trees into strings and apply rewrite rules on the string — doesn't actually produce a new framework. If the string-level rules implement the same SK reduction, the intermediate terms are isomorphic (just a different representation of the same tree). Counting tag 10 (K) in a flattened sequence gives the same value as counting K nodes in the tree. The result would be identical by construction, not by discovery.

A genuine new framework would need rewrite rules that are:
1. Semantics-blind (no boolean truth tables)
2. Structurally different from SK reduction (not isomorphic to tree rewriting)
3. Capable of computing boolean formulas (through encoding)

### Candidates for genuine third semantics-blind framework

**Tag systems**: A string rewriting system where only the first symbol is read and a fixed production is appended. Turing-complete (2-tag systems simulate any Turing machine). The encoding is radically different — no tree structure at all.

**Cyclic tag systems**: Even simpler than tag systems. Read one bit at a time, conditionally append a production. Turing-complete.

**Register machines**: Counter machines with increment/decrement/branch-on-zero. No tree structure, no string structure — pure integer registers. Booleans encoded as register values (0/non-zero), logic encoded as register operations.

**Cellular automata (Rule 110)**: Turing-complete, operates on a bit string with local rules. No explicit term structure. Booleans would need to be encoded as spatial patterns.

Each of these is genuinely different from tree-based term rewriting. The encoding challenge is significant — how do you encode a SAT formula into a tag system or cellular automaton in a way that lets you measure meaningful intermediate structure? The encoding itself may need to be the subject of a separate investigation.

## Summary

| Framework | Commutative? | Measure | TRUE≡FALSE? | Separates? |
|-----------|-------------|---------|-------------|------------|
| DynSemiring | Yes | countF₀ | Yes (92=92) | NO |
| DynSemiring | Yes | countF₁ | Yes (by truecount) | NO |
| DynSemiring | Yes | ALL measures | Yes | NO |
| SK | No | countK | Yes (1=1) | NO |
| SK | No | countS | No (0≠1) | Yes, fuel 10 |
| BCKW | No | countK | No (1≠2) | Yes, fuel 7 |
| Typed Expr ADT | N/A | countT | No (1≠0) | Yes, fuel 2/3 |
| Untyped S-expr | N/A | countTag0 | No (1≠0) | Yes, fuel 3 |

The critical variable is not "semantics in rules" but rather:
1. **Does the measure distinguish TRUE from FALSE?** If not, separation is impossible by construction.
2. **Is the framework commutative?** If yes, ALL measures may fail (DynSemiring). If no, there exists a separating measure.

The DynSemiring's total indistinguishability is the genuinely remarkable result. It may be a consequence of commutativity forcing all scalar measures into symmetric functions of the input.

## Open Questions

1. **Is commutativity sufficient for total indistinguishability?** Test another commutative algebra with a different normalization mechanism.

2. **Polynomial arithmetization**: Encode SAT as multilinear polynomial, partially expand. The algebra of polynomial expansion is commutative. If it also shows total indistinguishability, that confirms the commutativity hypothesis.

3. **Can the DynSemiring indistinguishability be broken by a non-scalar measure?** Tree-structural comparisons (not just node counts) might separate — the diffusion analysis showed that terms are structurally different despite identical counts, with first difference at depth 10.
