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

**Measurement**: countK (number of K combinators in the term).

**Result**: SAT/UNSAT collisions persist at EVERY fuel level tested (0 through 30). At no intermediate step does countK separate SAT from UNSAT. At convergence (fuel 30), both SAT (→ K) and UNSAT (→ SK) contain exactly 1 K, so even the endpoint doesn't separate via this measure.

**Key property**: S-reduction DUPLICATES subterms. S x y z → xz(yz) copies z, creating structural proliferation. K-reduction discards, but the net effect is complex intermediate terms.

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

## The Semantics Distinction

The results split cleanly along one axis: **whether the rewrite rules encode boolean truth tables**.

| Framework | Rules know about booleans? | Separates? |
|-----------|---------------------------|------------|
| DynSemiring obs | No (generic Leibniz) | NO |
| SK combinators | No (generic K-discard, S-distribute) | NO |
| Typed Expr ADT | Yes (pattern match on T/F/and/or/not) | Yes |
| Untyped S-expr | Yes (match on tags 0/1/3/4) | Yes |

The type system is irrelevant. What matters is whether the reduction rules contain the semantic content of boolean evaluation.

In SK combinators, `K x y → x` is a generic structural rule — "discard the second argument." It doesn't know it's computing TRUE. The boolean semantics emerges from the Church encoding, not from the rules.

In both ADT versions, `and false _ → false` IS the truth table for AND. The rule explicitly encodes the semantic relationship between AND and FALSE. The boolean meaning is in the rules, not just in the encoding.

## Refined Hypothesis

SAT indistinguishability under scalar measurement is a property of **semantics-blind** reduction systems: systems whose rewrite rules are generic structural operations that know nothing about boolean logic.

The phenomenon requires:
1. **Semantic encoding**: booleans must be encoded into primitives whose meaning comes from their structural role (K selects first argument, S distributes), not from explicit boolean rules.
2. **Generic reduction**: the rewrite rules must not encode boolean truth tables. They must be structural operations that happen to compute boolean logic through the encoding.
3. **Structural proliferation** (tentative): the reduction mechanism may need to create intermediate complexity (S-duplication, Leibniz expansion) rather than monotonically simplify. This still needs testing — it may be a consequence of (1) and (2) rather than an independent requirement.

The critical insight: when boolean semantics is pushed entirely into the encoding (Church booleans in SK, f₀/f₁ in DynSemiring), the reduction mechanism — which is semantics-blind — cannot extract it from scalar measurements. When boolean semantics is in the rules themselves (truth-table pattern matching), extraction is trivial.

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

## What We Know So Far

The four frameworks tested split cleanly:

| Framework | Semantics in rules? | Separates? |
|-----------|---------------------|------------|
| DynSemiring obs | No (generic Leibniz) | NO |
| SK combinators | No (generic K-discard, S-distribute) | NO |
| Typed Expr ADT | Yes (pattern match on T/F/and/or/not) | Yes, fuel 2/3 |
| Untyped S-expr | Yes (match on tags 0/1/3/4) | Yes, fuel 3 |

The distinguishing variable is whether the rewrite rules encode boolean semantics. Type information is irrelevant. The "structural proliferation" hypothesis (from the earlier analysis) may still be relevant but is confounded with the semantics distinction — the semantics-blind frameworks also happen to be the ones that create structural complexity during reduction.

To disentangle these two factors, we would need either:
- A semantics-blind system that simplifies monotonically (no structural growth) — to test if semantics-blindness alone suffices for indistinguishability
- A semantics-aware system that creates structural growth — to test if truth-table rules always enable separation even with complex intermediate terms

Neither of these is easy to construct, which suggests the two properties may be intrinsically linked.
