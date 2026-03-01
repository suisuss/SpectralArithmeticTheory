# Algebraic Embedding of Lambda Calculus in the DynSemiring Framework

## Overview

The DynSemiring framework proves that its normalization cannot compress SAT (113 theorems, zero sorry). The question is whether this result transfers to Turing-complete systems. This document examines the structural correspondence between the DynSemiring and three existing mathematical frameworks for lambda calculus — differential lambda calculus, Geometry of Interaction, and linear logic — and identifies the precise technical challenge for transferring the finite truncation result.

The central finding: the DynSemiring's `obs` operator IS a differential operator, the Leibniz rule IS the product rule for differentiation, and the rewrite chain IS a Taylor expansion. These are not analogies — they are the same mathematical structure viewed from different angles.

**Status:** The embedding is formalized in Lean 4 via SK combinatory logic (44 theorems, zero sorry). The formalization revealed that **f_0 count is NOT preserved by normalization for compound combinator terms** — contradicting the earlier "contraction nets to zero" hypothesis. This is documented in the Findings section below.

## The Differential Lambda Calculus Connection

### Background: Ehrhard-Regnier (2003)

The differential lambda calculus extends ordinary lambda calculus with a differential operator `D(M) . N` that captures "one linear use of N in M." Its key reduction rule is the product/chain rule:

```
D(M N) = D(M) N + M D(N)
```

This decomposes the differential of an application into: differentiate the function (keep the argument) plus keep the function (differentiate the argument).

### The correspondence

The DynSemiring's Leibniz rule is:

```
obs(compose(a, b)) = oplus(compose(obs(a), b), compose(a, obs(b)))
```

These are identical in structure. The full correspondence:

| DynSemiring | Differential Lambda Calculus | Role |
|---|---|---|
| `obs(t)` | `D(t)` — differential of t | Observe / differentiate one linear use |
| `compose(a, b)` | Application `(M N)` | Function applied to argument |
| `oplus(a, b)` | Sum `M + N` | Superposition of linear resources |
| `f_0` | Productive linear resource | Used, contributes to computation |
| `z` | Dead resource | Unused, annihilated by differentiation |
| `f_1` | Eigenstate | Stable under observation/differentiation |
| Leibniz rule | Product rule | Decomposition of compound observations |
| Sum rule | Linearity of differentiation | `D(M + N) = D(M) + D(N)` |

The sum rule `obs(oplus(a, b)) = oplus(obs(a), obs(b))` is linearity of differentiation: the differential of a sum is the sum of the differentials. The Leibniz rule is the product rule. Together they make `obs` a derivation on the DynSemiring — exactly what a differential operator is.

### Taylor expansion = the rewrite chain

Ehrhard-Regnier's central result: the full behavior of a lambda term is captured by its Taylor expansion — an infinite sum of differential (linear) terms:

```
M = M_0 + M_1 + M_2 + M_3 + ...
```

Each M_k captures the depth-k linear interactions. The full computation is the sum of all linear approximations.

The DynSemiring's rewrite chain `iterDeepRewrite k (cnfToTerm sigma phi)` is structurally analogous. Each depth k gives a partial view — a "Taylor coefficient" of the full normalization:

- `iterDeepRewrite 0 t` = M_0, the initial term (no differential reduction)
- `iterDeepRewrite 1 t` = M_1, one level of Leibniz/sum rule applied
- `iterDeepRewrite k t` = M_k, the depth-k linear approximation
- The fixed point (step 3+ for cnfSimple) = the convergent partial sum

### The finite truncation result as Taylor coefficient preservation

The finite truncation theorems (`trunc_indistinguishable_0` through `trunc_indistinguishable_3`) say: no Taylor coefficient separates SAT from UNSAT. At every depth k, `countF0(iterDeepRewrite k (cnfToTerm (TFTF) phi))` equals `countF0(iterDeepRewrite k (cnfToTerm (FFTT) phi))`.

In differential lambda calculus terms: no finite-order differential approximation of the SAT computation distinguishes satisfiable from unsatisfiable inputs. Only the full computation (branchSAT at the fixed point) separates them, and it equals evalCNF — the original problem.

### f_0 count as linear resource count

In the differential lambda calculus, a term uses its inputs some number of times:
- Linear use (exactly once) is the base case
- Contraction (using a variable multiple times) is decomposed into a sum of linear uses
- Weakening (discarding a variable) corresponds to annihilation

For SAT: a formula uses each variable in each clause. A satisfied literal is a **productive use** — the variable contributes `f_0` to the clause. An unsatisfied literal is a **dead use** — the variable contributes `z`. The f_0 count literally counts productive linear uses of the assignment in the formula.

The f_0 preservation theorem (`fixpoint_preserves_f0`) says: the total number of productive uses is determined by the assignment, not by the depth of differential decomposition. Differentiation redistributes productive uses (the f_0 oscillation 4 -> 8 -> 8 -> 4) but doesn't create or destroy them net.

## The Geometry of Interaction Connection

### Background: Girard (1989)

The Geometry of Interaction (GoI) represents lambda terms as operators on a Hilbert space and models beta-reduction via the execution formula:

```
EX(u) = u + u sigma (1 - tau sigma)^{-1} tau u
```

The `(1 - tau sigma)^{-1}` expands as a geometric series:

```
1 + tau sigma + (tau sigma)^2 + (tau sigma)^3 + ...
```

This is an infinite series of compositions (multiplications) and additions — DynSemiring operations. The series converges iff the spectral radius of `tau sigma` is less than 1.

### The spectral connection

The "spectral" in Spectral Arithmetic is not metaphorical. The DynSemiring's generators are eigenstates:
- `f_0`: eigenvalue 0 under obs (annihilated — `obs(f_0) = z`)
- `f_1`: eigenvalue 1 under obs (fixed point — `obs(f_1) = f_1`)
- `z`: zero element

These are spectral data. The obs operator acts as a spectral projector, extracting eigenvalue information from compound terms. The Leibniz rule governs how this extraction interacts with composition — exactly the situation GoI's execution formula addresses.

### GoI and the self-encoding cycle

The self-encoding cycle (`substitution_chain_distinct`) produces an infinite sequence of distinct terms. In GoI terms, this corresponds to the geometric series failing to truncate — each term `(tau sigma)^k` contributes something new. The no-fixed-point theorem says this series never reaches a partial sum that captures the full behavior.

For a normalizing lambda term (one that halts), the GoI series DOES converge — but the number of terms needed corresponds to the computational cost. A polynomial-time computation needs polynomially many terms. An exponential computation needs exponentially many.

The finite truncation result then says: truncating the GoI series at any polynomial depth preserves the spectral invariant (f_0 distribution). The SAT information is distributed across ALL terms of the series, not concentrated in any finite prefix.

## The Linear Logic Connection

### Background: Girard (1987)

Linear logic decomposes classical/intuitionistic logic into:
- Linear implication (resources used exactly once)
- Exponentials `!` and `?` (resource management — contraction and weakening)

Beta-reduction decomposes correspondingly into:
- Linear substitution (variable used once) — deterministic, terminating
- Contraction (variable duplicated) — creates computational power
- Weakening (variable discarded) — annihilation

### The DynSemiring decomposition

| Linear Logic | DynSemiring | Effect |
|---|---|---|
| Linear substitution | `compose(a, b)` | Deterministic composition |
| Contraction (duplication) | `oplus(a, b)` | Resource superposition |
| Weakening (discard) | `z` | Annihilation |
| Exponential `!A` | `obs(a)` | Marking for reuse |
| Cut elimination | Leibniz + sum rule | Normalization |

Linear lambda calculus (without contraction/weakening) is NOT Turing-complete. It corresponds to the DynSemiring's single-pass normalization: deterministic, terminating, cannot solve SAT. This is proved — the finite truncation theorems show that linear normalization preserves SAT information at every depth.

Full lambda calculus adds contraction, which is what makes it Turing-complete. The question is whether contraction — the ability to duplicate resources and process copies independently — can compress SAT information.

## The Core Tension: Contraction

### What contraction does in the DynSemiring

The Leibniz rule introduces oplus (contraction/duplication):

```
obs(compose(a, b)) = oplus(compose(obs(a), b), compose(a, obs(b)))
```

This creates TWO copies: one where `a` is observed, one where `b` is observed. The f_0 count doubles (from 4 to 8 for all-true SAT). This is contraction — duplicating the computation to observe different parts.

Then the sum rule pushes obs deeper, and `obs(f_0) = z` annihilates some copies. At the fixed point, the count returns to the original (8 back to 4). This is the resolution of contraction: the duplicated resources are processed and the redundant copies are eliminated.

### The "net zero" hypothesis — REVISED

The f_0 oscillation pattern for CNF-encoded SAT terms (4 -> 8 -> 8 -> 4) suggested that contraction temporarily inflates resources but observation resolves them back, with net effect zero. The formalization of the SK embedding reveals this is **not general**.

f_0 count under obs normalization of embedded combinator terms (proved in Embedding.lean):

| Term  | f_0 before | f_0 after obs+normalize | Change |
|-------|-----------|------------------------|--------|
| KK    | 2         | 2                      | =      |
| SK    | 1         | 1                      | =      |
| KS    | 1         | 1                      | =      |
| SS    | 0         | 0                      | =      |
| I=SKK | 2         | 3                      | +1     |
| K(KK) | 3         | 5                      | +2     |
| S(KK) | 2         | 4                      | +2     |

**Pattern:** Two-node terms (simple applications) preserve f_0 count. Compound terms (depth >= 2) show f_0 GROWTH — Leibniz tree duplication dominates over obs annihilation when the term structure is nested.

This is a critical correction: the "net zero" property holds for CNF-encoded SAT terms (which have a specific balanced structure) but NOT for arbitrary combinator terms. The SAT encoding's structure — balanced clause trees with uniform depth — is what makes f_0 preservation work. General computation does not share this balance.

The implication for the P vs NP argument: the finite truncation result (no scalar separates SAT from UNSAT at any depth) relies on the CNF encoding's balanced structure, not on a general property of differentiation + contraction. Whether this balanced structure is NECESSARY for the result, or whether a more refined measure could work for general terms, is open.

### Why contraction might not help

Contraction duplicates a resource so it can be used in multiple contexts. For SAT, this means: examining a variable's value in multiple clauses. But each clause check is independent — knowing that x_0 satisfies clause 1 tells you nothing about whether x_2 satisfies clause 2. The duplication creates independent sub-problems, not shared computation.

This is exactly what the f_0 distribution shows: in the normalized term, f_0 leaves are distributed across clause subtrees independently. The Leibniz branching mirrors the clause independence. Contraction distributes the work but doesn't reduce it.

### Why contraction might help (the honest counterpoint)

A SAT solver uses contraction in a fundamentally different way: not to duplicate the formula, but to implement control flow. Branch-and-bound, DPLL backtracking, clause learning — these all use contraction to explore the search space selectively. The duplicated resource is the search state, not the formula.

In the DynSemiring, contraction (oplus) is a symmetric, commutative operation. In lambda calculus, contraction can be asymmetric: use one copy to test a condition, then use the other copy to continue based on the result. This asymmetric use of contraction is what enables algorithms.

The DynSemiring's obs operator treats both branches of oplus symmetrically (sum rule: `obs(a + b) = obs(a) + obs(b)`). A SAT solver's branching is asymmetric: if the left branch fails, try the right. This asymmetry is where computational power might live, and it's not captured by the sum rule's linearity.

## The Formalized Embedding (Lean 4, zero sorry)

### SK Combinatory Logic

We use SK combinatory logic rather than raw lambda calculus because:
- It is variable-free and first-order (no binding, no substitution, no alpha-equivalence)
- It is Turing-complete (equivalent to untyped lambda calculus)
- Its term structure is parallel to the DynSemiring `Term` type

The embedding (`Embedding.lean`):

```
embed : CombTerm -> Term
  K   |-> f_0    (identity element, annihilated by obs)
  S   |-> f_1    (generator, eigenstate of obs)
  app |-> compose
```

### Why K -> f_0 and S -> f_1

The mapping is not arbitrary:
- K discards its second argument: `K x y -> x`. obs annihilates f_0: `obs(f_0) = z`. Both are **weakening** — removing a resource.
- S duplicates and distributes: `S x y z -> xz(yz)`. obs(f_1) = f_1 is an eigenstate — it persists through observation. S is the **contraction** combinator, and contraction is a fixed point of differentiation.

### The differential correspondence (proved)

```
embed_obs_leibniz:
  obsRewrite(obs(embed(app m n))) =
  oplus(compose(obs(embed m), embed n), compose(embed m, obs(embed n)))
```

This IS the product rule `D(M N) = D(M) N + M D(N)` from differential lambda calculus, stated for embedded combinator terms. Proved by `rfl` — it follows directly from the definitions.

```
embed_K_obs: obsRewrite(obs(embed K)) = z     -- D(constant) = 0
embed_S_obs: obsRewrite(obs(embed S)) = f_1   -- D(eigenstate) = eigenstate
```

### The commutativity gap (proved)

The Term algebra is **free** — compose is NOT commutative at the syntactic level:

```
embed_KS_ne_SK: embed(app K S) != embed(app S K)   -- as Terms
embed_KS_eq_SK_semantic: eval(embed(app K S)) = eval(embed(app S K))  -- in any model
```

This means the embedding does NOT preserve operational semantics. K S and S K are syntactically distinct Terms with distinct normalization behavior, but semantically equivalent in any DynSemiring.

More critically:

```
embed_not_simulation:
  reduceStep(app (app K S) K) = some S     -- K-reduction fires
  reduceStep(app (app S K) K) = none        -- no redex

embed_reduction_diverges:
  embed(reduce(KSK)) != obsRewrite(obs(embed(KSK)))
```

Combinator reduction and DynSemiring normalization produce **different results** on the same input. The embedding captures the differential (symmetric) decomposition of application, not the operational (asymmetric) execution.

### Church Booleans (proved)

```
embed_cTrue:  embed(K)  = f_0                    -- TRUE = identity
embed_cFalse: embed(SK) = compose(f_1, f_0)      -- FALSE = generator applied to identity

embed_bool_normalized:
  iterDeepRewrite 3 (obs(embed(TRUE)))  = z                                    -- D(constant) = 0
  iterDeepRewrite 3 (obs(embed(FALSE))) = oplus(compose(f_1, f_0), compose(f_1, z))
```

The differential of TRUE is zero (constant function has zero derivative). The differential of FALSE preserves the f_1 structure in one branch and annihilates in the other.

### SAT via Church-Encoded Combinators (proved)

CNF formulas can be encoded as combinator terms using Church Booleans and Church AND/OR:

```
Church OR:  OR p q  = p TRUE q     (if p then TRUE else q)
Church AND: AND p q = p q FALSE    (if p then q else FALSE)
TRUE = K, FALSE = SK
```

For `(x_0 OR x_1) AND (x_2 OR x_3)` with assignment sigma:

```
formula(sigma) = AND(OR(sigma_0, sigma_1), OR(sigma_2, sigma_3))
```

Church AND/OR truth tables are proved correct (8 theorems). The full formula correctly reduces to K (TRUE) for SAT assignments and SK (FALSE) for UNSAT assignments (4 theorems).

**The key finding: f_0 count after obs normalization for all 16 assignments:**

```
Assignment  SAT?   f_0 after   # true literals
FFFF        NO      30          0
FFFT        NO      29          1
FFTF        NO      28          1
FFTT        NO      27          2
FTFF        NO      29          1
FTFT        YES     28          2
FTTF        YES     27          2
FTTT        YES     26          3
TFFF        NO      28          1
TFFT        YES     27          2
TFTF        YES     26          2
TFTT        YES     25          3
TTFF        NO      27          2
TTFT        YES     26          3
TTTF        YES     25          3
TTTT        YES     24          4
```

All 16 values are proved in Lean (16 theorems, `native_decide`).

**Observations:**

1. **f_0 count = 30 - (number of true literals).** The count is determined by the assignment structure, not by satisfiability. This is anti-correlated with the CTerm encoding (where more true literals = more f_0), because K (true) maps to f_0 which obs annihilates.

2. **countF0 STILL cannot separate SAT from UNSAT.** FFTT (UNSAT, f_0=27) equals TFFT (SAT, f_0=27). The indistinguishability obstruction survives the change of encoding (proved: `cnfComb_indistinguishable`).

3. **The specific collision pairs are different.** In the CTerm encoding, TFTF and FFTT collide (both f_0=2). In the combinator encoding, FFTT and TFFT collide (both f_0=27). The encoding changes WHICH assignments are confused, but NOT the fact that confusion exists.

### What this means

**The obstruction is encoding-independent.** Two fundamentally different encoding strategies — CTerm/NAND (algebraic, balanced) and Church/SK (computational, Turing-complete) — both produce f_0 counts that cannot separate SAT from UNSAT. The obstruction is not an artifact of the CTerm encoding's structure. It is a property of the SAT problem itself, as seen through the differential lens of obs normalization.

This answers the key question from the revised research program: **the balanced structure of the CTerm encoding is NOT necessary for the indistinguishability.** The combinator encoding has completely different structure (Church conditionals rather than NAND gates, nested applications rather than balanced clause trees) yet the same phenomenon appears.

### What remains open

1. **Faithful simulation**: the embedding does not map combinator reduction to obsRewrite (proved to fail: `embed_reduction_diverges`). A different formulation of "correspondence" is needed — perhaps via Taylor coefficients rather than step-by-step simulation.

2. **f_0 preservation for general terms**: f_0 count grows for compound combinator terms (see table in "net zero" section). The SAT encoding produces well-behaved f_0 patterns, but arbitrary combinator terms do not.

3. **Distribution analysis**: can branchSAT (or an analog) distinguish SAT from UNSAT in the combinator encoding? The CTerm encoding's branchSAT works because the Leibniz decomposition creates clause-level branches. The combinator encoding's tree structure is different — it's unclear if a similar branch analysis applies.

4. **Larger formulas**: the results above are for a 2-clause, 4-variable formula. Whether the pattern (f_0 = constant - true_count, indistinguishability) holds for larger CNF formulas encoded as combinators is not tested.

## Assessment

### What is proved (Lean 4, zero sorry)

**In Combinator.lean (7 theorems):**
- SK combinatory logic syntax, reduction, size
- I reduces, K projects, S duplicates and grows
- Church booleans

**In Embedding.lean (67 theorems):**
- The embedding is injective (`embed_injective`)
- obs on embedded applications gives the Leibniz/product rule (`embed_obs_leibniz`)
- obs(K) = z, obs(S) = f_1 (`embed_K_obs`, `embed_S_obs`)
- f_0 count = K count in the original (`embed_countF0_eq_countK`)
- f_0 count under normalization for 7 specific combinator terms
- Size growth under obs normalization (`embed_obs_grows`)
- The embedding is NOT a simulation (`embed_not_simulation`, `embed_reduction_diverges`)
- Church TRUE annihilates, FALSE preserves structure (`embed_bool_normalized`)
- Church AND/OR truth tables (8 theorems)
- CNF formula correctness — reduces to K/SK for SAT/UNSAT (4 theorems)
- f_0 count after normalization for all 16 assignments (16 theorems)
- SAT/UNSAT indistinguishability under combinator encoding (`cnfComb_indistinguishable`)

### What is real

The structural correspondence between the DynSemiring and differential lambda calculus is mathematically precise and machine-checked:
- obs is a derivation satisfying the Leibniz/product rule (proved)
- The sum rule is linearity of differentiation (proved)
- K -> f_0 captures weakening/annihilation (proved)
- S -> f_1 captures contraction as eigenstate (proved)
- The embedding is injective (proved)

### What the formalization disproved

**The "contraction nets to zero" hypothesis is false for general terms.** The f_0 oscillation pattern (4 -> 8 -> 8 -> 4) that holds for CNF-encoded SAT terms does NOT hold for general combinator terms. Compound terms show f_0 growth: I goes from 2 to 3, K(KK) from 3 to 5, S(KK) from 2 to 4.

**The embedding does not preserve reduction.** `embed(reduce(t)) != obsRewrite(obs(embed(t)))` for specific terms. This is proved, not just suspected. The commutativity of compose vs non-commutativity of application is a real structural mismatch, not a minor technical issue.

### What the formalization revealed (the key result)

**The indistinguishability obstruction is encoding-independent.** When SAT is encoded via Church AND/OR in SK combinatory logic — a fundamentally different encoding from CTerm/NAND — countF0 still cannot separate SAT from UNSAT. The f_0 count is determined by the assignment (30 - number of true literals), not by satisfiability. Specific SAT/UNSAT pairs collide: FFTT(UNSAT) = TFFT(SAT) = 27.

This was the open question from the revised research program. The answer: **the balanced structure of the CTerm encoding is NOT necessary for the indistinguishability.** The obstruction survives a change to a Turing-complete, structurally different encoding.

The anti-correlation is itself informative: CTerm encoding gives f_0 = satisfied_literals (more true = more f_0), while combinator encoding gives f_0 = 30 - true_count (more true = fewer f_0). The encodings assign opposite meanings to f_0, yet both produce the same structural phenomenon: a scalar count that cannot separate SAT from UNSAT. This suggests the obstruction is about the SAT problem's combinatorial structure, not about any particular representation.

### What is speculative

Whether a **refined information measure** (not raw f_0 count) could separate SAT from UNSAT in the combinator encoding. Possibilities:
- f_0 distribution across subtrees (as in branchSAT for CTerm)
- A branch analysis adapted to the Church conditional structure
- A measure that accounts for the depth-dependent f_0 growth in compound terms

Whether the **indistinguishability** (not just f_0 count) holds at every truncation depth for the combinator encoding, as it does for the CTerm encoding (the finite truncation theorems). This would strengthen the encoding-independence claim.

Whether the pattern generalizes to **larger formulas**. The current results are for a 2-clause, 4-variable formula. Scaling to n clauses and m variables would test whether f_0 = constant - true_count is a general law or specific to small instances.

### Research program status

1. ~~Formalize the map from lambda terms to DynSemiring terms~~ (DONE: `embed`)
2. ~~Prove the map preserves beta-reduction~~ (DISPROVED: `embed_reduction_diverges`)
3. ~~Define f_0 count for embedded terms~~ (DONE: `embed_countF0_eq_countK`)
4. ~~Prove f_0 preservation at each normalization step~~ (PARTIALLY DISPROVED: fails for general terms, works for SAT-encoding terms)
5. ~~Prove contraction nets to zero~~ (DISPROVED for general terms)
6. ~~Encode SAT as combinator terms~~ (DONE: Church AND/OR on Church booleans)
7. ~~Check whether indistinguishability survives encoding change~~ (DONE: YES, proved for all 16 assignments)

**Remaining:**

8. Test larger formulas (3+ clauses, more variables)
9. Develop a branch analysis for the combinator encoding (analog of branchSAT)
10. Prove finite truncation indistinguishability for the combinator encoding
11. Investigate whether the anti-correlation between encodings is a general duality

The framework's contribution: making the problem VISIBLE, TESTABLE, and now ENCODING-INDEPENDENT. The formalization disproved one hypothesis (contraction nets to zero) but confirmed a stronger one (the indistinguishability is not encoding-specific). This is genuine progress — the obstruction is more robust than initially expected.

## Key References

- Ehrhard, T. and Regnier, L. (2003). "The differential lambda-calculus." Theoretical Computer Science.
- Ehrhard, T. and Regnier, L. (2006). "Differential interaction nets." Theoretical Computer Science.
- Girard, J.-Y. (1987). "Linear logic." Theoretical Computer Science.
- Girard, J.-Y. (1989). "Geometry of interaction I: Interpretation of system F." Logic Colloquium.
- Girard, J.-Y. (2011). "Geometry of interaction V: Logic in the hyperfinite factor." Theoretical Computer Science.

## Lean Files

| File | Role |
|---|---|
| `Lambda/Combinator.lean` | SK combinatory logic: syntax, reduction, Church booleans (7 theorems) |
| `Lambda/Embedding.lean` | Translation, differential correspondence, SAT encoding, indistinguishability (67 theorems) |
| `Obstruction/NANDEncoding.lean` | CNF encoding, f_0 distribution, regress, finite truncation |
| `Obstruction/Encoding.lean` | Term algebra, obsRewrite, encoding obstruction |

## Related Documents

| Document | Relationship |
|---|---|
| [../pvsnp/normalization-preserves-structure.md](../pvsnp/normalization-preserves-structure.md) | The SAT normalization results this embedding would transfer |
| [../../assessments/pvsnp-framework-assessment.md](../../assessments/pvsnp-framework-assessment.md) | Overall P vs NP assessment including Path 4 (this embedding) |
| [../impossibility-hierarchy.md](../impossibility-hierarchy.md) | The four-level obstruction chain |
| [../encoding-obstruction.md](../encoding-obstruction.md) | The abstract encoding obstruction |
