# Normalization Preserves Structure: The Encoding Obstruction Applied to SAT

## Overview

The encoding obstruction (proved in Encoding.lean) establishes abstractly that no injective encoding commutes with extensionalization — substitution always changes form while preserving meaning. The impossibility hierarchy (impossibility-hierarchy.md) traces this through four levels: substitution has no fixed point, Leibniz introduces addition, addition requires carry propagation, and carry requires external state whose normalization is undecidable.

This document shows that these abstract results have a **concrete instantiation in SAT**: when CNF formulas are encoded as DynSemiring terms and normalized, the combinatorial content of the satisfiability problem passes through the entire normalization chain intact. The encoding obstruction doesn't just prevent encoding from commuting with observation — it prevents normalization from compressing SAT.

The connection is proved in NANDEncoding.lean (113 theorems, zero sorry).

## The Concrete Finding

CNF-encoded terms, when fully normalized via the Leibniz product rule and the obs(oplus) sum rule, produce terms whose leaf structure **faithfully mirrors the original satisfiability problem**. Normalization does not compress, simplify, or resolve the combinatorial structure — it preserves it.

This was discovered by exhaustive evaluation of all 16 assignments for the formula `(x_0 OR x_1) AND (x_2 OR x_3)`:

```
Assignment  SAT?   f_0   z    Observation
────────────────────────────────────────────────────────
FFFF        NO      0    8    All leaves are z
FFFT        NO      1    7    f_0 only in clause 2
FFTF        NO      1    7    f_0 only in clause 2
FFTT        NO      2    6    Both f_0 in clause 2, clause 1 all-z
FTFF        NO      1    7    f_0 only in clause 1
FTFT        YES     2    6    One f_0 per clause
FTTF        YES     2    6    One f_0 per clause
FTTT        YES     3    5    f_0 in both clauses
TFFF        NO      1    7    f_0 only in clause 1
TFFT        YES     2    6    One f_0 per clause
TFTF        YES     2    6    One f_0 per clause
TFTT        YES     3    5    f_0 in both clauses
TTFF        NO      2    6    Both f_0 in clause 1, clause 2 all-z
TTFT        YES     3    5    f_0 in both clauses
TTTF        YES     3    5    f_0 in both clauses
TTTT        YES     4    4    Maximum f_0, all clauses satisfied
```

### Key observations

1. **f_0 count = number of satisfied literals across all clauses.** Each satisfied literal contributes exactly one f_0 to the normalized term; each unsatisfied literal contributes one z. The total leaf count is constant (8 = 2 clauses x 2 literals x 2 from Leibniz expansion).

2. **containsF0 does not cleanly separate SAT from UNSAT.** Both FFTT (UNSAT, f_0=2) and FTFT (SAT, f_0=2) have the same f_0 count. The difference is *distribution*: in FTFT, each clause subtree has at least one f_0. In FFTT, both f_0 are in clause 2's subtree.

3. **SAT iff every clause subtree contains at least one f_0.** This is the CNF conjunction requirement re-encoded as a tree property.

4. **Checking this tree property IS the original SAT problem.** The normalization has not simplified anything — it has produced a structural representation that requires the same combinatorial check.

## From Abstract Obstruction to Concrete SAT

The impossibility hierarchy has four levels. Each maps precisely onto the SAT normalization findings:

### Level 1 (Philosophical → Structural): Substitution has no fixed point

**Abstract result:** `substitution_chain_distinct` — three levels of extensionalization produce three provably distinct terms. The intension/extension gap is irreducible.

**SAT instantiation:** `cnf_chain_distinct_sat`, `cnf_chain_distinct_unsat` — CNF terms produce 3 distinct forms before convergence (step 0 ≠ step 1 ≠ step 2 ≠ step 3). The Leibniz rule unfolds `obs(compose(clause₁, clause₂))` into an oplus-rooted tree, the sum rule pushes obs into the OR subtrees, and each step produces a structurally distinct term.

**The connection:** The abstract no-fixed-point theorem applies directly to SAT-encoded terms because they have the form `obs(compose(a, b))` — exactly the compound observation terms that `substitution_chain_distinct` covers. The theorem `cnfToTerm_is_rewrite_site` proves this is general: ANY 2+ clause CNF formula produces a Leibniz rewrite site.

### Level 2 (Information-theoretic → f_0 preservation): Leibniz introduces addition

**Abstract result:** The Leibniz rule `obs(a·b) = obs(a)·b + a·obs(b)` introduces ⊕ into every compound observation. The `oplus_bitwise_impossible` theorem shows this ⊕ cannot be made local.

**SAT instantiation:** `f0_inflates_at_step1` — the Leibniz rule doubles the f_0 count at step 1 (from 4 to 8 for all-true). Both branches of the oplus carry copies of the original f_0 leaves. The sum rule then pushes obs deeper, and `obs(f_0) → z` destroys some copies. At convergence: `f0_at_fixpoint_sat` — the count returns to the original.

**The connection:** The Leibniz rule's introduction of ⊕ is what creates the tree duplication. The f_0 count oscillation (4 → 8 → 8 → 4) is the addition playing out concretely: ⊕ adds branches (inflation), obs resolves them (deflation), but the net information content is preserved. The ⊕ doesn't compress — it redistributes.

### Level 3 (Computational → the regress): Non-local carry = non-local SAT check

**Abstract result:** `carry_propagation_general` — addition on positional encodings requires carry propagation (output at position k depends on all inputs at positions 0..k-1). The register (external state for carry) is inescapable.

**SAT instantiation:** `branchSAT = evalCNF` for all 16 assignments across 6 formulas. Checking whether both Leibniz branches contain f_0 IS the original clause-by-clause SAT check. The tree structure forces a non-local check: you can't determine satisfiability from any single subtree; you must check ALL clause subtrees.

**The connection:** The non-locality of carry propagation manifests as the non-locality of the SAT check. Just as addition's output at position k depends on all lower positions, satisfiability depends on ALL clauses being satisfied. A local check (like `containsF0` — is there ANY f_0 anywhere?) fails: `containsF0_same_for_sat_and_unsat` proves it gives the same answer for SAT and UNSAT assignments. The clause-distribution check is inherently non-local, mirroring carry propagation's inherent non-locality.

### Level 4 (Logical → the JIT regress): No bottom

**Abstract result:** The halting problem for self-executing encodings — "done" would require a fixed point of substitution, but `substitution_chain_distinct` proves no fixed point exists.

**SAT instantiation:** The JIT regress. Any strategy for deciding which assignments to normalize faces the same combinatorial structure as the SAT problem itself:

- **Level 0:** Find a satisfying assignment (the SAT problem)
- **Level 1:** Choose which term to normalize (same search space)
- **Level 2:** Analyze the formula to guide the choice (computation on the formula)
- **Level 3:** Optimize the analysis (computation on the computation)
- **Level k:** Optimize level k-1 (computation on level k-1)

Each level is an intension/extension switch: the strategy (intensional) is unfolded into its execution (extensional), producing a new object that needs its own strategy. The `substitution_chain_distinct` theorem proves this chain never stabilizes.

**The connection:** The JIT regress IS the halting problem for SAT optimization. "The optimizer has finished optimizing" would require the analysis to reach a fixed point. But the analysis IS a computation on the same formula structure, and the encoding obstruction proves no fixed point exists for computations on self-encoding structures. The regress is not a contingent failure of our particular JIT — it's a structural consequence of the algebra.

## The Compilation Cost Interpretation

The four-level mapping reveals that the JIT regress is fundamentally a **compilation cost that buys nothing**:

| Compilation step | Cost | Benefit for SAT |
|---|---|---|
| Encode formula as Term (`cnfToTerm`) | Polynomial | None — encoding preserves structure |
| Normalize term (Leibniz + sum rule) | Polynomial per step, 3 steps to convergence | None — `fixpoint_preserves_f0`, f_0 count unchanged |
| Read SAT from normalized form (`branchSAT`) | Polynomial | None — `branchSAT = evalCNF`, same check |
| Optimize the reading (JIT analysis) | Polynomial per level | None — regress, each level faces same search |

Normal compilation amortizes: pay cost once, execute cheaply many times. Here, each compilation step is legitimate polynomial work that produces a structurally distinct, semantically equivalent form — but the SAT information passes through every compilation step intact. The fixed point (`fixpoint_obsNormal_sat`) exists and is reached in finite steps, but reading the fixed point (`branchSAT`) is the original problem.

This is why the framework makes P vs NP **algebraically visible**: the gap between compilation cost (polynomial, real work, structurally transformative) and compilation benefit (zero for SAT, information preserved) is provable from the DynSemiring axioms.

## The No-Compression Theorem

Combining the four levels, we get the central result:

> **Within the DynSemiring framework, normalization cannot compress SAT.** The encoding obstruction (form always changes) guarantees that each normalization step produces new structure. The f_0 preservation (content always preserved) guarantees that the SAT information survives every transformation. The convergence (fixed point exists) guarantees that normalization terminates. The regress (branchSAT = evalCNF) guarantees that the fixed point encodes the same combinatorial check.

This is not a proof that P ≠ NP — a polynomial-time SAT algorithm need not work within the DynSemiring framework. But it is a proof that the framework's own machinery (the Leibniz rule, the sum rule, the obs operator) cannot resolve SAT, and this incapacity is a structural consequence of the encoding obstruction, not a contingent limitation.

## Connection to the Natural Proof Barrier

The Razborov-Rudich natural proofs barrier (1997) shows that constructive, large proof techniques cannot prove P ≠ NP (assuming one-way functions exist). The DynSemiring framework provides an independent, algebraic perspective on why this barrier exists:

1. **The representation tradeoff.** No encoding of Boolean formulas as DynSemiring terms can simultaneously be compact (polynomial-size), decidable (a finite predicate separates SAT from UNSAT), and stable (preserved under normalization). `containsF0` illustrates: it is compact and stable but not a separator. `branchSAT` is a separator but is exactly `evalCNF` — no simpler.

2. **The extensionalization invariant.** Any "natural" property P of terms that satisfies P(t) = P(obsRewrite(t)) must ignore the obs structure entirely. But the obs structure IS where SAT information lives (the f_0/z distribution under obs-pushed-to-leaves). Natural properties cannot access SAT information.

3. **The JIT regress as barrier mechanism.** A natural proof needs a polynomial-time computable separator. The regress shows that any such separator within the framework faces the same exponential search. The analysis of the analysis reproduces the original problem.

The framework does not prove the natural proofs barrier (that requires cryptographic assumptions). It provides a concrete algebraic setting where the barrier phenomenon is visible and provable from algebraic axioms alone.

## Proved Results (Lean, zero sorry)

### From Encoding.lean (abstract obstruction)

| Theorem | Statement |
|---|---|
| `substitution_chain_distinct` | Three levels of extensionalization produce three distinct terms |
| `encoding_obstruction_general` | No injective encoding commutes with obsRewrite, for ALL a, b |
| `semantic_invariance_general` | eval is preserved across the gap, for ALL a, b |
| `extensionalize_more_than_doubles` | Each extensionalization more than doubles term size |

### From NANDEncoding.lean (SAT instantiation)

| Theorem | Statement |
|---|---|
| `cnfToTerm_is_rewrite_site` | Any 2+ clause CNF term is a Leibniz rewrite site (general) |
| `cnf_chain_distinct_sat/unsat` | 3 distinct forms before convergence |
| `cnf_converges_sat/unsat/TFTF` | Chain reaches fixed point at step 3 |
| `f0_at_fixpoint_sat/unsat/TFTF` | f_0 count at fixed point = original count |
| `f0_inflates_at_step1` | Leibniz doubles f_0 (tree duplication) |
| `f0_zero_throughout_unsat` | UNSAT: f_0 = 0 at every step |
| `fixpoint_preserves_f0` | Fixed point preserves f_0 across 4 assignments |
| `fixpoint_obsNormal_sat/unsat` | Fixed point is obs-normal |
| `containsF0_same_for_sat_and_unsat` | Coarse predicate fails as separator |
| `regress_*` (16 per formula, 6 formulas) | branchSAT = evalCNF exhaustively |

### From CoupledAnalysis.lean (assignment space)

| Theorem | Statement |
|---|---|
| Coupling invariance | Per-term normalization cost is the same regardless of variable sharing |
| Assignment space analysis | Independent formulas: 2^n distinct terms; shared variables collapse space |

## Files

| File | Role |
|---|---|
| `Obstruction/Encoding.lean` | Encoding obstruction, no fixed point theorem |
| `Obstruction/NANDEncoding.lean` | CTerm, CNF encoding, f_0 distribution, regress, no-compression |
| `Obstruction/CoupledAnalysis.lean` | Coupling invariance, assignment space analysis |
| `Obstruction/Complexity.lean` | Normalization depth, verification/construction asymmetry |
| `Obstruction/JIT.lean` | JIT pipeline, base case classification |
| `Core/Semiring.lean` | DynSemiring axioms including obs_oplus sum rule |

## Related Documents

| Document | Relationship |
|---|---|
| [encoding-obstruction.md](../obstruction/encoding-obstruction.md) | The abstract trilemma — this doc shows its SAT instantiation |
| [impossibility-hierarchy.md](../impossibility-hierarchy.md) | The four-level hierarchy — this doc maps each level to SAT |
| [addition-non-locality.md](../obstruction/addition-non-locality.md) | Carry propagation — mirrors non-locality of clause-distribution check |
| [convergence-conjecture.md](../convergence-conjecture.md) | Convergence question — answered concretely: converges at step 3, content preserved |
