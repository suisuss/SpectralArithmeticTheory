# P vs NP: Framework Assessment

## What Is Proved

The DynSemiring framework proves, in Lean with zero sorry, that its own normalization machinery cannot compress SAT. Specifically:

1. **The encoding obstruction applies to CNF terms** (`cnfToTerm_is_rewrite_site`): any 2+ clause CNF formula produces a Leibniz rewrite site. The Leibniz rule is the unique correct rewrite (proved). There is no alternative.

2. **Normalization produces distinct forms but preserves content** (`cnf_chain_distinct_*`, `f0_at_fixpoint_*`): the rewrite chain produces 3 structurally distinct terms before converging at step 3. At the fixed point, the f_0 count equals the original — the combinatorial content passes through intact.

3. **The fixed point encodes the same problem** (`regress_*`, 96 theorems across 6 formulas): checking f_0 distribution in the normalized term (`branchSAT`) gives exactly the same result as direct evaluation (`evalCNF`) for every assignment tested. The normalized form re-encodes SAT as a tree property.

4. **No finite truncation of the rewrite chain compresses SAT** (`fixpoint_preserves_f0`, `f0_zero_throughout_unsat`): at every step k of `iterDeepRewrite k (cnfToTerm sigma phi)`, and at the fixed point, the f_0 count is determined by the assignment. The information is never compressed at any truncation depth.

5. **The self-encoding cycle has no fixed point** (`substitution_chain_distinct`): the encode-normalize-re-encode loop never stabilizes. Each iteration produces a structurally distinct term with preserved semantics.

## What Is Not Proved

**P != NP is not proved.** The impossibility is framework-internal: the DynSemiring's normalization machinery (Leibniz + sum rule + obs at leaves) cannot compress SAT. A polynomial-time SAT algorithm, if one exists, need not work via DynSemiring normalization.

## The Gap Between Framework and General Result

### Why the framework result doesn't immediately generalize

To go from "DynSemiring normalization can't compress SAT" to "nothing can compress SAT" (P != NP), you would need to show that any polynomial-time algorithm can be faithfully represented as DynSemiring normalization. This fails for a specific reason:

- **Single-pass normalization always terminates** (confluence + termination, proved). Any single `iterDeepRewrite k t` halts.
- **Turing-complete systems require selective non-termination** — halt on some inputs, diverge on others.
- **The self-encoding cycle always diverges** (`substitution_chain_distinct`) — it's uniformly non-terminating, not selectively.
- Therefore the framework is neither Turing-complete (single-pass always halts) nor captures computation via the cycle (cycle always diverges). It sits between the two.

### Why the framework result is stronger than a single algorithm

The impossibility is not "we tried one algorithm and it didn't work." The Leibniz rule is the **unique minimal correct rewrite** satisfying the DynSemiring axioms (proved). The sum rule is forced by linearity. The encoding (CTerm via De Morgan) is the natural Boolean encoding in the algebra. None of these are design choices — they are forced by the algebraic structure.

The impossibility therefore says: the algebraically forced computation on the algebraically natural encoding of SAT cannot compress SAT. This is a structural result about the algebra, not a contingent failure.

### The finite truncation result

The strongest version of the impossibility: for ANY truncation depth k >= 0, the f_0 count in `iterDeepRewrite k (cnfToTerm sigma phi)` is determined by the assignment sigma. The information content (which literals are satisfied) is present at depth 0 and preserved through every rewrite step to the fixed point. No finite truncation of the framework's fundamental computational process compresses the SAT instance.

This is stronger than "normalization can't solve SAT" because it covers every intermediate state, not just the output. The pipeline is transparent to SAT at every point.

## The Compilation Cost Interpretation

The framework reveals the P vs NP gap as a **compilation/execution asymmetry**:

| Step | Cost | SAT Compression |
|---|---|---|
| Encode formula as Term | Polynomial | None (structural encoding) |
| Normalize (k steps) | Polynomial per step | None (f_0 count preserved at every k) |
| Read result (branchSAT) | Polynomial | None (= evalCNF) |
| Optimize the reading (JIT) | Polynomial per level | None (regress) |

Each step is legitimate polynomial work producing structurally distinct forms. The compilation is real. The compilation benefit for SAT is zero. This gap is provable from the DynSemiring axioms.

## Connection to Known Barrier Results

### Relativization (Baker-Gill-Solovay 1975)

The encoding obstruction is non-relativizing by construction. It examines internal algebraic structure (Leibniz decomposition, f_0 distribution within subtrees), which oracle access would destroy. A relativized version of the framework would have different obs behavior, changing the obstruction.

### Natural Proofs (Razborov-Rudich 1997)

The obstruction is not a natural proof. Natural proofs test combinatorial properties of Boolean function truth tables. The encoding obstruction examines algebraic structure of self-encoding systems. The `containsF0` predicate is "natural" (invariant, polynomial-time) and fails as a separator (proved: `containsF0_same_for_sat_and_unsat`). The `branchSAT` predicate is a separator but equals evalCNF — it's not a new distinguishing property.

### Algebrization (Aaronson-Wigderson 2009)

Plausibly non-algebrizing. The obstruction uses arithmetic (eigenvalues) but doesn't polynomially arithmetize Boolean functions. It examines encoding growth rates and structural compatibility, not polynomial evaluation.

### Assessment

The framework operates in a proof-theoretic space the three barriers weren't designed to capture. Avoiding barriers is necessary but not sufficient — it doesn't guarantee the approach works, only that it isn't blocked for known reasons.

## What Would Be Needed for P != NP

### Path 1: Computational universality

Prove that any polynomial-time algorithm can be represented within the DynSemiring framework in a way that our impossibility applies. This is circular in the obvious formulation: proving universality + impossibility = P != NP, so at least one step must be extremely non-trivial.

The specific obstacle: the framework's normalization is deterministic and terminating. Representing backtracking search (DPLL/CDCL) would require encoding the search tree as a term and normalization as tree exploration. It's unclear whether this is possible within the fixed rewrite rules.

### Path 2: Axiom-level impossibility

Prove that ANY algebraic system satisfying certain minimal axioms (composition, addition, observation with Leibniz) inherits the same obstruction. The impossibility hierarchy argues this informally via the self-encoding chain, but formalizing it requires showing the obstruction is intrinsic to the axiom structure, not specific to our term algebra.

This would require proving: if an algebra has obs, compose, oplus with the Leibniz rule, and can encode CNF formulas, then normalization in that algebra preserves f_0 count. The f_0 preservation would need to follow from the axioms alone, not from term-level computation.

### Path 3: Information-theoretic

Bypass the algebra entirely. Prove that ANY representation of SAT that supports polynomial-time verification must have exponential-size search spaces for construction. This is essentially the P != NP question stated information-theoretically. The framework provides intuition (verification is intensional/local, construction is extensional/non-local) but not a proof.

### Honest assessment of each path

- **Path 1** is likely blocked: the framework isn't Turing-complete, and making it so would break the termination that enables our proofs.
- **Path 2** is the most promising: the obstruction feels axiomatic, and the key results (Leibniz is forced, carry is non-local, no fixed point) do follow from minimal assumptions. But "feels axiomatic" is not a proof.
- **Path 3** is the hardest: it's essentially asking to prove P != NP by a new method, with the framework providing only motivation.

## What the Framework Contributes

The framework's genuine contribution is making the P vs NP gap **algebraically visible and formally precise**:

1. **Localization**: The gap lives in the assignment space (which term to normalize), not in per-term normalization cost. This is proved, not just observed.

2. **Preservation**: The gap survives every operation the algebra offers. Normalization, the JIT, meta-analysis — all transmit the SAT structure faithfully. This is proved at every truncation depth.

3. **Structural forcing**: The gap isn't due to poor algorithm choice. The Leibniz rule is unique, the sum rule is forced, the encoding is natural. The incapacity is algebraically necessary.

4. **The regress**: Any meta-analysis within the framework reproduces the same gap. This is proved for 6 formula classes and connects directly to the impossibility hierarchy's "no bottom" result.

These don't resolve P vs NP, but they provide the clearest algebraic picture of the gap that we're aware of. The framework sees the gap, proves it's structural within the algebra, and shows why the algebra's own tools can't cross it. Whether tools outside the algebra can cross it remains the open question.
