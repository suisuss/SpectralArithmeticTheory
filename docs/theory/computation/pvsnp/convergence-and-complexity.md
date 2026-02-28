# Convergence, Divergence, and Computational Complexity

## Date: 2026-02-28

## Summary

The convergence conjecture asks whether the encoding distortion — the gap between the semantic trajectory (eigenvalue scaling, intensional) and the syntactic trajectory (Leibniz extensionalization, positional encoding) — accumulates finitely or diverges totally as the extensionalization chain deepens.

This document investigates the conjecture with a specific focus: **what the answer implies for the structural cost of computation.** Algorithms are not abstract objects — they are representations that must be encoded into machine-readable form and executed. Every execution is an encoding transformation. The convergence conjecture therefore asks whether the cost of encoding transformation has a finite limit or grows without bound.

The investigation proceeds through four analyses:
1. Measuring distortion accumulation precisely (what grows, and how fast)
2. Distinguishing verification-depth from construction-depth chains
3. Connecting chain depth to the structural cost of algorithmic execution
4. Assessing what convergence vs divergence implies for complexity separation

---

## Part 1: What Exactly Accumulates?

### The distortion at each step

The proved results establish three facts about a single extensionalization step:

| Fact | Statement | Lean theorem |
|---|---|---|
| Form changes | obsRewrite(obs(compose(a,b))) != obs(compose(a,b)) | `extensionalize_ne_original_general` |
| Size more than doubles | termSize(rewritten) > 2 * termSize(original) | `extensionalize_more_than_doubles` |
| Meaning is preserved | eval(rewritten) = eval(original) | `semantic_invariance_general` |

The discrepancy at depth k, for an encoding family {epsilon_k}, is:

```
D_k = |epsilon_k(iterDeepRewrite k (obsRewrite(obs(compose(a,b)))))
     - epsilon_k(iterDeepRewrite k (obs(compose(a,b))))|
```

At depth 0, D_0 > 0 (proved: `discrepancy_nonzero_at_zero`). The question is the behavior of D_k as k grows.

### Three components of distortion

The distortion at each depth has three separable components, and they accumulate differently:

**Component 1: Structural divergence (term size).**
Each extensionalization more than doubles term size. After k steps:

```
termSize(iterDeepRewrite k t) > 2^k * termSize(t)
```

This is exponential. The syntactic trajectory explores an exponentially growing term space. Any injective encoding must assign codes from a range at least as large as the number of distinct terms of that size, so the codes themselves must grow (in bit length) at least linearly with k.

**Component 2: Positional divergence (code values).**
The codes assigned by any injective encoding must accommodate the growing term space. For an injective map from terms of size s to naturals, the codes must span at least C(s) values (the number of distinct terms of size <= s). Since the term algebra has branching, C(s) grows exponentially with s. So:

```
epsilon(iterDeepRewrite k t) >= C(2^k * s_0)
```

The code VALUES grow doubly exponentially with depth k. This is the positional divergence: the number used to name the k-th extensionalization is exponentially larger than the number used to name the (k-1)-th.

**Component 3: Semantic invariance (eigenvalue).**
The eigenvalue is constant across the entire trajectory: eval(iterDeepRewrite k t) = eval(t) for all k. The semantic observation is the same number at every depth. The semantic side contributes zero to the distortion growth.

### The accumulation structure

The distortion is entirely on the syntactic side. It grows because:

1. Each extensionalization step introduces new sub-terms (the Leibniz rule produces oplus of two compose sub-terms)
2. Deep rewriting then extensionalizes the sub-terms, producing further expansion
3. The expansion is multiplicative: each obs sub-term spawns two terms via Leibniz, so k levels of extensionalization produce O(2^k) sub-terms

The accumulation is **branching accumulation**. Each extensionalization is a branching event (one obs becomes two compose-obs pairs joined by oplus). The number of branches doubles at each depth. This is the same branching structure as an exhaustive search tree.

---

## Part 2: Verification Chains vs Construction Chains

### Verification has depth 1

To verify a property of an eigenstate: apply obs once, read the eigenvalue.

```
obs(f_n) = n * f_n
```

This is a single intensional operation. It does not extensionalize. No Leibniz rule fires because obs is applied to a primitive eigenstate, not to a compound term. There is no branching. The depth of the extensionalization chain is 0 (no extensionalization needed) or 1 (one obs application with immediate eigenvalue readoff).

The encoding distortion for verification is D_0 — nonzero (proved) but bounded. One step. No accumulation.

### Construction requires arbitrary depth

To construct a compound state from components, the system must compose eigenstates and observe the result:

```
obs(compose(f_m, f_n))
```

This is where Leibniz fires:

```
obs(compose(f_m, f_n)) = oplus(compose(obs(f_m), f_n), compose(f_m, obs(f_n)))
```

The result contains oplus — addition enters the dynamics. If this result is itself part of a larger composition, the outer Leibniz application produces further branching:

```
obs(compose(compose(f_a, f_b), compose(f_c, f_d)))
```

Extensionalizing this produces 4 terms joined by oplus. Each term may contain further compound sub-terms whose obs must be resolved. The chain continues until all obs sub-terms are fully resolved.

For a term of nesting depth d (compositions nested d levels deep), the full extensionalization chain has depth at least d, and produces at least 2^d branches.

### The asymmetry quantified

| Operation | Chain depth | Branches | Distortion growth |
|---|---|---|---|
| Verification (obs on eigenstate) | 0-1 | 1 | Bounded (D_0) |
| Construction (obs on depth-1 compound) | 1 | 2 | D_0 * c for some c > 2 |
| Construction (obs on depth-2 compound) | 2 | 4 | D_0 * c^2 |
| Construction (obs on depth-d compound) | d | 2^d | D_0 * c^d |

The distortion for construction grows exponentially with the structural depth of the term being constructed. Verification's distortion is constant. This exponential gap is a structural property of the extensionalization chain, not a property of any particular algorithm.

### What this means for search

Searching for a satisfying assignment to a Boolean formula is constructing a compound state: the formula is a composition of clauses, each clause is a composition of literals, and finding an assignment requires resolving the interactions across all levels.

The formula's structural depth (nesting of compositions) determines the depth of the extensionalization chain needed to resolve it. For a k-SAT formula with n variables and m clauses:

- Each clause is a composition of k literals: depth at least 1
- The formula is a composition (conjunction) of m clauses: depth at least 2
- Variable interactions cross clauses: resolving them requires extensionalizing to depth proportional to the interaction depth

The key structural fact: **NP-complete problems have interaction depths that grow with input size.** The clauses are not independent — shared variables create cross-clause dependencies that force the extensionalization chain to go deeper. This is precisely the combinatorial structure that makes exhaustive search exponential: each branching event (one extensionalization step) doubles the search space.

---

## Part 3: Encoding Execution as Distortion Accumulation

### The claim restated

Every algorithm is a representation. To execute it, the representation must be:
1. Encoded into a machine-readable format (intensionalization — the algorithm becomes a code)
2. Executed step by step (extensionalization — the code is unfolded via the transition function)
3. The result re-encoded (re-intensionalization — the output is written back as data)

Each step of execution is one pass through the intension/extension cycle. The total cost of executing an algorithm is the total distortion accumulated across all passes.

### Distortion per execution step

A single execution step (one transition of a Turing machine, one beta reduction in lambda calculus) corresponds to one extensionalization of the current term:

1. Read the current state (intensional: the state is a code, treated as a unit)
2. Apply the transition function (extensional: unfold the state according to the rules, producing new sub-terms)
3. Normalize the result (re-intensional: the new sub-terms are combined — via addition, which requires carry propagation — into a single new code)

The distortion of one execution step is D_1 — the single-step encoding distortion. This is bounded (proved to be nonzero, but finite for any given term).

### Distortion across T execution steps

An algorithm that runs for T steps accumulates distortion across all steps. But the accumulation is not additive — it is **compositional**. Each step's output is the next step's input, and the distortion compounds:

```
Total distortion >= D_1 * D_1 * ... * D_1    (T times)
```

But this is imprecise. The more careful analysis: each execution step extensionalizes the current term, which may have been extensionalized by previous steps. The iterated extensionalization result `iterDeepRewrite T t` has:

```
termSize(iterDeepRewrite T t) > 2^T * termSize(t)
```

The term size grows exponentially with the number of execution steps. For T execution steps, the system must manipulate terms of size proportional to 2^T times the input size.

### The polynomial time constraint

A polynomial-time algorithm runs for T = O(n^k) steps on input of size n. The term sizes encountered during execution grow exponentially with T, but T is polynomial in n, so the term sizes grow as:

```
2^{O(n^k)} * n
```

This is exponential in n — **even a polynomial-time algorithm produces exponentially large intermediate terms** in the extensionalization model.

But this analysis is too coarse. A real computation does not simply iterate deepRewrite on the same term. It normalizes (re-intensionalizes) at each step — the carry propagation resolves the addition, producing a new compact code. The re-intensionalization absorbs the extensionalization's branching back into a single state.

The critical question is: **does re-intensionalization (normalization via carry) fully absorb each step's extensionalization, or does distortion leak across steps?**

---

## Part 4: Normalization as Distortion Absorption

### What carry propagation does to the chain

After each extensionalization step, the result contains oplus (addition). The carry propagation resolves this addition into a single normalized code. In the encoding framework:

```
extensionalize:  obs(compose(a,b)) -> oplus(compose(obs(a),b), compose(a,obs(b)))
normalize:       oplus(x, y) -> x + y  (carry propagation, producing a single new eigenstate)
```

The normalization step is the register absorbing the branching. The two branches (compose(obs(a),b) and compose(a,obs(b))) are combined into a single result via addition, which requires carry propagation across all bit positions.

After normalization, the result is a single eigenstate f_{m+n} (in the semantic interpretation). The term size returns to O(1). The exponential blowup from extensionalization is absorbed.

### Why normalization doesn't fully close the gap

Normalization produces the correct **semantic** result (the eigenvalue m+n is correct). But the **syntactic** route to that result — the carry chain — is not represented in the encoding. The encoding before normalization is the code for the extensional form (large, branching). The encoding after normalization is the code for the intensional result (small, flat). These are different codes for the same meaning.

The distortion is not in the final answer — it is in the **process**. Each normalization step requires:
1. Reading two codes (the two branches)
2. Performing carry propagation (non-local, Omega(log n) circuit depth)
3. Writing one new code (the normalized result)

Steps 1-3 are the external state doing work that the encoding cannot internalize. The distortion is the work that the register must perform at each step.

### Per-step normalization cost

For each extensionalization+normalization cycle:

| Phase | What happens | Cost |
|---|---|---|
| Extensionalize | One obs unfolds via Leibniz, producing 2 branches | O(1) structural operation |
| Encode branches | Each branch must be represented as a code | O(encoding length) |
| Carry propagation | Addition of the two branch-codes | Omega(log n) circuit depth |
| Write result | Normalized code stored | O(encoding length) |

The per-step cost is dominated by carry propagation: Omega(log n) per step, where n is the current encoding size.

For T execution steps with input size n, the total normalization cost is at least:

```
Sum_{t=1}^{T} Omega(log(code_size_at_step_t))
```

If the code sizes remain bounded (normalization keeps them small), this is O(T * log n) — polynomial if T is polynomial. The distortion is absorbed.

If the code sizes grow (normalization doesn't fully absorb the extensionalization), the per-step cost grows, and the total cost may become super-polynomial.

### The leakage question

Does normalization perfectly absorb extensionalization at every step? Or does distortion leak — does each normalization leave a residue that makes the next step harder?

**Evidence for full absorption (convergence):**
- In the analytic model, obs is a genuine derivative, and the Leibniz rule is exact. Normalization (computing the sum) is closed-form. No residue.
- For eigenstates of definite eigenvalue, obs produces a definite result. No ambiguity accumulates.
- Finite-precision arithmetic (fixed-width registers) absorbs carry in fixed time per step.

**Evidence for leakage (divergence):**
- Self-encoding creates cross-references: the code for step t may reference codes from earlier steps. Normalization at step t must resolve these references, and the resolution may itself require extensionalization.
- Gödel encoding uses prime factorization, which has no efficient inverse. De-encoding (extracting term structure from a code) requires factoring, and factoring's cost depends on the code's value, which may grow.
- The fundamental theorem: `extensionalize_more_than_doubles`. If the system is self-encoding (operating on its own codes), each extensionalization more than doubles the term being manipulated. Even if normalization absorbs the branching, the CODE on which the next step operates may be exponentially larger because the previous step's result was an exponentially larger number.

### The self-encoding amplification

Here is the critical observation. In a non-self-encoding system, normalization absorbs the distortion fully: the result is a new state, the state is compact, the next step starts fresh. But in a self-encoding system, the state IS a code. The code IS the term. The term's extensionalization more than doubles its size. The extensionalized code, even after normalization, is a LARGER number than the original code (because it encodes a larger term).

The self-encoding constraint means: normalization cannot shrink the result back to the original code size, because the normalized result is semantically different from the original (it's the next step's output, not the same as the current step's input). The code size grows with the computation's progress.

**This is the amplification mechanism.** In a self-encoding system:
1. Step t operates on code c_t (size s_t bits)
2. Extensionalization produces a term of size > 2 * s_t (more-than-doubling)
3. Normalization resolves the addition but produces a new code c_{t+1}
4. c_{t+1} encodes the result of step t, which is semantically different from c_t
5. If the computation is constructing increasingly complex objects (as search does), then c_{t+1} > c_t in code value, hence s_{t+1} >= s_t in code size
6. The per-step normalization cost Omega(log s_{t+1}) is non-decreasing
7. The total cost over T steps is at least Sum Omega(log s_t), which may grow super-linearly even for polynomial T

---

## Part 5: Convergence vs Divergence — The Assessment

### What convergence means precisely

Convergence (in the sense of the convergence conjecture) means: there exists an encoding family {epsilon_k} such that the discrepancy D_k between the extensionalized path and the intensional path vanishes as k -> infinity.

In computational terms: **the cost of converting between the extensional form (what execution produces) and the intensional form (what the encoding requires) can be made arbitrarily small by choosing the right encoding.**

If convergence holds, then:
- The distortion is a finite-depth phenomenon
- There exists a limiting encoding where execution and encoding are compatible
- The structural cost of encoding transformation is bounded
- The von Neumann bottleneck (memory vs processor) is a finite-depth artifact

### What divergence means precisely

Total divergence means: for every encoding family, there exist terms where the discrepancy stays above a positive bound for all depths.

In computational terms: **no encoding strategy can fully reconcile execution with representation. The structural cost of encoding transformation is unbounded.**

If divergence holds, then:
- The distortion grows without bound as the chain deepens
- No limiting encoding exists — self-representation is impossible even approximately
- The structural cost of encoding transformation grows with the depth of the computation
- The von Neumann bottleneck is absolute

### The exponential growth argument for divergence

The strongest evidence for divergence:

1. `extensionalize_more_than_doubles`: each step more than doubles term size
2. After k steps, term size > 2^k * original size
3. Any injective encoding from terms of size s requires codes of value at least exponential in s (because the number of distinct terms of size s is exponential)
4. The codes at depth k are therefore doubly exponential in k
5. For an encoding family {epsilon_k} to make D_k vanish, epsilon_k must map the exponentially-larger extensionalized form and the exponentially-smaller original form to codes that are close together
6. But injectivity prevents this: the two forms are DISTINCT terms (proved), so they must get DISTINCT codes, and the code gap is at least 1 for any injective encoding

The minimum possible discrepancy is 1 (the gap between two distinct codes). For D_k to vanish, it would need to drop below 1, which is impossible for integer-valued codes.

### The subtlety: normalized discrepancy

The convergence conjecture as stated uses integer discrepancy, which is always >= 1 for distinct terms under injective encoding. This means **weak convergence as literally stated is false** — the discrepancy is always >= 1 for depth 0 (proved), and the terms remain distinct at every depth (by extensionalize_ne_original_general applied to the iterated form), so the discrepancy is >= 1 at every depth.

Wait. That needs more care. At depth k > 0, both paths go through iterDeepRewrite, which may bring the two forms closer. The extensionalized form and the original form are distinct at depth 0. After one deep rewrite, they may become more similar (if deepRewrite normalizes both toward the same normal form).

**If the rewriting system is confluent and terminating**, both the extensionalized and original forms converge to the same normal form. In that case, for large enough k, iterDeepRewrite k (extensionalized) = iterDeepRewrite k (original), and the discrepancy is exactly 0.

This would make strong convergence TRUE, contradicting the earlier assessment. The key question: does iterDeepRewrite k eventually identify the two forms?

### The confluence resolution

The confluence result (from confluence.md) establishes that deepRewrite has unique normal forms for the fragment where it terminates. If both the extensionalized form and the original form are in the terminating fragment, they converge to the same normal form (because they have the same semantics, and the rewriting is confluent and semantics-preserving).

In that case:
- The discrepancy is nonzero at depth 0 (proved)
- The discrepancy may decrease at each subsequent depth
- The discrepancy reaches 0 at the depth where both forms hit their common normal form

**This suggests convergence is TRUE for the terminating fragment.** The extensionalization chain converges because the rewriting system normalizes.

### Why this doesn't resolve the computational question

If convergence holds because both forms normalize to the same normal form, the convergence depth — the number of deep rewrite steps needed to reach normal form — is itself the interesting quantity.

The convergence depth for a term of size s is at most the longest rewriting chain from s to normal form. If the rewriting system has exponential worst-case normalization time (as suggested by `extensionalize_more_than_doubles`), then the convergence depth is exponential.

**Convergence with exponential depth is divergence in disguise.** The discrepancy eventually vanishes, but it takes exponentially many steps. If the computation must wait for convergence before proceeding, the cost is exponential.

This is the refined question: **what is the convergence rate?**

- Polynomial convergence depth: the distortion is absorbed efficiently. Compatible with P = NP.
- Exponential convergence depth: the distortion takes exponentially long to absorb. Compatible with P != NP.

---

## Part 6: Convergence Rate as the Complexity Measure

### The proposal

Define the **convergence depth** of a term t as the smallest k such that:

```
iterDeepRewrite k (obsRewrite(obs(t))) = iterDeepRewrite k (obs(t))
```

(Or = up to a suitable equivalence, if exact equality is too strict.)

This is the number of normalization steps needed to reconcile the extensional and intensional forms of a single observation. It measures how much work the register must do to absorb one extensionalization event.

### Convergence depth for verification vs construction

For verification (obs on a primitive eigenstate):
- obs(f_n) is already in "normal form" for observation purposes — the eigenvalue is immediately readable
- Convergence depth: 0 or 1
- Cost: O(1) normalization work

For construction (obs on a compound term of depth d):
- obs(compose(...compose(f_{a_1}, f_{a_2}), ..., f_{a_n})) produces Leibniz expansion with 2^d branches
- Each branch may contain further obs sub-terms requiring resolution
- Convergence depth: proportional to d (at least), potentially exponential in d
- Cost: grows with the structural complexity of the term

### The complexity-theoretic question, restated

**Is the convergence depth for compound terms polynomially bounded in the term's encoding length?**

If yes: every extensionalization chain converges in polynomial steps. The register absorbs the distortion efficiently. Encoding transformation is polynomial-cost. This is consistent with P = NP.

If no: some extensionalization chains require super-polynomial steps to converge. The register cannot absorb the distortion efficiently for complex terms. Encoding transformation is super-polynomial-cost for some problems. This is consistent with P != NP.

### Connection to NP-completeness

An NP-complete problem, encoded as a term in the eigenvalue framework, would be a compound term whose observation (determining satisfiability) requires extensionalizing its full structure. The convergence depth of this term — the number of normalization steps to reconcile the extensional (unfolded, searched) and intensional (compact, verified) forms — corresponds to the computational complexity of solving the problem.

The NP-completeness reduction guarantees that all NP problems encode into SAT. In term-algebraic language: every NP problem's encoding term is reducible (via polynomial-time encoding transformation) to a SAT-encoding term. The convergence depth of the SAT-encoding term is therefore an upper bound on the convergence depth for all NP problems.

**The question P vs NP, in this framework, becomes: what is the convergence depth of SAT-encoding terms as a function of input size?**

---

## Part 7: The Branching-Carry Interaction

### Why the exponential bound might hold

The strongest argument that convergence depth is exponential for NP-complete problems:

**The branching-carry interaction.** Each extensionalization step:
1. Branches (Leibniz produces 2 terms from 1)
2. Requires normalization via carry propagation
3. The carry propagation cost is Omega(log s) where s is the current code size
4. The code size after branching is at least doubled (more-than-doubles theorem)
5. So the carry cost at the next step is at least Omega(log(2s)) = Omega(1 + log s)

The carry cost grows logarithmically with each branching step. After d branching steps:
- Code size: at least 2^d * s_0
- Per-step carry cost: Omega(d + log s_0)
- Total carry cost through depth d: at least Sum_{i=1}^{d} Omega(i) = Omega(d^2)

For a term of encoding length n with structural depth d = O(n) (as in a SAT formula with n variables), the total carry cost is at least Omega(n^2). This is polynomial — not super-polynomial.

**The branching-carry interaction alone does not give a super-polynomial bound.** The logarithmic growth of carry cost, combined with the linear depth of the extensionalization chain, gives a polynomial total cost.

### Where super-polynomial cost could enter

The polynomial bound above assumes that each extensionalization step is independent — the carry propagation at step t does not increase the work at step t+1 beyond the size increase. But in a self-encoding system with cross-clause variable interactions (SAT), this independence fails:

1. **Variable sharing creates cross-branch dependencies.** Assigning a value to variable x in clause C_1 affects the extensionalization of clause C_2 (which also contains x). The extensionalization of C_2 cannot proceed independently of C_1.

2. **Dependencies force sequential extensionalization.** The branches cannot be resolved in parallel — each branch's normalization depends on the others' results (because shared variables connect them). This sequentializes the 2^d branches.

3. **Sequential processing of exponentially many branches is exponential.** Even if each branch is cheap (polynomial), processing 2^d branches one at a time takes 2^d steps.

This is the familiar exponential blowup of exhaustive search, but now grounded in the encoding framework: the extensionalization chain has 2^d branches, the branches are not independent (variable sharing creates dependencies), and sequential resolution of dependent branches is exponential.

### The structural content of this argument

The argument identifies **variable sharing** (or more generally, **non-local interaction in the problem structure**) as the mechanism that forces sequential processing of exponential branches. This is:

- In SAT: shared variables across clauses
- In the eigenvalue framework: shared sub-terms across branches of the Leibniz expansion
- In the encoding obstruction: the carry chain crossing bit positions (addition is non-local)

All three are instances of the same structural phenomenon: **non-local interaction prevents parallel collapse of the extensionalization tree.** The branches must be resolved sequentially because each branch's normalization depends on others' state (through shared variables/sub-terms/bit positions).

---

## Part 8: Assessment and Open Questions

### What is established

1. **The distortion exists and is nonzero at depth 0.** Proved in Lean (`discrepancy_nonzero_at_zero`). The encoding gap between intensional and extensional forms is a theorem, not a conjecture.

2. **The distortion grows exponentially per step.** Proved in Lean (`extensionalize_more_than_doubles`). Each extensionalization step more than doubles term size.

3. **Verification has bounded distortion.** Observation of primitive eigenstates does not trigger extensionalization. No branching. Constant cost.

4. **Construction has depth-dependent distortion.** Observation of compound terms triggers Leibniz extensionalization. Branching grows exponentially with structural depth.

5. **Normalization (carry propagation) absorbs individual steps.** But the total cost across all steps depends on whether branches can be processed in parallel or must be sequential.

### What is conjectured

6. **The convergence conjecture may resolve to "convergence with exponential depth" for NP-complete instances.** The rewriting system is confluent, so the extensionalized and intensional forms eventually normalize to the same result. But the normalization depth may be exponential because variable-sharing forces sequential branch resolution.

7. **The convergence rate IS the complexity measure.** The number of normalization steps to reconcile extensional and intensional forms corresponds to the computational complexity of the problem. Polynomial convergence depth = polynomial-time solvable. Exponential convergence depth = exponential-time required.

### What remains to prove

8. **Formalize the branching-dependency structure for SAT.** Define precisely what "variable sharing prevents parallel branch resolution" means in the eigenvalue framework. This requires encoding SAT as a term-algebraic object and proving that the extensionalization tree has non-collapsible dependencies.

9. **Prove that the confluence depth for SAT-encoding terms is super-polynomial.** This is the convergence-to-complexity bridge. It requires showing that no rewriting strategy can reach normal form in polynomial steps for worst-case SAT instances.

10. **Connect confluence depth to Turing machine time.** Show that k steps of iterDeepRewrite correspond to at most polynomial overhead over k steps of a Turing machine (or vice versa). This would make the convergence-depth measure equivalent to standard time complexity up to polynomial factors.

### The honest assessment

The convergence conjecture, when analyzed carefully, likely resolves to **convergence with problem-dependent depth**: the extensionalization chain always converges (by confluence), but the convergence rate depends on the problem's structure. For verification (eigenstates), convergence is immediate. For construction (compound terms with non-local interactions), convergence may require exponentially many steps.

This reframing transforms the convergence conjecture from a binary question (converges or diverges?) into a quantitative one (how fast does it converge?). The quantitative question is structurally equivalent to the complexity question: how much normalization work does the register need to reconcile extensional execution with intensional encoding?

The framework does not yet prove P != NP. But it provides a structural account of WHY the verification/construction gap exists (extensionalization branching), WHERE the computational cost resides (carry propagation across dependent branches), and WHAT would need to be shown (super-polynomial confluence depth for NP-complete encoding terms) to establish the separation.

The gap between this structural account and a proof is the gap between understanding why something should be true and proving that it is. The encoding obstruction narrows that gap by identifying the precise algebraic mechanism (addition non-locality in self-encoding systems with branching extensionalization) that makes construction harder than verification. Whether this mechanism can be turned into a proof technique that survives the barrier results is the open question.

---

---

## Part 9: Update -- Lean Formalization Results (2026-02-28)

The new Lean formalization (SAT.lean, CostBounds.lean, Complexity.lean Part 8, VarSharing.lean) refines the convergence-complexity connection:

1. **Convergence depth is now quantified for specific term families.** Compose chains of k obs-free atoms require exactly k-1 passes (proved for k=2..6). This is linear, not exponential, but it's linear in clause width -- and clause width is the parameter that separates 2-SAT (P) from 3-SAT (NP-complete).

2. **The convergence rate depends on obs placement.** Obs at every level (nestedObsCompose) gives constant convergence rate (2 passes). Obs only at the boundary (compose chains) gives linear convergence rate (k-1 passes). This is the structural analogue of "certificates enable fast convergence."

3. **Variable sharing doesn't affect single-assignment convergence.** Under a fixed assignment, all formulas with the same shape converge at the same rate regardless of variable sharing. The sharing effect is across the assignment space, not within a single normalization trajectory.

4. **The Leibniz rule is algebraically forced.** There is no alternative rewrite that avoids the branching. The convergence rate's lower bound comes from the algebraic structure, not from a particular algorithm choice. See [leibniz-uniqueness.md](leibniz-uniqueness.md).

---

## Related

- [encoding-complexity.md](encoding-complexity.md) -- P vs NP as encoding execution problem
- [leibniz-uniqueness.md](leibniz-uniqueness.md) -- Leibniz rule is forced, certificates as pruning, lower bound structure
- [normalization-depth.md](normalization-depth.md) -- Normalization depth, fixed points, and halting
- [barrier-analysis.md](barrier-analysis.md) -- Barrier analysis for the encoding obstruction
- [../encoding-obstruction.md](../encoding-obstruction.md) -- The core trilemma
- [../convergence-conjecture.md](../convergence-conjecture.md) -- The convergence conjecture (original statement)
- [../addition-non-locality.md](../addition-non-locality.md) -- Carry propagation as the mechanism
- [../computing-as-external-state.md](../computing-as-external-state.md) -- Computation = language + external state
- [../information-domain.md](../information-domain.md) -- The refined obstruction: oplus as the obstacle
- [../impossibility-hierarchy.md](../impossibility-hierarchy.md) -- Four levels of impossibility
