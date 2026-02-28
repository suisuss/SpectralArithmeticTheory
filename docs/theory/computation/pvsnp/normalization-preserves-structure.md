# Normalization Preserves Structure: A Metatheory of the Natural Proof Barrier

## The Finding

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

## The JIT Regress

The JIT pipeline (JIT.lean) classifies terms into base cases and decides normalization strategy. But the discovery above reveals a regress:

**Level 0 — The SAT problem.** Given formula phi, find an assignment sigma such that all clauses are satisfied.

**Level 1 — The Term encoding.** Map each assignment to a Term via CTerm/De Morgan translation. Per-term normalization is polynomial (depth 2-4 for our test cases). But there are 2^n possible terms. Which one to normalize?

**Level 2 — The JIT.** Analyze formula structure (constraint graph, coupling type) to guide assignment selection. But this analysis is itself a computation on the formula. The JIT must decide which assignments are "worth" normalizing.

**Level 3 — The meta-JIT.** To optimize the JIT's analysis, you'd need an analysis of the analysis. And to optimize that...

Each level of the regress is an instance of the intension/extension gap from Encoding.lean:

- The **intensional** form is the strategy (opaque, named, treated as a unit)
- The **extensional** form is the strategy's output (unfolded, all parts visible)
- Extensionalizing the strategy produces a new form that itself needs a strategy

The `substitution_chain_distinct` theorem proves this gap has no fixed point: extensionalization always produces a structurally distinct term. Applied reflexively, the framework's own machinery for analyzing terms cannot reach a point where further analysis is unnecessary.

## The Fixed Point Impossibility

### What is proved (in Lean, zero sorry)

1. **No syntactic fixed point for extensionalization** (`substitution_chain_distinct`): For any compound observation term, the intensional form, one-step extensional form, and deeply extensional form are all structurally distinct. The chain never converges.

2. **No injective encoding commutes with extensionalization** (`encoding_obstruction_general`): For any injective encoding epsilon and any compound observation term, epsilon(obsRewrite(t)) != epsilon(t). The code of the rewritten form always differs from the code of the original.

3. **Normalization preserves combinatorial structure** (the table above, proved in NANDEncoding.lean): The f_0/z leaf distribution in normalized CNF terms mirrors exactly which literals are satisfied under the given assignment. The normalized form is an isomorphic representation of the satisfiability question, not a reduction of it.

4. **Per-term normalization cost is coupling-invariant** (CoupledAnalysis.lean): Structural sub-term sharing between clauses does not affect the cost of normalizing any individual term. The exponential lives in the number of terms (assignment space), not in the cost of processing each one.

5. **The assignment space is the hard part** (CoupledAnalysis.lean): Independent formulas produce 2^n distinct terms from 2^n assignments. Shared variables collapse the space (sharing halves it), but dense coupling (3-SAT structure) preserves exponential space.

### What this means

Within the DynSemiring framework, the following impossibility holds:

> **No finite sequence of extensionalizations (obsRewrite applications) can determine satisfiability of a CNF-encoded term without examining the leaf structure, which encodes the assignment.**

The normalization machinery (Leibniz product rule + sum rule) pushes obs through the term tree to the leaves, where obs(f_0) -> z and obs(z) -> z. The result is a tree of compose and oplus nodes over {f_0, z} leaves. But the pattern of f_0 vs z IS the assignment, re-encoded. Reading satisfiability from this pattern requires checking the distribution across clause subtrees — the original problem.

The framework cannot "see past" the encoding. It can only unfold structure (extensionalize) or re-name structure (intensionalize). Neither operation compresses the combinatorial content. The information-theoretic content of "which assignment satisfies the formula" passes through normalization intact.

### What this does NOT mean

This is not a proof that P != NP. The impossibility is specific to the DynSemiring framework's extensionalization machinery:

- A polynomial-time SAT algorithm (if one exists) would not need to work within this framework
- The impossibility shows that Leibniz extensionalization + sum rule linearity cannot compress SAT, not that no algebraic technique can
- This is analogous to a **barrier result** (like relativization or natural proofs): it shows that a specific proof/computation technique is insufficient, not that the problem is unsolvable

The correct interpretation is:

> **The DynSemiring framework faithfully represents the P vs NP gap without resolving it.** The gap between polynomial per-term normalization and exponential assignment space search is a structural feature of the algebra, visible in the encoding, preserved through normalization, and immune to the framework's own optimization machinery (the JIT regress).

## Connection to the Halting Problem

The `substitution_chain_distinct` theorem has a temporal reading: if you interpret extensionalization as "one step of execution" and intensionalization as "compilation into a new form," then the chain of distinct forms is an infinite computation that never reaches a halting state. The no-fixed-point result IS the halting problem for self-executing encodings.

The JIT regress is the same phenomenon applied to optimization: any strategy for choosing which computation to perform is itself a computation, which could itself be optimized, ad infinitum. The system cannot lift itself out of the regress because the regress is structural (proved by the encoding obstruction), not contingent.

## A Metatheory of the Natural Proof Barrier

The Razborov-Rudich natural proofs barrier (1997) shows that any proof technique for circuit lower bounds that is *constructive* (produces a distinguishing property) and *large* (satisfied by a random function with noticeable probability) cannot prove P != NP, assuming one-way functions exist. The barrier explains why many proof attempts fail: they use properties that are too "natural" — too symmetric, too uniform — to separate P from NP.

The DynSemiring framework provides an independent, algebraic perspective on why this barrier exists:

1. **The representation tradeoff.** No encoding of Boolean formulas as DynSemiring terms can simultaneously be:
   - **Compact** (polynomial-size representation)
   - **Decidable** (a finite predicate separates SAT from UNSAT)
   - **Stable** (preserved under extensionalization/normalization)

   Normalization preserves structure (our table above). Any decidable property of the normalized form either (a) encodes the full assignment distribution (not compact to check) or (b) ignores clause structure (not a SAT separator). The `containsF0` predicate illustrates (b): it returns true for both SAT and some UNSAT assignments because it ignores distribution.

2. **The extensionalization invariant.** The `substitution_chain_distinct` theorem shows that extensionalization always produces a structurally distinct term. Applied to proof strategies: any "natural" property P of terms satisfies P(t) = P(obsRewrite(t)) only if P ignores the obs structure entirely. But the obs structure IS where SAT information lives. So natural properties (those invariant under the algebra's own operations) cannot access the SAT information.

3. **The JIT regress as barrier mechanism.** A natural proof would need to identify a polynomial-time computable property that separates SAT from UNSAT. The JIT regress shows that within the framework, any such property faces the same exponential search it was meant to avoid. The analysis of the analysis reproduces the original problem — this is the barrier, made algebraic.

The framework does not prove the natural proofs barrier (that requires cryptographic assumptions). Instead, it provides a concrete algebraic setting where the barrier phenomenon is visible and provable without cryptographic assumptions: the DynSemiring's own normalization machinery cannot compress SAT, and this is provable from the algebraic axioms alone.

## What the Framework Contributes

Rather than resolving P vs NP, the framework makes the gap **algebraically visible**:

1. **The gap is localized.** It lives in the assignment space (which term to normalize), not in per-term normalization cost (polynomial for any fixed assignment).

2. **The gap is preserved under normalization.** The sum rule and product rule faithfully transmit the combinatorial structure from input to output. No information is lost or compressed.

3. **The gap generates a regress.** Any meta-level analysis of the gap faces the same gap, because the framework's own machinery (obs, compose, oplus) is what creates the gap.

4. **The gap has a precise algebraic characterization.** It is the distance between the intensional description of a satisfying assignment (a point in 2^n space) and the extensional verification of that assignment (polynomial-time normalization). Finding the point is hard; checking it is easy. The framework represents both sides and proves they don't collapse.

## Files

| File | Role |
|------|------|
| `Obstruction/Encoding.lean` | Encoding obstruction, no fixed point theorem |
| `Obstruction/NANDEncoding.lean` | CTerm, De Morgan, CNF encoding, structural distinguishability |
| `Obstruction/CoupledAnalysis.lean` | Coupling invariance, assignment space analysis |
| `Obstruction/Complexity.lean` | Normalization depth, verification/construction asymmetry |
| `Obstruction/JIT.lean` | JIT pipeline, base case classification |
| `Core/Semiring.lean` | DynSemiring axioms including obs_oplus sum rule |
