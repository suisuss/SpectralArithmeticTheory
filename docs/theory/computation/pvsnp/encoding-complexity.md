# P vs NP as an Encoding Execution Problem

## Date: 2026-02-28

## Summary

P vs NP is standardly framed as a question about algorithms: is there a polynomial-time procedure for SAT? This document reframes it as a question about **encoding execution**: computation is fundamentally the execution of an encoding, encoding execution structurally requires external state, and the cost of that execution is governed by the encoding obstruction. The verification/construction gap is not an accident of known algorithms but a consequence of the algebraic structure of executable encodings.

The argument proceeds in four stages:
1. Computation IS encoding execution (not merely uses encoding)
2. Encoding execution has structurally different costs for verification vs construction
3. The encoding obstruction proves this structural difference at the algebraic level
4. The open question: does the algebraic separation entail the complexity-theoretic separation?

---

## Part 1: Computation is Encoding Execution

### The standard framing and its blind spot

The standard formulation of P vs NP abstracts away encoding. A decision problem is a language L over {0,1}*. An algorithm is a Turing machine. The question is whether the machine halts in polynomial time. The encoding of the problem instance as a binary string is treated as a fixed, uninteresting preliminary — a notational convenience.

This abstraction hides the fact that every step of computation IS an encoding operation. A Turing machine does not "solve" SAT. It:

1. Reads an encoded formula (positional symbols on a tape)
2. Manipulates the encoding (rewrites symbols according to transition rules)
3. Produces an encoded answer (a symbol at a designated position)

Every intermediate step is a transformation of one encoding into another. The tape IS the encoding. The transition function IS the rewriting rule. The computation IS the sequence of encoding transformations. There is no computation "behind" the encoding — the encoding execution is the computation.

### Why this matters for P vs NP

If computation is encoding execution, then the cost of computation is the cost of encoding transformation. The question "is SAT solvable in polynomial time?" becomes: "is there a polynomial-length sequence of encoding transformations that takes an encoded SAT formula to an encoded answer?"

This is not a restatement. It shifts the question from "do fast algorithms exist?" (a question about the space of all possible procedures) to "what is the structural cost of encoding transformation?" (a question about the algebra of encoding itself). The second question is amenable to the encoding obstruction framework.

### The encoding obstruction's contribution

The encoding obstruction (encoding-obstruction.md) establishes:

1. **Computation requires external state.** Any system that executes its own encoding must maintain state (register, tape, accumulator) external to the encoding itself (computing-as-external-state.md).

2. **External state is forced by addition.** The Leibniz rule introduces addition when extensionalizing compound terms. Addition in any unique positional encoding requires carry propagation, which is non-local. The non-locality cannot be absorbed into the encoding (addition-non-locality.md).

3. **The cost of encoding execution is governed by the intension/extension duality.** Verification reads an intensional property (eigenvalue, certificate check — local). Construction performs extensionalization (unfolding structure via the Leibniz rule — introduces addition — non-local).

These are not observations about particular algorithms. They are theorems about the algebra of self-representing systems.

---

## Part 2: Verification vs Construction as Intensional vs Extensional

### Verification is intensional

To verify a SAT certificate: given a formula phi and an assignment sigma, check whether sigma satisfies phi. This is:

- Read the encoded assignment (intensional — the assignment is a fixed object, treated as a unit)
- Evaluate each clause under the assignment (local — each clause depends on a bounded number of variables)
- Confirm all clauses are satisfied (conjunction — local, no carry across clauses)

The verification procedure never needs to extensionalize the search space. It takes one encoded object (sigma) and reads off a property. This is structurally analogous to eigenvalue observation: obs(f_n) = n * f_n. The eigenvalue (satisfaction/non-satisfaction) is read from the state without unfolding the state's internal structure.

Cost: polynomial in the encoding length. This is not because we chose a clever algorithm — it is because verification is an intensional operation, and intensional operations are structurally local.

### Construction is extensional

To find a satisfying assignment (or determine none exists): the procedure must explore the space of possible assignments. This requires:

- Extensionalizing the formula (unfolding its structure to determine which variables interact, which clauses constrain which assignments)
- Constructing candidate assignments (building new encoded objects from components)
- Evaluating interactions between variables across clauses (non-local — a variable assignment in one clause affects satisfiability of other clauses sharing that variable)

The construction procedure necessarily extensionalizes. It cannot treat the formula as a black box — it must unfold the formula's structure, manipulate the components, and re-encode the results. Each extensionalization step introduces addition (via the Leibniz rule or its computational equivalent: combining partial results from different branches of the search).

### The structural asymmetry

| Operation | Mode | Locality | Carry required | Cost structure |
|---|---|---|---|---|
| Verification | Intensional | Local (per-clause) | No | Polynomial (read eigenvalue) |
| Construction | Extensional | Non-local (cross-clause variable interaction) | Yes | ? (this is the question) |

The encoding obstruction proves that this asymmetry is not an artifact of known algorithms. It is a property of encoding execution itself:

- **Intensional operations** (verification, eigenvalue reading, certificate checking) are positionally local — each output position depends on a bounded number of input positions
- **Extensional operations** (construction, Leibniz unfolding, search) introduce addition, and addition is positionally non-local — output at position k depends on all inputs at positions 0..k

---

## Part 3: The Algebraic Separation

### What is already proved

The encoding obstruction trilemma establishes (at the algebraic level):

1. **Eigenvalue observation is linear.** obs(f_n) = n * f_n. The cost of reading the eigenvalue scales linearly with the index. (Proved in Lean — Semiring.lean)

2. **Injective encoding is super-linear.** Any injective pairing function pi: N x N -> N satisfies pi(n,n) in omega(n). Encoding structure requires super-linear growth. (Known result in computability theory — formalized in Pairing.lean)

3. **These cannot be reconciled.** The coalgebra morphism (encoding commutes with observation) requires matching growth rates. Linear observation and super-linear encoding are incompatible. (The trilemma — encoding-obstruction.md)

This is an unconditional algebraic theorem: verification (observation) is structurally cheaper than construction (encoding) in any self-representing eigenvalue system.

### The gap to P vs NP

The algebraic separation is:
- **Observation**: linear (eigenvalue = n * f_n)
- **Encoding**: super-linear (pairing in omega(n))

P vs NP asks about:
- **Verification**: polynomial (certificate checking in O(n^k))
- **Construction**: super-polynomial? (finding a certificate in omega(n^k) for all k?)

The algebraic result gives **linear vs super-linear**. P vs NP requires **polynomial vs super-polynomial**. These are different thresholds. A super-linear function (e.g., n log n) is not necessarily super-polynomial.

This is the honest boundary of what the current framework establishes. The structural asymmetry is proved. The complexity-theoretic consequence is not.

---

## Part 4: The Compounding Question

### Why per-step overhead is not enough

The carry non-locality result (addition-non-locality.md) shows that each extensionalization step costs at least Omega(log n) non-local work (carry propagation in bounded fan-in circuits). But a polynomial-time algorithm can afford polynomially many steps, each costing O(log n). The per-step overhead alone does not separate P from NP.

The question is not whether each step has overhead. The question is whether the **number of extensionalization steps** required for construction is super-polynomial.

### The intension/extension regress

The encoding obstruction proves that substitution has no fixed point: each extensionalization produces a new term that can be re-intensionalized, and the new intensional form requires its own extensionalization. The chain is provably infinite (chain_distinct — proved in Lean, Obstruction/Main.lean).

For **verification**, this regress is irrelevant. Verification reads one eigenvalue from one state. It does not need to follow the chain — it performs a single intensional read.

For **construction**, the regress is the search itself. Finding a satisfying assignment requires exploring the consequence of each variable choice. Each choice extensionalizes part of the formula (substituting a value for a variable, evaluating the resulting clauses). The result may reveal new constraints that require further extensionalization (unit propagation, conflict analysis, backtracking). The search IS the intension/extension regress, applied to the specific structure of the formula.

### The compounding hypothesis

**Hypothesis.** In an NP-complete problem, the number of extensionalization steps required for construction grows super-polynomially with input size, because the intension/extension regress compounds: each extensionalization reveals new structure that requires further extensionalization, and the structure of NP-complete problems is such that this chain cannot be short-circuited.

More precisely: the intension/extension chain for verification has depth 1 (read the eigenvalue). The intension/extension chain for construction (search) has depth that depends on the problem structure. For NP-complete problems, the chain depth is super-polynomial because:

1. Each extensionalization step (substituting a variable, evaluating consequences) introduces addition (combining constraints from different clauses)
2. Addition creates new encoded states that may require further extensionalization (new implications discovered)
3. The NP-completeness structure (every NP problem reduces to this one) means the chain cannot be collapsed — collapsing it would collapse all of NP

This is the central conjecture. It is not proved. What follows is the analysis of what would be needed to prove it and why the encoding obstruction framework is the natural setting.

---

## Part 5: What a Proof Would Require

### The bridge from algebra to complexity

To move from the algebraic separation (linear vs super-linear) to the complexity separation (polynomial vs super-polynomial), one would need:

**Step 1: Formalize the extensionalization chain for SAT.**

Define the sequence of encoding transformations that any procedure solving SAT must perform. In the eigenvalue framework: identify the eigenstates corresponding to formula variables, clauses, and assignments, and characterize the obs applications (extensionalizations) required to determine satisfiability.

**Step 2: Show the chain length is super-polynomial.**

Prove that for any polynomial-time procedure, the number of extensionalization steps is insufficient to resolve all clause interactions in a worst-case SAT formula. This requires showing that the intension/extension regress, when specialized to SAT structure, cannot terminate in polynomial steps.

**Step 3: Show this is not circumventable.**

Prove that no alternative encoding strategy (different pairing, different Gödel encoding, different representation of formulas) reduces the chain length to polynomial. This is the analogue of the barrier results — the proof must be robust to encoding changes.

### Relationship to existing barriers

The encoding obstruction framework interacts with the known barriers:

| Barrier | What it blocks | Encoding obstruction's position |
|---|---|---|
| **Relativization** | Proofs that treat the machine as a black box | The obstruction looks inside the encoding — it examines the structure of the encoding transformations, not just input-output behavior. Non-relativizing by construction. |
| **Natural proofs** | Combinatorial properties satisfied by random functions | The obstruction is structural (algebraic growth rates, carry propagation), not combinatorial (truth table properties). It does not test a random function — it examines the algebra of self-representation. Potentially non-natural. |
| **Algebrization** | Proofs that arithmetize and then relativize | The obstruction uses arithmetization (eigenvalues ARE arithmetic) but does not relativize — the trilemma is about the internal structure of the arithmetic, not its behavior with oracles. Potentially non-algebrizing. |

The encoding obstruction's approach — examining the structural cost of encoding execution rather than the combinatorial properties of Boolean functions — is in a different proof-theoretic space than the techniques the barriers exclude. This does not mean it works. It means the barriers do not obviously block it.

### Connection to Williams' algorithmic approach

Williams (2011) showed that NEXP is not contained in ACC^0 by converting an algorithmic result (a faster-than-brute-force algorithm for ACC^0 circuit satisfiability) into a circuit lower bound. The method: if you can solve the problem slightly faster than brute force, then the problem's complexity class cannot be computed by circuits of that type.

The encoding obstruction suggests a different but related strategy: instead of finding a faster algorithm and deriving a lower bound from it, **derive the lower bound directly from the structure of encoding execution**. The cost of encoding transformation is not a property of any particular algorithm — it is a property of what any algorithm must do when it manipulates encoded objects. If that structural cost is super-polynomial for NP-complete problems, the lower bound follows without needing an algorithmic starting point.

---

## Part 6: The Convergence Connection

### Convergence vs total divergence

The convergence conjecture (convergence-conjecture.md) asks: does the encoding distortion (the gap between obs_semantic and obs_code) converge or diverge as the encoding chain extends?

- **Weak convergence**: The distortion is bounded. The encoding trajectory and the semantic trajectory stay within a fixed distance. The system approximately bisimulates itself, and the approximation has a definite limit (conjectured: base e, connecting to the analytic model).

- **Total divergence**: The distortion grows without bound. The encoding trajectory and semantic trajectory separate indefinitely. Self-knowledge is structurally impossible even approximately.

### Implications for P vs NP

**If weak convergence**: The extensionalization chain for construction converges — the number of required extensionalization steps is bounded (perhaps polynomially). The encoding overhead is absorbed into a finite correction factor. This would be *consistent with* P = NP (the construction cost is polynomial after the convergence factor is applied).

**If total divergence**: The extensionalization chain for construction diverges — the number of required extensionalization steps grows without bound, and each step introduces new structure requiring further steps. This would be *consistent with* P != NP (the construction cost is super-polynomial because the chain never stabilizes).

The convergence conjecture does not directly resolve P vs NP. But it addresses the same structural question from the encoding side: does the intension/extension regress terminate (in a useful sense) or not? If it diverges, the search cost for construction is unbounded relative to verification, which is the structural content of P != NP.

---

## Part 7: What This Framework Does and Does Not Claim

### Does claim

1. **Computation is encoding execution.** Every computational step is an encoding transformation. This is not metaphorical — the tape IS the encoding, the transition function IS the rewriting rule.

2. **Encoding execution has structural costs.** The intension/extension duality means that extensionalization (unfolding, search, construction) is structurally more expensive than intensionalization (reading, verification, eigenvalue observation). This is a theorem, not a conjecture.

3. **The verification/construction asymmetry is algebraic.** Verification is intensional (local, no carry). Construction is extensional (non-local, requires carry, requires external state). This asymmetry is proved at the algebraic level in the encoding obstruction trilemma.

4. **The barrier results do not obviously block this approach.** The encoding obstruction examines the internal algebra of self-representation, which is not the kind of argument that relativization, natural proofs, or algebrization were designed to exclude.

### Does not claim

1. **P != NP.** The algebraic separation (linear vs super-linear) does not entail the complexity-theoretic separation (polynomial vs super-polynomial). The gap between the two thresholds is the open problem.

2. **The compounding hypothesis is proved.** The conjecture that the extensionalization chain for NP-complete problems is super-polynomial is precisely that — a conjecture. Proving it requires formalizing the chain for specific problems and establishing the super-polynomial bound.

3. **The convergence conjecture resolves P vs NP.** Even if total divergence is established, it would show that self-encoding systems cannot approximate their own dynamics — a statement about self-reference, not directly about SAT. The connection to specific NP-complete problems would still need to be established.

4. **This is a proof strategy.** This document identifies a structural framework within which P vs NP might be approached. It does not constitute a proof or a proof sketch. The distance from the algebraic results to the complexity-theoretic conclusion remains large.

### The honest assessment

The encoding obstruction proves that verification and construction have structurally different costs at the algebraic level. This is a genuine result — it explains *why* we should expect P != NP, grounded in the algebra of encoding execution rather than in the failure of known algorithms.

The path from this algebraic result to a proof of P != NP requires showing that the structural cost difference compounds super-polynomially for NP-complete problems. This is the compounding hypothesis, and it is the central open question that would need to be resolved.

The framework's value, independent of whether P != NP is proved through it, is that it identifies **encoding execution** as the fundamental object of study for computational complexity — not algorithms, not circuits, not Boolean functions, but the structural cost of transforming one encoding into another. If this perspective yields new lower bound techniques, the encoding obstruction will have contributed to the field regardless of the ultimate resolution.

---

## Part 8: Research Directions

### Immediate: formalize the extensionalization chain for SAT

Define, within the eigenvalue framework, what it means to "solve SAT" as a sequence of extensionalization steps. Map the eigenstates to formula components, define the encoding, and characterize the obs applications required. This would make the compounding hypothesis precise and testable.

### Medium-term: prove chain length lower bounds

For the formalized SAT extensionalization chain, prove lower bounds on the chain length. Start with specific restricted cases (2-SAT, 3-SAT on structured instances, k-SAT for varying k). Determine whether the chain length grows polynomially (as in 2-SAT, which is in P) or super-polynomially (as expected for 3-SAT). The transition between k=2 and k=3 would be the critical test case.

### Long-term: connect chain length to complexity classes

If chain length lower bounds can be established, connect them to standard complexity measures (time, circuit depth, space). Show that a super-polynomial extensionalization chain implies a super-polynomial time lower bound. This is the bridge from the algebraic framework to the complexity-theoretic conclusion.

### Parallel: resolve the convergence conjecture

Independent of the SAT-specific direction, resolve whether the encoding distortion converges or diverges. This addresses the structural question underlying P vs NP without requiring the problem-specific formalization. If total divergence is proved, it provides evidence (not proof) that the compounding hypothesis holds.

---

## Related

- [../encoding-obstruction.md](../encoding-obstruction.md) -- The core trilemma: eigenvalue arithmetic + self-encoding + coalgebra morphism
- [../addition-non-locality.md](../addition-non-locality.md) -- Carry propagation as the mechanism forcing external state
- [../computing-as-external-state.md](../computing-as-external-state.md) -- Computation = language + external state (derived, not stipulated)
- [../impossibility-hierarchy.md](../impossibility-hierarchy.md) -- Four levels: substitution -> tropical -> carry -> undecidability
- [../convergence-conjecture.md](../convergence-conjecture.md) -- Does the encoding distortion converge or diverge?
- [../self-representation.md](../self-representation.md) -- Godel encoding within the eigenvalue framework
