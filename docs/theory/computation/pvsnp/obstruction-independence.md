# P vs NP Independence via the Encoding Obstruction

## Date: 2026-04-13

## Summary

The encoding obstruction (proved universally in `Universal.lean`, `EvalRewrite.lean`) establishes: evaluation changes syntactic form while preserving semantics, and no injective encoding commutes with evaluation. This is the structural atom underlying incompleteness and the halting problem (proved in `Diagonal.lean`, `Halting.lean`).

This document argues that the same obstruction applies to ALL proof systems, constraining BOTH directions of P vs NP -- not just P != NP but also P = NP. If the argument completes, P vs NP is independent of any formal system whose verification requires arithmetic, which is all of them.

**Status:** Research program with identified steps. Not proved. The formalized chain ends at "the encoding obstruction holds universally" (proved) and "incompleteness follows from the obstruction" (proved). The extension to proof complexity lower bounds and P vs NP independence is the open frontier.

---

## Part 1: The Argument

### Step 1: The encoding obstruction is universal

For any term algebra `TermF C` parameterized over an arbitrary constant signature `C`, the Leibniz rewrite changes root constructors (`obs` -> `add`), and no injective encoding commutes with it. This is proved in `Universal.lean` and is universal over ALL choices of `C`.

PA's own evaluation rules are an instance: `times(a, succ(b))` rewrites to `plus(times(a,b), a)` (root: `times` -> `plus`), and `plus(a, succ(b))` rewrites to `succ(plus(a,b))` (root: `plus` -> `succ`). Proved in `EvalRewrite.lean`.

The obstruction depends only on the structural constructors. The constants are irrelevant.

### Step 2: The rewrite rules are the only variable

Across all term algebras, the encoding obstruction holds for the same reason: evaluation changes root constructors. Different systems have different constants and different specific evaluation rules, but the pattern is identical: a binary operation's evaluation introduces a different binary operation at the root.

The Leibniz rule (derivation on a product), PA's multiplication rule (recursive definition of times), and PA's addition rule (recursive definition of plus) are all instances of the same pattern. The obstruction is about EVALUATION ITSELF, not about any specific evaluation rule.

### Step 3: Proof systems require arithmetic

A proof system (Cook-Reckhow) is a polynomial-time computable relation R(proof, theorem). Verification must:

- **Parse the proof** (a sequence of formulas) -- requires string/term manipulation
- **Check each step is valid** (substitution, modus ponens, etc.) -- requires comparing sub-terms, counting positions
- **Confirm the conclusion matches the claimed theorem** -- requires term matching

Parsing, comparing, counting -- these are arithmetic operations. Any system that manipulates strings with two generators and concatenation interprets PA (the mutual interpretability result from formal language theory: string theories and number theories are equivalent up to interpretation). Proof verification IS string manipulation. So proof verification interprets PA.

This is not an analogy. A proof verifier literally computes primitive recursive functions on encoded formulas. Primitive recursion requires PA. Therefore the verifier's internal computation has evaluation rewrites that change root constructors.

### Step 4: PA has the encoding obstruction

PA's evaluation rewrites change root constructors:

| Rule | Root change | Proved in |
|------|-------------|-----------|
| `a * S(b) = a * b + a` | `times` -> `plus` | `EvalRewrite.lean` |
| `a + S(b) = S(a + b)` | `plus` -> `succ` | `EvalRewrite.lean` |

These are PA's OWN axioms, read as rewrite rules. No external derivation operator is imposed. The obstruction comes from arithmetic itself.

### Step 5: Therefore any proof system has the encoding obstruction

The chain:

```
Proof system verification
    requires string manipulation
    requires arithmetic (PA)
    has evaluation rewrites (times -> plus, plus -> succ)
    has the encoding obstruction (EvalRewriteWitness)
```

No injective encoding of verification states commutes with verification steps, for ANY proof system. The verification trajectory diverges syntactically while remaining semantically invariant.

---

## Part 2: Application to P != NP

### What a proof of P != NP requires

A proof of P != NP must show: for ALL polynomial-time algorithms A and ALL polynomials p, there exists an input phi such that A does not correctly solve SAT within p(|phi|) steps.

This requires the proof system T to:

1. **Encode arbitrary algorithms** as terms in T's language
2. **Track execution** of each algorithm on arbitrary inputs
3. **Prove the execution fails** (wrong answer or timeout) for some input

Step 2 is where the obstruction bites. Tracking execution requires encoding computation states and reasoning about how they evolve. The encoding obstruction says: the encoding of evolved states diverges from the evolution of encoded states. T cannot faithfully track what algorithms do through its encoding.

This is the second incompleteness theorem's cousin: T can't prove its own consistency because the proof would require T to fully model its own provability. Similarly, T can't prove P != NP because the proof would require T to fully model ALL computations, but T's encoding of computation doesn't commute with computation itself.

### The universal quantification problem

P != NP is a universal statement: "for ALL algorithms." Proving it requires the proof system to reason about arbitrary computations -- computations it has never seen, computations that may be adversarially constructed. This universal reasoning requires encoding-evaluation commutation: the proof must show that the ENCODING of any algorithm's execution has certain properties, which requires the encoding to faithfully represent the execution.

The encoding obstruction blocks this: the encoding representation necessarily diverges from the execution it represents. The proof system is always one substitution step behind.

---

## Part 3: Application to P = NP

### What a proof of P = NP requires

A proof of P = NP requires exhibiting an algorithm A and proving:

1. **Correctness:** for ALL inputs phi, A(phi) = SAT(phi)
2. **Efficiency:** for ALL inputs phi, A(phi) terminates within p(|phi|) steps

Both are universal statements over inputs.

### The algorithm must use arithmetic

Any non-trivial algorithm computes. Computing requires arithmetic -- the algorithm manipulates encoded data using operations that interpret PA (indexing, counting, comparing, branching). The algorithm's own execution has evaluation rewrites that change root constructors.

### Proving correctness requires tracking execution

To prove "for all phi, A(phi) = SAT(phi)," the proof system must:

1. Encode A's computation on an arbitrary input phi
2. Track the computation through to its output
3. Prove the output matches SAT(phi)

This tracking is subject to the encoding obstruction. The proof system's encoding of A's computation diverges from A's actual computation. The encoding of the computed states is not the computation of the encoded states.

### The abstraction question

We DO prove algorithms correct all the time -- sorting, primality testing, graph algorithms. These proofs use abstraction: loop invariants, induction, type systems. These techniques establish properties of computation without tracking every execution step. They work AROUND the obstruction by reasoning about PROPERTIES rather than TRAJECTORIES.

The critical question: can a hypothetical polynomial-time SAT algorithm's correctness be established through abstraction alone, without requiring encoding-evaluation commutation?

For algorithms solving problems in P (sorting, GCD, primality), abstraction suffices -- their correctness proofs use induction and invariants that don't require tracking every step. But a polynomial-time SAT algorithm would be solving an NP-complete problem, which might require a qualitatively different correctness proof.

**The conjecture:** NP-completeness forces any correctness proof of a hypothetical polynomial-time SAT algorithm to require encoding-evaluation tracking that the obstruction blocks. SAT's combinatorial structure (the interaction between clauses, the exponential space of assignments) cannot be abstracted away -- any correct proof must engage with the encoding of this structure, and that engagement triggers the obstruction.

---

## Part 4: The Independence Argument

### Both directions blocked

If the argument in Parts 2 and 3 completes:

- **P != NP is unprovable:** the proof would require universal quantification over all algorithms, tracking their execution through encoding. The obstruction blocks the tracking.

- **P = NP is unprovable:** the proof would require exhibiting an algorithm and proving it correct, which requires universal quantification over all inputs and tracking the algorithm's execution. The obstruction blocks the tracking.

Therefore: **P vs NP is independent** of any formal system whose verification requires arithmetic (which is all Cook-Reckhow proof systems).

### Comparison to known barriers

| Barrier | What it blocks | Mechanism |
|---------|---------------|-----------|
| Relativization (Baker-Gill-Solovay 1975) | Proofs that relativize | Oracles can make P = NP or P != NP |
| Natural proofs (Razborov-Rudich 1997) | Proofs that are "natural" | Pseudorandom functions defeat constructive largeness |
| Algebrization (Aaronson-Wigderson 2009) | Proofs that algebrize | Algebraic extensions preserve both outcomes |
| **Encoding obstruction (conjectured)** | **Proofs requiring encoding-evaluation commutation** | **Evaluation changes form; encoding can't track it** |

The encoding obstruction would be a NEW barrier, distinct from the existing three. Unlike the existing barriers (which show specific proof techniques fail), the obstruction would show that ANY proof requiring faithful encoding of computation fails -- because all proof systems have the obstruction.

The open question: does the encoding obstruction subsume the existing barriers, or is it a fourth independent barrier?

### The remaining gap

The argument has one unproved step: **does proving statements about NP-complete problems necessarily require encoding-evaluation commutation?**

- For universal statements about ALL algorithms (P != NP direction): plausible, since the proof must handle arbitrary computations
- For universal statements about ALL inputs to ONE algorithm (P = NP direction): plausible but less clear, since abstraction techniques can handle universal-over-inputs for P problems

The conjecture: NP-completeness is the PRECISE boundary where abstraction stops working and encoding-evaluation tracking becomes necessary. Problems in P admit abstract correctness proofs. NP-complete problems force the proof to engage with exponential combinatorial structure that triggers the obstruction.

If this conjecture is true, P vs NP is independent -- and the reason is the encoding obstruction: evaluation changes form, encoding can't track it, and this structural fact prevents any proof system from resolving the question.

---

## Part 5: The Research Program

### Proved (machine-checked, sorry-free)

| Result | File |
|--------|------|
| Universal encoding obstruction for all term algebras | `Universal.lean` |
| PA's evaluation rules create the obstruction | `EvalRewrite.lean` |
| Diagonal lemma from GodelSystem axioms | `Diagonal.lean` |
| Incompleteness from the obstruction | `Diagonal.lean` |
| Halting problem from the same pattern | `Halting.lean` |
| Unified EvalRewriteWitness captures all three | `EvalRewrite.lean` |

### Open (issues filed)

| Step | Issue | Status |
|------|-------|--------|
| Proof systems require arithmetic -> EvalRewriteWitness | #36 | Open |
| Encoding obstruction -> proof complexity lower bounds | #33 | Open |
| Root constructor change vs generic non-trivial semantics | #34 | Open |
| Instantiate GodelSystem for PA | #35 | Open |

### The path

```
PROVED:  Encoding obstruction (universal)
         Incompleteness + halting problem (from obstruction)
              |
OPEN #36:    Proof systems require arithmetic -> EvalRewriteWitness
              |
OPEN #33:    Obstruction -> proof complexity lower bounds
              |
CONJECTURED: NP-completeness forces encoding-evaluation tracking
              |
              v
         P vs NP independent
```

Each step is well-defined. The gap between "proved" and "conjectured" is where the Rotational Calculus (SAT formalized as term rewriting, resolution as composition, width trajectory analysis) provides the tools. If the trajectory analysis shows that SAT's structure forces the kind of encoding-evaluation tracking that the obstruction blocks, the argument completes.

---

## Part 6: Connection to the Rotational Calculus

### Resolution IS an EvalRewriteWitness

Resolution in the Rotational Calculus:

- **Form changes:** `resolve(C1, C2, x)` takes two clause-terms and produces a new clause-term with different structure (different literals, different width)
- **Semantics preserved:** satisfiability is invariant under resolution
- **Root constructor changes:** a pair of clauses (pair-rooted term) becomes a single clause or ground (different root structure)

This is exactly the EvalRewriteWitness pattern. The encoding obstruction applies.

### Width trajectory as obstruction manifestation

The Rotational Calculus tracks width trajectories of resolution proofs:

- **PHP:** width narrows (3 -> 2 -> 1 then cascade) -- structured conflicts, predictable trajectory
- **Random UNSAT:** width flat -- unstructured conflicts, trajectory doesn't converge
- **Modular:** width narrows at cluster boundaries -- intermediate structure

These trajectories are manifestations of the encoding obstruction: the verification state (clause set) changes form at each resolution step, and the width measures HOW MUCH the form changes. Wide clauses = large form change = more encoding divergence.

Haken's exponential lower bound for PHP says: resolution proofs must pass through wide clauses (the "bottleneck" argument). In the obstruction framing: the proof trajectory must visit states with large encoding divergence, and there are exponentially many such states.

### The concrete target

Show that the encoding obstruction, applied to resolution proof systems via the EvalRewriteWitness, implies Haken's lower bound (or an analogous bound). This would demonstrate that the obstruction has proof-complexity teeth -- the same structural fact that causes incompleteness also causes exponential resolution proofs.

From there, the question is whether the obstruction extends to stronger proof systems (Frege, extended Frege, etc.). If it extends universally (as the "proof systems require arithmetic" argument suggests), the independence result follows.

---

## Related

- [encoding-complexity.md](encoding-complexity.md) -- earlier framing of P vs NP as encoding execution
- [barrier-analysis.md](barrier-analysis.md) -- analysis of existing barriers
- [../encoding-obstruction.md](../encoding-obstruction.md) -- the encoding obstruction theory
- [../self-representation.md](../self-representation.md) -- self-representation and incompleteness
