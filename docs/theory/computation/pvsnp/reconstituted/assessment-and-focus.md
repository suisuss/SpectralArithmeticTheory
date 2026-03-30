# Assessment of the Full Computation Document Stack and Research Focus

## Date: 2026-03-24

## Summary

An external assessment of the entire computation theory body of work — the encoding obstruction, addition non-locality, impossibility hierarchy, barrier analysis, normalization depth, Leibniz uniqueness, convergence analysis, SAT encoding, and the reconstituted encoding-generator-coupling direction. The assessment identifies what is genuinely strong, where the arguments have gaps, and which research directions are most likely to produce results.

**Verdict:** The Lean-verified core is real and nontrivial. The barrier analysis is the most careful part. The VarSharing finding undermines the main algebraic narrative more than the existing documents acknowledge. The generator fixed-point argument from the reconstituted direction is the most novel and promising path forward precisely because it operates at the assignment-space level where VarSharing says the hardness actually lives.

---

## Part 1: What Is Genuinely Strong

### The Lean-verified encoding obstruction

The trilemma — eigenvalue arithmetic + self-encoding + coalgebra morphism are jointly unsatisfiable — is a genuine theorem with sorry-free proofs. The key results:

- `no_coalgebra_morphism`: for ANY injective encoding and ANY compound term, the extensionalized form has a different code from the original
- `substitution_chain_distinct`: three successive passes produce three distinct codes — no fixed point
- `semantic_invariance_general`: meaning is preserved at every step — the divergence is syntactic, not semantic

These are real theorems, not conjectures. They establish that self-encoding systems have a structural gap between syntax and semantics that no encoding can close.

### The three blocked exits

The impossibility hierarchy's analysis of escape routes is tight:

| Exit | Sacrifices | Why fatal for self-encoding |
|------|-----------|---------------------------|
| Redundant representations | Uniqueness | Godel encoding requires bijection; carry reappears at equality testing |
| Residue number systems | Ordering | Bounded quantification, prime factorization, Godel decoding all require positional access |
| Tropical algebra | Cancellation | No subtraction, no division, no factorization, eigenvalue orbit collapses |

Every exit reintroduces carry or destroys self-encoding. This is well-argued and the vertical integration across the impossibility hierarchy (substitution -> carry -> undecidability) is the best part of the theoretical work.

### The normalization depth correction

The original conjecture was exponential normalization depth (>= 2^d passes). Lean formalization disproved this: normalization depth is exactly 2 (constant) for nestedObsCompose, with exponential per-pass work instead. The entire document stack was updated accordingly.

This correction is a mark of intellectual honesty and actually produces a more interesting structural finding: the exponential cost lives in per-pass term size, not pass count. This precisely identifies WHERE complexity enters the framework — the Leibniz branching factor, not the iteration count.

### The barrier analysis

The most careful part of the P vs NP direction:

- **Non-relativizing:** Definitive. The obstruction looks inside compose structure via the Leibniz rule. Oracle terms are atomic — Leibniz cannot fire on them. The proof technique structurally depends on internal composition, which oracle access prevents.

- **Non-natural:** Sound. The obstruction does not define a combinatorial property of Boolean function truth tables. It operates on algebraic structure of self-encoding systems. The property is problem-specific (not large) and not tested on truth tables (not constructive in the Razborov-Rudich sense).

- **Non-algebrizing:** The most subtle and best-analyzed. The key distinction is correct: the obstruction uses arithmetic at the meta-level (encoding growth rates, carry propagation) rather than the object-level (polynomial evaluation of Boolean functions at non-Boolean field points). The position-existence argument — that Boolean and arithmetic are the same layer in self-encoding systems, not separate layers connected by lifting — is the strongest part of the algebrization analysis.

---

## Part 2: Where the Arguments Have Gaps

### Gap 1: The bridge problem is understated

Every document acknowledges "the gap from algebraic result to complexity separation remains large." But the documents keep adding structural analysis without narrowing this gap.

The trilemma proves verification is structurally cheaper than construction *in the eigenvalue framework*. But SAT solvers don't operate in the eigenvalue framework. The connection between Leibniz normalization cost and Turing machine time is assumed, not proved.

Step 4 in leibniz-uniqueness.md ("search term lower bound — show that deepRewrite's cost lower bound applies to ALL normalization strategies") is where the entire program lives or dies. It is marked "open, hard" with no concrete attack strategy.

**The risk:** The encoding obstruction may be a correct structural fact about self-encoding systems that has no implication for computational complexity. The algebraic level and the complexity level may be disconnected — true statements at each level, with no logical path between them. This is explicitly acknowledged in barrier-analysis.md (Part 5, Risk 3) but not given enough weight elsewhere.

### Gap 2: The SAT encoding doesn't preserve semantics

The SAT encoding maps literals to f_0/z, clauses to compose chains, formulas to obs-wrapped compositions. The documents acknowledge: "eval does not correspond to Boolean satisfaction."

This is a critical gap. If the encoding doesn't preserve the problem's semantic structure, then lower bounds on normalization of the encoding don't transfer to lower bounds on solving the problem. The relationship is:

- "The encoding is expensive to normalize" — proved for specific term families
- "The problem is hard to solve" — the claim
- The logical gap: normalizing the encoding is not the same operation as solving the problem

A lower bound on Leibniz normalization depth for SAT-structured terms would be a lower bound on a specific algebraic operation, not on SAT itself. To connect them, you'd need to show that any SAT solver must, at some point, perform an operation equivalent to Leibniz normalization of the encoding — and this equivalence is not established.

### Gap 3: VarSharing undermines the algebraic narrative

VarSharing.lean proves: **under any fixed assignment, independent and sharing formulas with the same shape produce identical normalization costs.** Variable sharing only manifests across the assignment space.

This is a significant finding that undermines the main argument more than the documents acknowledge:

1. The entire Leibniz-expansion argument is about normalization of a single term (a fixed assignment produces a fixed term)
2. If the structural hardness lives in the assignment space (a combinatorial object) rather than in any single term's normalization (an algebraic object), then the encoding obstruction framework is addressing the wrong level
3. The hardness would be combinatorial (how many assignments must be explored), not algebraic (how expensive is each normalization)
4. The framework's algebraic tools — Leibniz branching, carry propagation, encoding obstruction — don't reach the combinatorial level

The documents note this ("The sharing effect is a combinatorial property of the assignment space, not a property of any single term") but don't follow the implication to its conclusion: the algebraic normalization framework may not be the right tool for the P vs NP question, because the relevant hardness is combinatorial.

### Gap 4: "Computation = language + external state" oversells

The carry propagation argument shows that *addition* requires state external to the encoding. But the claim "computation is language plus external state, and the external state is algebraically necessary because of carry" oversells in two ways:

1. Carry is not the *only* reason computation needs state. Control flow, memory management, IO, and context switching all require state for reasons unrelated to carry. The claim is about *one* source of external state necessity, not the *unique* source.

2. The claim that Turing's tape is "necessary because of carry" conflates two different roles of the tape: (a) storage for the encoding (which is about representation, not carry) and (b) workspace for intermediate computation (which may involve carry but also involves pattern matching, copying, and other operations). The tape serves both roles, and only (b) is related to carry.

The core insight — that the Leibniz rule forces addition into the dynamics of observation, and addition requires non-local state — is genuine. The extrapolation to "this is why computation requires external state" goes further than the argument supports.

---

## Part 3: How the Reconstituted Direction Connects

### What the encoding-generator-coupling adds

The reconstituted document captures insights not present in the existing body of work:

1. **The coupling as diagonal structure.** The existing documents treat the encoding obstruction and incompleteness as analogous. The reconstituted framing goes further: the coupling between encoding complexity and search space complexity IS a diagonal structure isomorphic to incompleteness. The proof and the object of the proof are entangled — the same structure that prevents the Godel sentence from being resolved prevents the encoding-search complexity relationship from being proved internally.

2. **The generator argument.** No existing document contains this argument. The claim: any encoding scheme for an NP search space must implicitly contain a generator (a function that navigates the space), and the generator creates a recursive dependency — it must be as complex as the space it navigates. This is genuinely new.

3. **The atom observation.** The connection between f_1 (fixed point of obs), NAND (universal gate), and Y combinator (fixed-point combinator) as instances of "self-application produces universality" is not in the existing documents. The identification of the confluence measure mu as a literal complexity measure (distance from ground state) is implicit in the confluence document but never stated in these terms.

### How the directions map to existing work

| Direction | Existing work | Gap |
|-----------|--------------|-----|
| 5 (Leibniz <-> NP-verification isomorphism) | Leibniz rule is forced; certificates are pruning licenses | No formal functor constructed; the parallel is structural analogy, not a theorem |
| 3 (Generator fixed-point argument) | **No existing work — genuinely new** | Needs formalization from scratch |
| 2 (Encoding complexity lower bound) | Encoding obstruction trilemma (proved) | Only proves linear vs super-linear, not polynomial vs super-polynomial |
| 4 (New formal language) | Entire framework is an attempt at this | Framework operates at the algebraic level; VarSharing shows hardness is at the combinatorial level |
| 1 (Universal impossibility / independence) | Coupling argument from encoding-generator-coupling.md | Pure conjecture, no formalization path visible |

---

## Part 4: What to Pursue Next

### Priority 1: Generator fixed-point argument (Direction 3)

**Why this is most promising:**

The generator argument is the most novel contribution and is NOT pre-empted by the VarSharing finding. The argument operates at the *assignment-space* level — exactly where VarSharing says the hardness actually lives:

- The generator must navigate the space of assignments (combinatorial, not algebraic)
- The encoding of the generator must be as complex as the space (information-theoretic, not algebraic)
- The recursive dependency (generator needs the result to produce the result) is a fixed-point problem

This sidesteps the main gap in the existing work (algebraic normalization cost doesn't connect to combinatorial search cost) by working directly at the combinatorial level.

**Concrete next steps:**

1. Formalize what "a generator for an NP search space" means. Candidate: a function G: Instance -> Code such that decode(G(x)) is a valid witness for x (when one exists).

2. Formalize what "the generator's complexity" means. Candidate: the Kolmogorov complexity of G, or the circuit complexity of G, or the description length of G in some fixed encoding.

3. Prove (or find a counterexample for): any polynomial-size generator G for SAT must implicitly encode the solution — the description of G must contain at least as much information as the satisfying assignment it produces.

4. If (3) holds, formalize the recursion: G needs the solution to compress below exponential size, but producing the solution is what G is for. Show the only fixed point of this recursion is the trivial one (brute enumeration).

**Risk:** Kolmogorov complexity is uncomputable, so step (2) may need a computable proxy. Circuit complexity would work but faces its own lower bound barriers.

### Priority 2: Leibniz-verification isomorphism (Direction 5)

**Why this is worth pursuing:**

The structural parallel between Leibniz decomposition and NP verification is the most concrete algebraic claim. If formalizable as a functor, it would give algebraic content to the P vs NP question.

**Blocker:** The SAT encoding doesn't preserve semantics. Before constructing an isomorphism, the encoding needs to be fixed so that Leibniz normalization of the encoded formula corresponds to checking/finding satisfying assignments.

**Concrete next steps:**

1. Redesign the SAT encoding so that eval of the encoded formula under a substitution (assignment) equals the Boolean satisfaction value. This may require using the Boolean subalgebra {f_0, f_1} more carefully.

2. Prove that Leibniz normalization of the redesigned encoding, with a certificate (fixed assignment), collapses to polynomial work.

3. Prove that Leibniz normalization without a certificate requires exponential work (or identify where this fails).

4. If (2) and (3) hold, construct the functor: a category of Leibniz decompositions -> a category of NP verification problems, preserving the cost structure.

### Priority 3: Coupling/independence argument (Direction 1)

**Why to keep this as a north star:**

The argument that P vs NP may be independent of PA-strong systems because the proof requires resolving a self-referential coupling is the most intellectually ambitious direction. It would explain *why* the problem has resisted solution for 50+ years.

**Why not to formalize it yet:**

- No known formalization technique for proving independence of complexity-theoretic statements from PA or ZFC
- The structural analogy ("this looks like incompleteness") is not a proof that it IS incompleteness
- The barrier results could equally be explained by "we haven't found the right technique yet" rather than "no technique exists"

**What would change this assessment:** If the generator fixed-point argument (Direction 3) produces a formal statement that demonstrably cannot be proved or disproved in PA, that would be concrete evidence for independence. Without such a statement, the independence conjecture remains philosophical.

---

## Part 5: The Honest Bottom Line

### What the framework achieves

The spectral arithmetic framework, applied to computation, achieves:

1. **A genuine structural explanation for WHY verification is cheaper than construction.** Verification is intensional (eigenvalue read, local). Construction is extensional (Leibniz unfolding, introduces addition, non-local). This asymmetry is proved, not conjectured.

2. **A proof that the verification/construction gap is intrinsic to self-encoding systems.** No encoding, no alternative observation operator, no change of number system eliminates the gap. The exits are blocked.

3. **A barrier analysis showing the approach is not pre-emptively defeated.** The encoding obstruction is non-relativizing, plausibly non-natural, and plausibly non-algebrizing. This is necessary but not sufficient.

4. **Machine-verified theorems.** The core results are Lean-verified with zero sorry. This is stronger than any hand-waved argument.

### What the framework does not achieve

1. **A proof of P != NP.** The algebraic separation (linear vs super-linear) does not entail the complexity-theoretic separation (polynomial vs super-polynomial).

2. **A concrete bridge from algebraic results to complexity classes.** The connection between Leibniz normalization cost and Turing machine time is not established.

3. **An explanation of hardness at the right level.** VarSharing shows the relevant hardness is combinatorial (across the assignment space), not algebraic (within a single normalization). The framework's algebraic tools don't reach the combinatorial level.

### What the reconstituted direction adds

The generator fixed-point argument addresses gap (3) directly by operating at the combinatorial level. If formalized, it would be the first result in the framework that engages with the hardness where it actually lives — in the structure of the search space, not in the cost of normalizing a single term.

The coupling/independence conjecture, if correct, would explain why gap (2) is permanent — not because the bridge is hard to build, but because it provably cannot exist within systems that can represent their own computation.

---

## Related

- [encoding-generator-coupling.md](encoding-generator-coupling.md) -- The reconstituted research directions
- [../encoding-complexity.md](../encoding-complexity.md) -- P vs NP as encoding execution problem
- [../barrier-analysis.md](../barrier-analysis.md) -- Barrier analysis
- [../normalization-depth.md](../normalization-depth.md) -- Normalization depth and the constant-depth correction
- [../leibniz-uniqueness.md](../leibniz-uniqueness.md) -- Leibniz is forced; certificates as pruning
- [../../encoding-obstruction.md](../../encoding-obstruction.md) -- The core trilemma
- [../../addition-non-locality.md](../../addition-non-locality.md) -- Carry propagation forces external state
- [../../computing-as-external-state.md](../../computing-as-external-state.md) -- Computation = language + external state
- [../../impossibility-hierarchy.md](../../impossibility-hierarchy.md) -- Four levels of impossibility
- [../../confluence.md](../../confluence.md) -- Termination and confluence
