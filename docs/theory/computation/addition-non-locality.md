# Addition Non-Locality: Why Self-Encoding Systems With Addition Require External State

## Date: 2026-02-20

## Summary

The encoding obstruction trilemma (encoding-obstruction.md) and its refinement (information-domain.md) localize the impossibility to **⊕** — the additive operation in the Leibniz rule. This document argues that the obstruction has a deeper root: **carry propagation in addition is non-local in any unique positional encoding**, and this non-locality forces any self-encoding, self-executing system with addition to maintain external state (registers, accumulators) for normalization.

The claim, stated precisely: **no mathematical system that self-encodes and self-executes can perform addition without intermediate normalization state, provided the encoding is unique (non-redundant) and positional.** This is because unique positional encodings require carry propagation for addition, carry propagation is non-local (output at position k depends on all inputs at positions 0 through k), and non-local operations cannot be absorbed into a local (position-independent) encoding.

**Novelty assessment:** The specific framing — "addition forces registers as a mathematical necessity for self-encoding systems" — does not appear in the literature. The individual components (carry non-locality, self-encoding limitations, necessity of state for algorithms) are well-established. The synthesis is new, but the claim requires careful restriction to avoid known counterexamples (redundant number systems, residue number systems).

---

## Part 1: Carry Propagation Is Non-Local

### The basic fact

In any standard positional number system (base b), adding two numbers requires carry propagation. A carry at position 0 can propagate to position n-1:

```
Binary:   0 1 1 1 1 1
        + 0 0 0 0 0 1
        ─────────────
          1 0 0 0 0 0
```

The output bit at position 5 depends on the carry chain from position 0 through positions 1, 2, 3, 4. The output at position k depends on ALL inputs at positions 0 through k.

### Contrast with other operations

| Operation | Output at position k depends on | Locality |
|---|---|---|
| Bitwise AND/OR/XOR | Inputs at position k only | Fully local |
| Bit shift / rotation | Input at position k ± c | Local (fixed offset) |
| Multiplication (single digit) | Input at position k only | Fully local |
| **Addition** | **Inputs at ALL positions 0..k** | **Non-local** |

Addition is the unique basic arithmetic operation where output at one position depends on inputs at ALL lower positions. This is intrinsic — it's not an implementation choice.

### Circuit complexity formalization

The non-locality is captured by circuit depth lower bounds:

- Bitwise operations: depth O(1) — constant depth, fully parallel
- Addition (bounded fan-in): depth O(log n) — carry-lookahead reduces sequential carry to parallel prefix, but cannot eliminate the dependency
- Addition (unbounded fan-in): depth O(1) — in AC⁰, but requires unbounded fan-in gates, which are not physically realizable at unit cost

Carry-lookahead (Weinberger & Smith, 1958) achieves O(log n) depth by parallelizing the carry computation. But it does NOT eliminate non-locality — it computes all carries simultaneously by broadcasting information from all lower positions. The information flow from position 0 to position n-1 is irreducible; only the sequential bottleneck is removed.

---

## Part 2: The Self-Encoding Constraint

### What "self-encoding and self-executing" means

A system is **self-encoding** if its states serve as codes for its own terms (Gödel encoding: eigenstates ARE Gödel numbers of terms). A system is **self-executing** if it can perform computation on those codes using its own operations (the Computes predicate from self-representation.md operates on eigenstates using compose, ⊕, obs).

In a self-encoding, self-executing system:
- The **encoding** maps terms to numbers (positional representation)
- The **execution** performs arithmetic on those numbers (including addition, via ⊕)
- The **encoding IS the data being computed on** — the representation and the computation share the same number system

### The reflexive constraint

This reflexivity creates a unique situation: the encoding must be compatible with the arithmetic it encodes. In a non-self-encoding system, the encoding and the computation can use different representations (e.g., encode in binary, compute in floating-point). In a self-encoding system, they must be the same.

This means: whatever positional representation the encoding uses, addition must operate on THAT SAME representation. The carry non-locality of addition becomes a property of the encoding itself, not just of the computation.

---

## Part 3: Why Addition Forces External State

### The argument

1. **Self-encoding requires a unique positional representation.** Gödel encoding requires injectivity (different terms get different codes) and decodability (given a code, recover the term). This requires a unique (non-redundant) representation — each number has exactly one encoding.

2. **In any unique positional representation, addition requires carry propagation.** This is the circuit complexity result: carry at position k depends on all inputs at positions 0..k. Non-locality is inherent.

3. **The Leibniz rule introduces addition into the observation dynamics.** obs(compose(a, b)) = compose(obs(a), b) ⊕ compose(a, obs(b)). The observation of a composed state produces two terms that must be ADDED.

4. **Addition on encoded states requires non-local normalization.** The two summands exist as encoded bit patterns. Their sum is a DIFFERENT bit pattern requiring carry propagation across all positions. The result must be materialized as a new, normalized code before it can serve as input to further operations.

5. **This normalization is external to the encoding.** The encoding decomposes information into independent positional layers. Carry propagation crosses layers. The normalization step (computing the carry chain and producing the sum) cannot be represented as a layer-local operation on the encoding. It requires state that tracks the carry across positions.

**Conclusion:** Any self-encoding, self-executing system with addition must maintain normalization state (a register, accumulator, or carry chain) external to the encoding. The encoding can represent the INPUTS to addition and the OUTPUT of addition, but not the PROCESS of addition — because the process is non-local while the encoding is positional.

### What "external state" means precisely

The external state is: **a mechanism that receives two encoded values, performs carry propagation across all bit positions, and produces a normalized encoded result.**

This is exactly what a hardware register + ALU does:
1. Load operand A from memory (encoded)
2. Load operand B from memory (encoded)
3. Compute A + B with carry chain (non-local process)
4. Store result in register (newly encoded, normalized)

The register is not an engineering convenience — it is the mathematically necessary buffer between the positional encoding and the non-local addition process.

---

## Part 4: Counterexamples and Restrictions

### Redundant number systems

**Counterexample:** Signed-digit representations (Avizienis, 1961) achieve carry-free addition in O(1) time per digit. Each output digit depends only on adjacent input positions — addition becomes local.

The trade-off: the representation is **non-unique**. The number 5 might be represented as (0,1,0,1) or (0,1,1,-1) or other combinations. Multiple encodings map to the same number.

**Why this doesn't defeat the claim:** Self-encoding requires UNIQUE representation (injectivity + decodability). If multiple encodings represent the same number, the Gödel encoding becomes ambiguous — different codes could represent the same term, breaking the one-to-one correspondence. The syntactic predicates (WellFormed, IsAxiom, ValidStep) require deterministic decoding: given a code, there must be exactly one term it represents.

**Restriction needed:** The claim must be stated for **non-redundant (unique) positional encodings**. Redundant representations trade uniqueness for carry locality — but uniqueness is exactly what self-encoding requires.

### Residue number systems (RNS)

**Counterexample:** RNS represents a number as its residues modulo several coprime moduli: n → (n mod m₁, n mod m₂, ..., n mod mₖ). Addition, subtraction, and multiplication are per-component — fully local, no carry.

The trade-off: **comparison and ordering are lost**. Given RNS representations, you cannot directly determine which number is larger without converting back to positional form (an expensive operation). Division is also extremely difficult.

**Why this doesn't defeat the claim:** Self-encoding requires more than addition. The Gödel encoding requires:
- Prime factorization (needs ordering and division)
- Bounded quantification (needs comparison: "for all n < k")
- The primitive recursive predicates (needs ordering for bounded search)

Without comparison and ordering, the syntactic predicates cannot be defined. RNS eliminates carry at the cost of ordering, and ordering is essential for self-encoding.

**Restriction needed:** The claim must specify that the encoding supports ordering and comparison — which forces a positional representation, which forces carry non-locality for addition.

### Hybrid representations

One could imagine a hybrid: store numbers in RNS for addition, convert to positional for comparison. The conversion step is expensive (O(n log n) for CRT reconstruction) and requires... carry propagation. The external state reappears at the conversion boundary.

This suggests the claim is robust: you can defer the carry propagation to later, but you cannot eliminate it. The normalization state is needed at some point before the result can be compared, ordered, or used for any operation requiring positional structure.

---

## Part 5: The Precise Claim

### Statement

**Theorem (conjectured).** Let S be a mathematical system that is:
1. **Self-encoding:** States serve as Gödel codes for terms (injective, decodable)
2. **Self-executing:** Computation on codes uses the system's own operations
3. **Additive:** The system includes a cancellative, characteristic-zero addition operation ⊕
4. **Ordered:** The encoding supports comparison and bounded quantification

Then the evaluation of ⊕ on encoded states cannot be represented as a position-local operation on the encoding. Any execution model for S requires normalization state external to the encoding for performing ⊕.

### Conditions explained

- **Self-encoding** (1) forces unique positional representation (for injectivity + decodability)
- **Self-executing** (2) forces the encoding and the arithmetic to share the same representation
- **Additive** (3) introduces carry propagation (non-local in unique positional systems)
- **Ordered** (4) eliminates residue number systems (which sacrifice ordering for locality)

Conditions (1)-(4) together force: the system must perform addition on its own positional encoding, carry propagation is non-local, and no position-local encoding transformation can absorb the carry chain.

### Relationship to the trilemma

This theorem, if proved, would be the **foundation** under the trilemma:

| Level | Result | What it says |
|---|---|---|
| **Foundation** | Addition non-locality theorem (this document) | ⊕ on self-encoding requires external state |
| **Trilemma** | Encoding obstruction (encoding-obstruction.md) | Eigenvalue arithmetic + self-encoding + coalgebra morphism are jointly unsatisfiable |
| **Refinement** | Information domain analysis (information-domain.md) | The obstruction is specifically ⊕ in the Leibniz rule |

The foundation explains WHY the trilemma holds: the coalgebra morphism requires encoding to preserve dynamics, but ⊕ dynamics (carry propagation) are non-local and cannot be preserved by any position-local encoding.

---

## Part 6: The Register as Mathematical Primitive

### What the theorem tells us about computation

If the claim is correct, then the **register** (or accumulator, or carry chain, or normalization buffer) is not an engineering artifact — it is a mathematical necessity. Any computational model that includes addition and self-encoding must have a mechanism external to the encoding for performing addition normalization.

This explains:

| Architectural feature | Mathematical necessity |
|---|---|
| CPU registers / ALU | Carry chain for addition cannot be absorbed into memory encoding |
| Von Neumann bottleneck | Data must flow between memory (encoding) and ALU (normalization) |
| Accumulator architectures | The accumulator IS the addition normalizer |
| Memory hierarchy | Encoding (storage) and computation (normalization) use different structures |
| Carry-lookahead / prefix adders | Optimizations of the irreducible carry chain, not elimination of it |

The von Neumann bottleneck — the separation between memory and processor — is not just an engineering choice that better architectures could eliminate. It is a mathematical consequence of self-encoding systems with addition: the encoding (memory) is positional/local, addition (processor) is non-local, and the two cannot be unified.

### The register in the eval-quote diagram

The eval-quote diagram from encoding-obstruction.md:

```
        eval
Terms --------→ State
  |                |
  | ⌜·⌝            | obs_semantic
  |                |
  ↓                ↓
State --------→ State
     obs_code
```

The diagram doesn't commute because the bottom-left path (encode then rewrite) must perform addition on codes, which requires carry propagation, which requires a register. The register is the "external state" that the encoding cannot absorb. The diagram would need to be expanded:

```
        eval
Terms --------→ State
  |                |
  | ⌜·⌝            | obs_semantic
  |                |
  ↓                ↓
State ──→ Register ──→ State
  encode    normalize    re-encode
          (carry chain)
```

The register is the intermediate step where addition's non-locality is resolved. It breaks the direct encoding→encoding path, which is why the coalgebra morphism fails.

### Implications for the bisimulation conjecture

The bisimulation between obs_semantic and obs_code fails because obs_code must pass through a normalization step (the register) that obs_semantic doesn't need. The semantic observation scales by eigenvalue — a single multiplicative step, fully local. The syntactic observation rewrites and re-encodes — but the Leibniz rule's ⊕ forces an addition, which requires a carry chain, which is non-local.

The non-locality of addition is the specific mechanism by which the encoding distorts the dynamics. It's not just that the encoding is "non-linear" (the growth-rate argument) or that "⊕ becomes max in the info domain" (the tropical argument). It's that **addition crosses bit layers, and crossing bit layers is exactly what positional encoding cannot represent locally.**

---

## Part 7: Generalization Beyond Eigenvalue Systems

### The universal claim

If the argument holds, it applies to **any** self-encoding system with addition — not just eigenvalue systems, not just this framework. Any system where:

- States encode terms (Gödel encoding or equivalent)
- Computation operates on those states (self-execution)
- Addition exists as a fundamental operation

...must have external normalization state. This includes:

- **PA itself:** Gödel's original encoding + arithmetic on codes requires carry propagation
- **ZF:** Set-theoretic arithmetic on Gödel numbers has the same structure
- **Type theories:** Any type theory with natural numbers and self-representation
- **Any PA-strength system:** By equiconsistency, all face the same constraint

The register is universal. Every sufficiently powerful self-encoding system needs one.

### What this means for foundations

If correct, this establishes a structural fact about mathematical foundations:

> **No foundation that includes addition can be fully "self-contained" without an external normalization mechanism.** The encoding of terms (syntax) and the execution of arithmetic (semantics) necessarily use different structures — positional layers vs. carry chains — and the interface between them (the register) is an irreducible primitive.

This is a precise, algebraic version of the philosophical claim that "syntax and semantics are distinct." They're distinct because syntax is positional (layer-local) and semantics includes addition (layer-crossing), and these cannot be unified.

---

## Part 8: Connection to Existing Results

### Closest existing work

| Work | Relevance | Difference from this claim |
|---|---|---|
| **Gurevich (2000), Sequential ASM Theorem** | Proves any sequential algorithm is equivalent to an abstract state machine — algorithms NEED state | General: all algorithms need state. This claim: addition SPECIFICALLY forces state because of carry non-locality |
| **Avizienis (1961), redundant number systems** | Carry-free addition via non-unique representations | Counterexample to the unrestricted claim; addressed by requiring unique (self-encoding-compatible) representation |
| **Hastad (1987), circuit depth lower bounds** | Addition requires Ω(log n) depth with bounded fan-in | Formalizes non-locality but doesn't frame it as encoding-vs-execution impossibility |
| **Backus (1978), von Neumann bottleneck** | The memory-processor separation as intellectual limitation | Framed as engineering criticism, not mathematical necessity |
| **Girard (1987), linear logic** | Additive/multiplicative distinction mirrors carry-local/carry-crossing operations | Conceptual parallel but no theorem connecting to self-encoding |
| **Landauer (1961), irreversibility** | Addition destroys information, requiring energy dissipation | Thermodynamic framing; related but orthogonal to encoding framing |

### What is new

The specific synthesis: **carry non-locality + self-encoding uniqueness + Leibniz rule = external state is mathematically necessary.** Each piece is known. The assembly — framing the register as the mathematical consequence of addition's non-locality in self-encoding systems — does not appear in the literature.

### What remains to prove

1. **Formalize "position-local encoding transformation."** Define precisely what it means for an encoding to absorb an operation locally vs. requiring external state.

2. **Prove carry non-locality is irreducible for unique encodings.** Show that no unique positional encoding admits carry-free addition. (This is widely believed and likely follows from information-theoretic arguments, but needs a clean proof.)

3. **Prove self-encoding requires unique positional encoding.** Show that injectivity + decodability + ordering force a positional system with unique representations. (Needs to rule out non-standard representations that might be unique but non-positional.)

4. **Connect to Gurevich's ASM framework.** Specialize the ASM theorem: show that the state transitions in any ASM computing addition on self-encoded terms must include carry normalization as a primitive step. This would be the formal version of "registers are mathematically necessary."

---

## Part 9: The Deeper Reading

### Why addition is special

Addition is the operation that **creates information interaction across layers**. All other basic operations (bitwise, shift, single-digit multiplication) keep each layer independent. Addition is the unique operation where the result at one layer depends on the process at all lower layers.

In the eigenvalue framework:
- compose (multiplication of eigenstates) is local — eigenvalue indices add, bit layers don't interact
- obs (derivative / layer read) is local — reads one layer at a time
- **⊕ (addition of eigenstates) is non-local** — carry propagation crosses all layers

The Leibniz rule forces ⊕ into the dynamics of obs. Without Leibniz, observation would be purely local, and the encoding could preserve dynamics. With Leibniz, observation produces sums, sums require carry propagation, and the encoding breaks.

The Leibniz rule is the **product rule for differentiation**. It says: observing a composed system requires summing the observations of the parts. The sum is the non-local step. The product rule is the structural reason that differentiation of products requires addition, and addition requires external state.

### The position-velocity-acceleration connection

The derivative chain (position → velocity → acceleration) is the chain of information layers. Each derivative peels off one layer. The Leibniz rule says: differentiating a product requires ADDING the cross-terms. This addition is the moment where independent information layers (the two factors) must interact, and that interaction requires carry propagation.

In physical terms: if you have two objects with known positions and velocities, the position of their composite requires adding their velocities. That addition — combining independent information channels into a single normalized value — is the irreducible non-local step. A register (or physical accumulator) is needed to perform it.

The register is the physical manifestation of the mathematical fact that **addition crosses information boundaries.**

---

## Related

- [impossibility-hierarchy.md](impossibility-hierarchy.md) — The unified view: addition → state → halting → incompleteness as one impossibility
- [encoding-obstruction.md](encoding-obstruction.md) — The trilemma: eigenvalue arithmetic + self-encoding + coalgebra morphism
- [information-domain.md](information-domain.md) — The information domain analysis: ⊕ as the refined obstruction
- [self-representation.md](self-representation.md) — Gödel encoding and the self-representation chain
- [confluence.md](confluence.md) — The oriented rewriting system

## References

- Avizienis, A. (1961). *Signed-digit number representations for fast parallel arithmetic.* IRE Transactions on Electronic Computers, EC-10(3):389-400
- Backus, J. (1978). *Can Programming Be Liberated from the von Neumann Style?* Communications of the ACM, 21(8):613-641 (Turing Award lecture)
- Bennett, C.H. (2003). *Notes on Landauer's principle, reversible computation, and Maxwell's demon.* Studies in History and Philosophy of Modern Physics, 34(3):501-510
- Girard, J.-Y. (1987). *Linear Logic.* Theoretical Computer Science, 50(1):1-102
- Gurevich, Y. (2000). *Sequential Abstract State Machines Capture Sequential Algorithms.* ACM Transactions on Computational Logic, 1(1):77-111
- Hastad, J. (1987). *Computational Limitations of Small-Depth Circuits.* MIT Press
- Landauer, R. (1961). *Irreversibility and heat generation in the computing process.* IBM Journal of Research and Development, 5(3):183-191
- Weinberger, A. & Smith, J.L. (1958). *A logic for high-speed addition.* National Bureau of Standards Circular 591:3-12
