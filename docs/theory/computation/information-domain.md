# The Information Domain: Bitwise Encoding, Tropical Algebra, and the Refined Obstruction

## Date: 2026-02-19

## Summary

The encoding obstruction trilemma (encoding-obstruction.md) argues that pairing is super-linear while eigenvalue observation is linear, making coalgebra morphism impossible. This document shows that argument is **too coarse**: measured in information content (bit length) rather than arithmetic value, both pairing and eigenvalue scaling are additive. The growth-rate mismatch disappears in the information domain.

However, a **refined obstruction** emerges: moving to the information domain transforms the additive operation ⊕ into tropical max, which destroys the semiring structure needed for PA and hence for self-encoding. The obstruction is not growth rates — it is **⊕**. The additive operation that makes eigenvalues form ℕ is the same operation that resists every change of domain that would reconcile encoding with observation.

**Key result:** The precise location of the encoding obstruction is the ⊕ operation in the Leibniz rule. Compose and obs are reconcilable with encoding in the information domain. ⊕ is not. The research question becomes: is there a domain where compose, obs, AND ⊕ are all compatible with injective pairing?

---

## Part 1: Two Domains, Two Measures

### The arithmetic domain

The trilemma measures growth in **arithmetic value** — the magnitude of the natural number:

| Operation | Input | Output | Growth |
|---|---|---|---|
| Eigenvalue scaling | f_n | n · f_n | Linear in n |
| Cantor pairing | (m, n) | (m+n)(m+n+1)/2 + n | Quadratic in max(m,n) |
| Prime factorization | (m, n) | 2^m · 3^n | Exponential in m+n |
| Binary interleaving | (m, n) | interleave bits | ≈ max(m,n)² in value |

In this measure, every pairing function is super-linear. Eigenvalue scaling is linear. The mismatch drives the trilemma.

### The information domain

The same operations measured in **bit length** (information content, log₂ of the value):

| Operation | Input bits | Output bits | Growth |
|---|---|---|---|
| Eigenvalue scaling | log₂(n) | log₂(n) + log₂(n) = 2·log₂(n) | **Additive** (doubles) |
| Cantor pairing | (log₂(m), log₂(n)) | ≈ 2·max(log₂(m), log₂(n)) | **Additive** |
| Prime factorization | (log₂(m), log₂(n)) | m + n·log₂(3) | **Additive** |
| Binary interleaving | (k bits, k bits) | 2k bits | **Additive** (exactly doubles) |

In the information domain, **all growth rates are additive**. The super-linear/linear mismatch that drives the trilemma is an artifact of measuring in arithmetic value rather than information content.

### Why bit length is the natural measure

Information content (bit length) is the natural measure for encoding because:

1. **Encoding IS information manipulation.** An encoding maps structured information (a term with sub-terms) to flat information (a number/bitstring). The relevant measure is how much information is preserved, not what arithmetic value it maps to.

2. **Binary interleaving is the canonical information-preserving encoding.** It maps k + k bits to 2k bits — no information loss, no information gain. It's the "identity" of the information domain.

3. **The derivative chain is an information hierarchy.** Position = total information. Velocity = rate of information change. Acceleration = rate of rate. Each derivative level peels off one information layer, measured in bits of the rate, not arithmetic magnitude.

---

## Part 2: The Derivative Chain as Information Layers

### Position, velocity, acceleration

In the analytic model, eigenstates are f_n(x) = e^{nx}. Taking logarithms:

```
log(f_n(x)) = nx
```

The eigenvalue n is the **slope** — the information rate. Each derivative reads off the next coefficient:

| Derivative level | What it reads | Information content |
|---|---|---|
| 0th (position) | f_n(x) = e^{nx} | Total state |
| 1st (velocity) | obs(f_n) = n · f_n | Rate = eigenvalue = n |
| 2nd (acceleration) | obs²(f_n) = n² · f_n | Curvature = n² |
| k-th | obs^k(f_n) = n^k · f_n | k-th moment = n^k |

The observation operator doesn't just scale — it **extracts information layers**. Each application of obs peels off one layer of the exponential structure, exposing the next power of the eigenvalue.

### Taylor series as information decomposition

Taylor series makes this explicit:

```
f(x) = Σ (obs^k(f)(0)/k!) · x^k
```

Each term is a derivative level. The coefficients obs^k(f)(0)/k! are the **information at each layer**. Taylor expansion is literally the decomposition of a function into its information content at each derivative order.

In the information domain, this decomposition is a **bit-layer decomposition**: the state's total information is the concatenation of its information at each derivative level. This is structurally identical to how binary interleaving decomposes a pair into interleaved bit layers.

### The connection to encoding

If states are information (bitstrings) and obs reads bit layers, then:

- **obs** reads the next bit layer (derivative = next information level)
- **compose** concatenates/interleaves information (compose(f_m, f_n) = f_{m+n}, additive in eigenvalue = additive in bits)
- **encoding** also interleaves information (binary interleaving is additive in bits)

All three operations are **the same kind of operation** in the information domain: reading, combining, or rearranging bit layers. The growth rates match because all are additive in information content.

---

## Part 3: Where the Information Domain Breaks

### The ⊕ obstacle

The Leibniz rule connects obs to both compose and ⊕:

```
obs(compose(a, b)) = compose(obs(a), b) ⊕ compose(a, obs(b))
```

In the information domain (log scale):
- compose → addition of bit lengths ✓
- obs → reading a bit layer ✓
- ⊕ → ???

Arithmetically, ⊕ is addition of numbers (a + b). In the information domain:

```
info(a ⊕ b) = info(a + b) = log₂(2^{info(a)} + 2^{info(b)})
```

For large values where info(a) > info(b):

```
info(a + b) ≈ info(a) + log₂(1 + 2^{info(b)-info(a)}) ≈ info(a) = max(info(a), info(b))
```

**Addition of numbers becomes max of bit lengths in the information domain.** This is the transformation to the **tropical semiring**.

### The tropical semiring

The information-domain version of (ℕ, +, ×) is (ℕ_info, max, +):

| Arithmetic domain | Information domain | Name |
|---|---|---|
| a + b (addition) | max(info(a), info(b)) (tropical addition) | ⊕ becomes max |
| a × b (multiplication) | info(a) + info(b) (tropical multiplication) | compose becomes + |
| 0 (additive identity) | −∞ (tropical zero) | z becomes −∞ |
| 1 (multiplicative identity) | 0 (tropical unit) | f₀ becomes 0 |

This is a well-studied algebraic structure. Tropical geometry uses exactly this semiring to study piecewise-linear analogues of algebraic geometry.

### Why tropical ℕ doesn't support self-encoding

The tropical semiring (ℕ, max, +) is a legitimate semiring. But it's **not PA-strength**:

1. **No cancellation under max.** max(a, b) = max(a, c) does not imply b = c (e.g., max(5,3) = max(5,2) = 5). Cancellation is essential for PA — it's what gives subtraction, division, and ultimately prime factorization.

2. **No unique factorization.** Without cancellation under the additive operation, the fundamental theorem of arithmetic (unique prime factorization) fails. Without unique factorization, Gödel encoding is impossible — different terms could encode to the same number.

3. **Induction changes character.** Tropical induction (max-induction) doesn't have the same power as standard induction. The tropical naturals under max are an idempotent semiring (max(a,a) = a), which means "adding a number to itself" doesn't give a new number. The counting mechanism that drives PA breaks.

4. **No primitive recursion.** The primitive recursive functions are defined using addition and multiplication. With max replacing addition, the class of definable functions changes — and shrinks. The syntactic predicates (WellFormed, IsAxiom, ValidStep) required for self-encoding are primitive recursive and may not be definable in the tropical setting.

### The refined obstruction

The precise location of the encoding obstruction is now identified:

**It is ⊕ in the Leibniz rule.**

| Operation | Arithmetic domain | Information domain | Compatible with encoding? |
|---|---|---|---|
| compose | Multiplication (super-linear) | Addition (linear) | ✓ in info domain |
| obs | Linear scaling | Bit-layer read | ✓ in info domain |
| **⊕** | **Addition (linear)** | **max (idempotent)** | **✗ in both domains** |

In the arithmetic domain, ⊕ is fine but pairing is super-linear.
In the information domain, pairing is fine but ⊕ becomes max (destroying PA).
**⊕ is the operation that is ill-behaved in whichever domain makes the other operations work.**

---

## Part 4: The Refined Trilemma

### Original trilemma (from encoding-obstruction.md)

Three properties, pick any two:
1. Eigenvalue arithmetic (linear eigenvalues → ℕ → PA)
2. Self-encoding (injective pairing → Gödel encoding)
3. Coalgebra morphism (matching growth rates)

### Refined trilemma

The actual obstruction is sharper. The three properties are:

1. **⊕ is cancellative addition** (needed for PA, hence self-encoding)
2. **⊕ appears in the Leibniz rule** (needed for eigenvalue arithmetic)
3. **Encoding is a coalgebra morphism** (needed for bisimulation)

Pick any two:

**Case 1: Cancellative ⊕ + Leibniz ⊕, without coalgebra morphism** — the framework as it stands. ⊕ is addition, Leibniz works, eigenvalues are linear, PA holds, self-encoding works. But the Leibniz rule's ⊕ creates sums that encoding must pair super-linearly. No morphism.

**Case 2: Leibniz ⊕ + Coalgebra morphism, without cancellative ⊕** — move to the information domain. Compose and obs become compatible with encoding (all additive in bits). But ⊕ becomes max (tropical), which is idempotent, not cancellative. No PA, no self-encoding.

**Case 3: Cancellative ⊕ + Coalgebra morphism, without Leibniz ⊕** — remove ⊕ from the Leibniz rule entirely. But then obs doesn't interact with compose via the product rule. The eigenvalue theorem fails — you can't derive obs(f_n) = n · f_n without the Leibniz rule decomposing obs of products into sums. No eigenvalue arithmetic.

### Why the refined trilemma is tighter

The original trilemma was about growth rates (linear vs. super-linear). The information domain shows growth rates can be reconciled. The refined trilemma is about **algebraic properties of ⊕** — cancellation vs. idempotency — which cannot be reconciled by any change of measure.

The refined trilemma is tighter because:
- Growth rates can be matched by changing the measurement domain (bits vs. values)
- Algebraic properties (cancellative vs. idempotent) are invariant under change of measurement domain
- ⊕ must be cancellative for PA and idempotent (or absent) for encoding compatibility
- These are contradictory algebraic properties of the same operation

---

## Part 5: Is There a Third Domain?

### The question

The arithmetic domain makes ⊕ cancellative but pairing super-linear. The information domain makes pairing additive but ⊕ idempotent. Is there a domain where **all three** — compose, obs, ⊕ — are compatible with injective pairing?

### What the third domain would need

A semiring (S, ⊕', ⊗') where:
1. ⊗' is "compose" — must be compatible with an injective pairing function π: S × S → S
2. ⊕' is "addition" — must be cancellative (a ⊕' b = a ⊕' c → b = c)
3. A derivation obs exists satisfying Leibniz: obs(a ⊗' b) = obs(a) ⊗' b ⊕' a ⊗' obs(b)
4. The eigenvalues of obs form a sub-semiring of S isomorphic to (ℕ, +, ×)
5. The pairing function π is a coalgebra morphism for obs (or at least for some observation operator derived from obs)

### Candidate: p-adic numbers

The p-adic integers ℤ_p have a metric where "closeness" is measured by divisibility by powers of p — an information-theoretic metric (how many leading digits agree). In this metric:

- Addition is continuous and cancellative ✓
- Multiplication is continuous ✓
- The p-adic expansion IS a bitwise encoding (base-p digits) ✓

The p-adic numbers are the natural home of "arithmetic where the digit structure IS the encoding." Buium's "differential calculus with integers" (2013) uses Fermat quotients as p-adic derivations — literally p-adic eigenvalue theory.

**Open question:** Do p-adic derivations (Fermat quotients) produce eigenvalue structure compatible with injective encoding? The p-adic expansion of a number IS its encoding (each digit is a component). If the derivation acts compatibly on digits, the encoding might naturally be a coalgebra morphism.

This is highly speculative but structurally motivated: the p-adic domain is the one where "number" and "encoding" are literally the same structure (a sequence of digits = a sequence of components).

### Candidate: 2-adic integers specifically

The 2-adic integers ℤ_2 are particularly relevant because:
- The encoding IS the binary representation (bit layers)
- The derivative chain (position/velocity/acceleration) maps to successive 2-adic digits
- Binary interleaving is a natural pairing in ℤ_2 (interleave the 2-adic digits)
- The 2-adic metric measures "how many leading bits agree" — information similarity

**The 2-adic Leibniz rule:** If obs is a 2-adic derivation (Fermat quotient δ_2(n) = (n - n²)/2), does the Leibniz rule hold? Fermat quotients satisfy:

```
δ_p(ab) = a · δ_p(b) + b · δ_p(a) + p · δ_p(a) · δ_p(b)
```

This is a **deformed Leibniz rule** — the standard Leibniz rule plus a correction term p · δ_p(a) · δ_p(b). For p = 2, the correction is 2 · δ_2(a) · δ_2(b).

The correction term is the deviation from the standard framework. In the standard framework, the Leibniz rule has no correction. In the 2-adic setting, there's an extra "interaction" term between the derivatives. Whether this correction preserves eigenvalue arithmetic or destroys it is the key question.

### Candidate: formal power series / streams

Rutten's original coalgebra work studied **streams** (infinite sequences) as a final coalgebra. Streams have:
- A head operation (read the first element) = obs
- A derivative operation (shift the stream) = stream derivative
- Pointwise operations (+, ×) with Leibniz-like rules

Streams over a field form a differential algebra where the encoding (a stream IS a sequence of coefficients) is literally the same as the state. The encoding is the identity map, which is trivially a coalgebra morphism.

**The issue:** Streams are infinite objects. ℕ (the eigenvalue space) is discrete and countable. The stream coalgebra is final (universal), so any other coalgebra maps INTO it, but the map from ℕ-indexed eigenstates to streams might not be injective/decodable in the required sense.

---

## Part 6: The ⊕ Spectrum

### Parameterizing the obstruction

The refined trilemma identifies ⊕ as the obstruction. We can parameterize the space of possible ⊕ operations and ask where in this space the obstruction is minimized:

| ⊕ variant | Cancellative? | PA? | Info-domain behavior | Encoding compatible? |
|---|---|---|---|---|
| Standard addition (a + b) | Yes | Yes | Becomes max | No |
| Tropical max (max(a,b)) | No | No | Native | Yes (trivially) |
| Saturating addition (min(a+b, N)) | No (saturates) | No | Bounded max | Partially |
| Modular addition (a + b mod 2^k) | Yes (mod 2^k) | Partial (ℤ/2^k) | Wrapping | Partially |
| p-adic addition | Yes | Embeds ℤ | Digit-compatible | Open question |
| Nim addition (XOR) | Yes (self-inverse) | No (char 2) | Bitwise native | Yes (bitwise) |

### Nim addition (XOR) — the most encoding-compatible ⊕

Binary XOR is the bitwise operation that is:
- Cancellative: a ⊕ b = a ⊕ c → b = c ✓ (XOR is its own inverse)
- Bitwise native: operates independently on each bit ✓
- Compatible with interleaving: bit-layer decomposition is a homomorphism ✓
- Associative and commutative ✓

But XOR gives characteristic 2 (a ⊕ a = 0 for all a). The framework requires characteristic zero (axiom B5: n · f₀ ≠ z for all n ≥ 1). XOR violates this: 2 · f₀ = f₀ ⊕ f₀ = 0.

Without characteristic zero, the eigenvalue theorem fails — you can't distinguish f_2 from f_0 (since 2 = 0 in char 2). The orbit collapses. No ℕ.

### The characteristic zero constraint

This reveals another face of the obstruction. The three requirements on ⊕ are:

1. **Cancellative** — needed for PA
2. **Characteristic zero** — needed for eigenvalue theorem (B5: n · f₀ ≠ z)
3. **Bit-compatible** — needed for encoding morphism

Standard addition satisfies (1) and (2) but not (3).
XOR satisfies (1) and (3) but not (2).
Max satisfies (3) but not (1) or (2).

No known operation satisfies all three. The obstruction is a three-way algebraic incompatibility on ⊕ itself.

---

## Part 7: What This Means for the Research Program

### The obstruction is localized

The information-domain analysis narrows the obstruction from a broad "growth rate incompatibility" to a precise algebraic constraint: **⊕ must be cancellative, characteristic-zero, AND bit-compatible, and no operation satisfies all three.**

This is progress. A broad growth-rate argument is hard to formalize and easy to attack. A precise algebraic impossibility on a single operation is concrete, falsifiable, and potentially provable.

### The research question is now precise

**Is there an algebraic operation ⊕: ℕ × ℕ → ℕ that is simultaneously cancellative, characteristic-zero, and compatible with bitwise encoding (acts independently or predictably on bit layers)?**

If no: the trilemma is a theorem. Prove it by showing these three properties are jointly unsatisfiable for any binary operation on ℕ.

If yes: the trilemma has a loophole. Investigate whether the operation supports a Leibniz rule, eigenvalue arithmetic, and self-encoding.

### Paths forward

**Path A: Prove the ⊕ impossibility directly.** Show that no binary operation on ℕ is simultaneously cancellative, characteristic-zero, and bit-compatible. This is a finite algebraic question — it might be decidable by exhaustive analysis of the constraints.

**Path B: Investigate p-adic arithmetic.** The p-adic integers are the setting where number theory and digit structure naturally coexist. The deformed Leibniz rule (Fermat quotients) might provide a framework where the correction term compensates for the encoding distortion.

**Path C: Investigate 2-adic streams.** Combine Rutten's stream coalgebra (where encoding = identity) with Buium's 2-adic derivations (where derivative = digit shift). If these can be married, the encoding obstruction dissolves because the encoding IS the identity map on the state space.

**Path D: Weaken the bisimulation requirement.** Accept the trilemma and instead characterize the maximal fragment where partial bisimulation holds (encoding-obstruction.md, Part 6). The information-domain analysis suggests this fragment might be larger than the arithmetic-domain analysis implies — because in the information domain, the obstruction is localized to ⊕, not spread across all operations.

---

## Part 8: The Derivative Chain Revisited

### Why position/velocity/acceleration matter

The derivative chain isn't just an analogy — it's the structural reason the information domain is relevant.

In the analytic model:
- **Position** f(x) = e^{nx} — the full state, all information
- **Velocity** f'(x) = n·e^{nx} — first information layer, the eigenvalue
- **Acceleration** f''(x) = n²·e^{nx} — second information layer
- **k-th derivative** f^{(k)}(x) = n^k·e^{nx} — k-th information layer

The eigenvalue n^k at level k is the k-th **moment** of the state's information. The full Taylor expansion recovers the state from its moments:

```
f(x) = Σ_k (n^k/k!) · x^k = e^{nx}
```

This is an **information-theoretic identity**: a state IS the concatenation of its derivative layers. Each obs application peels off one layer. The state is fully determined by its observation sequence — which is the coalgebraic principle (a state is characterized by its behavior under observation).

### Bit layers as derivative layers

In the information domain, binary interleaving decomposes a pair (m, n) into interleaved bit layers. Each "layer" is one bit from each component.

The structural parallel:

| Derivative decomposition | Bit decomposition |
|---|---|
| f = Σ (obs^k(f)(0)/k!) · x^k | n = Σ bit_k(n) · 2^k |
| Each term = one derivative layer | Each term = one bit layer |
| obs peels off one layer | Right-shift peels off one layer |
| Taylor series = full decomposition | Binary expansion = full decomposition |

In both cases: the state is a layered structure, and observation/extraction reads one layer at a time. The information domain is the setting where this parallel becomes an identity — derivative layers ARE bit layers.

### The obstruction, in information-theoretic terms

The Leibniz rule says: the derivative of a product is a **sum** of products of derivatives. In information terms: observing a composed state produces **multiple** information channels (one for each summand in the Leibniz expansion). Encoding multiple channels back into a single state requires pairing.

The obstruction is that **branching** (one observation producing multiple terms via Leibniz) and **encoding** (packing multiple terms into one number) interact through ⊕, and ⊕ has incompatible requirements in the two domains.

If Leibniz produced a single term (no sum, no branching), there would be no obstruction — encoding one term is trivial. The obstruction exists because differentiation of products **branches** (the product rule creates two terms), and this branching is fundamentally incompatible with faithful encoding in a linear observation space.

---

## Related

- [impossibility-hierarchy.md](impossibility-hierarchy.md) — The unified view: addition → state → halting → incompleteness as one impossibility
- [addition-non-locality.md](addition-non-locality.md) — Carry propagation forces external state in self-encoding systems
- [encoding-obstruction.md](encoding-obstruction.md) — The original trilemma and impossibility argument
- [self-representation.md](self-representation.md) — Gödel encoding and the discrete-continuous conjecture
- [confluence.md](confluence.md) — The oriented rewriting system
- [../assessments/lean-formalization-assessment.md](../assessments/lean-formalization-assessment.md) — Full theory assessment
- [../assessments/novelty.md](../assessments/novelty.md) — Novelty analysis
