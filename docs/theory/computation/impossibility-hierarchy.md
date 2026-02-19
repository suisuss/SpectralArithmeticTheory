# The Impossibility Hierarchy: Addition, State, and Undecidability

## Date: 2026-02-20

## Summary

The encoding obstruction (encoding-obstruction.md), the information-domain analysis (information-domain.md), and the addition non-locality theorem (addition-non-locality.md) are not three separate results — they are three levels of a single impossibility that traces from algebra through computation to logic. This document unifies them into a hierarchy:

1. Self-encoding requires addition
2. Addition requires external state (the register)
3. The register is the same state whose normalization is undecidable (the halting problem)
4. Undecidability of normalization is Gödel's incompleteness applied to the system's own computational state

The common object across all four levels is the **register** — the normalization buffer that addition's carry propagation forces into existence, and that the system can represent but cannot decide is "done." The impossibility is self-referential: the system needs addition to encode itself, addition needs state to normalize, and the system cannot decide when its own state normalization is complete.

Every attempt to avoid the register — redundant number systems, residue number systems, tropical algebra — sacrifices a property (uniqueness, ordering, cancellation) that is itself required for self-encoding. The exits are blocked, and they are blocked for specific, identifiable algebraic reasons.

---

## Part 1: The Chain

### Step 1: Self-encoding requires addition

A self-encoding system (one whose states serve as Gödel codes for its own terms) needs the following machinery:

| Requirement | Why it needs addition |
|---|---|
| **Sequence encoding** | Gödel numbers are products of prime powers: 2^{s₁} · 3^{s₂} · 5^{s₃} · ... Computing these products requires repeated addition (multiplication is iterated addition) |
| **Primitive recursive predicates** | WellFormed, IsAxiom, ValidStep are defined by bounded recursion, which requires addition for counting loop iterations and accumulating results |
| **Bounded quantification** | "∃n < k: P(n)" requires iterating from 0 to k, testing P at each step, and combining results — all requiring addition |
| **The Computes predicate** | "There exists a derivation sequence from input to output" requires encoding sequences (addition), checking each step (addition), and counting steps (addition) |

Addition is not optional. Every component of self-encoding — from the basic number assignment through the syntactic predicates to the computational semantics — requires addition as a primitive operation.

### Step 2: Addition requires external state

In any unique positional encoding (which self-encoding requires — see Part 2), addition involves carry propagation: the output at bit position k depends on all inputs at positions 0 through k. This non-locality means:

- Two encoded values enter the addition
- A carry chain propagates across all bit positions (non-local process)
- A new, normalized encoded value emerges

The carry chain is the **external state**. It is a register, an accumulator, a buffer — a mechanism that holds intermediate information (the carry bits) while the non-local process completes. The encoding represents the inputs and the output, but the PROCESS of addition — the carry propagation — lives outside the encoding, in the register.

This is what hardware implements: the ALU's carry chain is physically separate from memory. Data flows from memory (encoding) through the carry chain (state) back to memory (re-encoding). The separation is not an engineering choice but a consequence of addition's non-locality in positional representation.

### Step 3: Can the system account for its own state?

The system can REPRESENT the register's contents. Self-encoding means every state — including the register — has a Gödel code. The system can encode:

- "The register currently holds value v" → an eigenstate encoding this proposition
- "The carry chain has propagated to position k" → an eigenstate encoding this fact
- "The addition of a and b has intermediate result r with carry c at position k" → all encodable

Representation is not the problem. The problem is **normalization**: knowing when the register holds the FINAL value — when the carry chain has fully propagated and the result is complete.

### Step 4: Normalization = halting

"Is the register value the final result of this addition?" seems simple for addition in isolation (carry chains terminate in O(n) steps for n-bit numbers). But in a self-executing system, additions are chained — the output of one addition is the input to the next computation, which may trigger further additions, which produce further carries.

The general question — "has this computation finished producing its final state?" — is the **halting problem**. And it is undecidable.

The subtlety the user identified: **a quiescent state is not necessarily a final state.** A register that hasn't changed might be:

| Observation | Possible reality |
|---|---|
| Register holds value v, unchanged for k steps | The addition is complete and v is the final answer |
| Register holds value v, unchanged for k steps | A carry is propagating through a long chain and hasn't reached this register yet |
| Register holds value v, unchanged for k steps | The computation is in an infinite loop that includes v as a recurring state |
| Register holds value v, unchanged for k steps | The computation is waiting for input from another process that will trigger further state changes |
| Register holds value v, unchanged for k steps | v is a fixed point of the computation — stable but never was "computing" in the first place |

The system cannot distinguish these cases in general. That is Rice's theorem: no non-trivial semantic property of programs (including "this computation has terminated") is decidable.

### Step 5: The recursive trap

The chain loops back on itself:

```
Self-encoding
    requires addition (for prime factorization, predicates, quantification)
        requires external state (carry chain, register)
            representing that state requires encoding it
                encoding requires addition
                    requires more state
                        deciding when state is "done" = halting problem
                            undecidable (Gödel/Turing)
```

The register that addition forces into the system is the same state whose normalization the system cannot decide. The system can create it (it must), represent it (self-encoding), but not determine when it holds a final value (halting problem).

---

## Part 2: Why Every Exit Is Blocked

### The three exits and what they sacrifice

There are exactly three known ways to avoid carry propagation in addition. Each sacrifices a property required for self-encoding.

---

### Exit 1: Redundant number systems (sacrifice uniqueness)

**What they are:** Signed-digit representations (Avizienis, 1961) allow each digit to take values beyond the standard range (e.g., {-1, 0, 1} instead of {0, 1} in binary). This eliminates carry propagation — each output digit depends only on adjacent input digits. Addition becomes local.

**Example (balanced ternary, digits {-1, 0, 1}):**

The number 5 can be represented as:
- (1, -1, -1) meaning 9 - 3 - 1 = 5
- (1, -1, 2) ... but 2 is out of range, so normalize → multiple paths
- Other combinations exist

Multiple digit sequences represent the same number. The representation is **non-unique**.

**What self-encoding requires from uniqueness:**

| Self-encoding requirement | Why uniqueness is needed |
|---|---|
| **Injective encoding** | Different terms must get different codes. If the number 73294 has multiple representations, the Gödel code ⌜compose(f₁, f₀)⌝ is ambiguous — which representation is "the" code? |
| **Deterministic decoding** | Given a code, recover exactly one term. Non-unique representation means a single number could be decoded along different digit paths, potentially yielding different terms |
| **Equality testing** | The predicate "does code n equal code m?" requires comparing Gödel numbers. With non-unique representation, syntactically different digit strings can represent the same number, and determining equality requires... normalization (carry propagation in the comparison), reintroducing the state we were trying to avoid |
| **Canonical forms** | The rewriting system (confluence.md) requires unique normal forms. If codes aren't unique, the notion of "canonical Gödel number for this term" is undefined |
| **Induction** | The induction principle (P5) requires well-ordering: every non-empty subset of ℕ has a least element. Non-unique representations make well-ordering complicated — you need a canonical form to determine ordering, and canonicalization requires... carry propagation |

**The precise trade-off:** Redundant representations eliminate carry propagation for addition but reintroduce it for equality testing and canonicalization. The state doesn't disappear — it migrates from addition to comparison. And comparison is required for every predicate in the self-encoding machinery.

**The fundamental reason:** Self-encoding requires a bijection between terms and numbers. A bijection requires each number to have one representation. One representation per number means non-redundant encoding. Non-redundant encoding means carry propagation for addition. The exit loops back to the entrance.

---

### Exit 2: Residue number systems (sacrifice ordering)

**What they are:** Residue Number Systems (RNS) represent a number by its residues modulo several coprime moduli. For example, with moduli {3, 5, 7}:

```
n = 17  →  (17 mod 3, 17 mod 5, 17 mod 7) = (2, 2, 3)
n = 23  →  (23 mod 3, 23 mod 5, 23 mod 7) = (2, 3, 2)
```

Addition is per-component: (2,2,3) + (2,3,2) = (4 mod 3, 5 mod 5, 5 mod 7) = (1, 0, 5). No carry between components. Fully local.

The representation is unique within the range [0, 3·5·7) = [0, 105) by the Chinese Remainder Theorem.

**What self-encoding requires from ordering:**

| Self-encoding requirement | Why ordering is needed |
|---|---|
| **Bounded quantification** | "∀n < k: P(n)" and "∃n < k: P(n)" require comparing n to k. In RNS, comparing (2,2,3) to (2,3,2) requires converting back to positional form (expensive, involves carry) or comparing residue-by-residue (which doesn't determine ordering: 17 < 23, but the residue (2,2,3) vs (2,3,2) shows no clear pattern) |
| **Primitive recursion** | Defined by recursion on the ORDERING of ℕ: f(0) = base, f(n+1) = step(f(n), n). The successor function n → n+1 in RNS is per-component addition of (1,1,1), which is local. But the recursion bound ("do this n times") requires knowing when to stop, which requires comparing the counter to n — ordering |
| **Prime factorization** | "p divides n" requires division. In RNS, division is only possible when the divisor is coprime to all moduli. General division requires converting out of RNS — which requires carry propagation |
| **Gödel decoding** | Extracting the k-th symbol from a Gödel number requires computing the exponent of the k-th prime in n's factorization. This requires division, modular exponentiation, and ordering — none of which are native to RNS |
| **Induction** | The well-ordering principle (every non-empty subset has a least element) requires ordering. Without it, the induction that drives every syntactic predicate in the self-encoding machinery is unavailable |

**The precise trade-off:** RNS provides carry-free addition, subtraction, and multiplication — but at the cost of ordering, comparison, and division. These are exactly the operations that self-encoding requires beyond basic arithmetic.

**The fundamental reason:** Gödel encoding is inherently POSITIONAL — the k-th prime's exponent encodes the k-th symbol. Decoding requires positional access (which prime? what exponent?). Positional access requires ordering. Ordering in RNS requires conversion to positional form. Conversion requires carry propagation. The exit loops back to the entrance.

---

### Exit 3: Tropical algebra (sacrifice cancellation)

**What it is:** The tropical semiring replaces (ℕ, +, ×) with (ℕ, max, +). In the information domain (log scale), standard addition becomes max. Max is fully local — max(a, b) at each bit position depends only on that position (it's essentially bitwise OR for the leading bit).

**What self-encoding requires from cancellation:**

| Self-encoding requirement | Why cancellation is needed |
|---|---|
| **Subtraction** | If a + b = c, then b = c - a. Cancellation (a + b = a + c → b = c) is what makes subtraction well-defined. With max: max(3,5) = max(3,7) = 7, but 5 ≠ 7. No subtraction |
| **Division** | Division is repeated subtraction. Without subtraction, no division. Without division, no prime factorization. Without prime factorization, no Gödel encoding |
| **Unique factorization** | The fundamental theorem of arithmetic requires cancellation: if p·a = p·b then a = b. Without cancellation, factorization is not unique, and Gödel encoding becomes ambiguous |
| **The eigenvalue theorem** | obs(f_n) = n · f_n requires that different eigenvalues give different observations. With max instead of +, the eigenvalue "addition" max(m, n) = max(m, k) doesn't distinguish n from k. The eigenvalue orbit collapses |
| **Characteristic zero** | Axiom B5 requires n · f₀ ≠ z for all n ≥ 1 (no finite characteristic). In the tropical semiring, n · f₀ = max(f₀, f₀, ..., f₀) = f₀ for all n. Characteristic is effectively 1. The orbit is trivial |

**The precise trade-off:** Tropical algebra makes addition local (max is bitwise) but destroys the algebraic structure needed for number theory. Without cancellation, there is no subtraction, no division, no factorization, and no Gödel encoding.

**The fundamental reason:** Cancellation is what makes ℕ an ORDERED structure with well-defined inverses and decompositions. Tropical max is idempotent (max(a,a) = a) — it loses the counting structure that makes ℕ work. You can't count in a tropical world because adding something to itself doesn't give you something new. And counting is what self-encoding is built on.

---

### Summary of blocked exits

| Exit | What it sacrifices | Why that sacrifice blocks self-encoding | Where carry reappears |
|---|---|---|---|
| **Redundant representations** | Uniqueness | Gödel encoding requires bijection term↔number; non-unique representations break injectivity and require normalization for equality testing | Equality testing, canonicalization |
| **Residue number systems** | Ordering | Bounded quantification, prime factorization, and Gödel decoding all require positional access, which requires ordering | Conversion to positional form |
| **Tropical algebra** | Cancellation | No subtraction → no division → no prime factorization → no Gödel encoding; eigenvalue orbit collapses | Never (but self-encoding becomes impossible, so the question is moot) |

Every exit reintroduces either carry propagation (at a different point in the computation) or destroys self-encoding entirely. The register is inescapable.

---

## Part 3: The Impossibility Hierarchy

### Four levels, one impossibility

| Level | Domain | Impossibility | Common object |
|---|---|---|---|
| **Algebraic** | Coalgebra, eigenvalue theory | Encoding obstruction trilemma: eigenvalue arithmetic + self-encoding + coalgebra morphism are jointly unsatisfiable | ⊕ (addition in the Leibniz rule) |
| **Information-theoretic** | Tropical algebra, bit representations | Growth rates match in the information domain, but ⊕ becomes tropical max, destroying PA | ⊕ (transforms to max under log) |
| **Computational** | Circuit complexity, hardware | Carry propagation in addition is non-local; self-encoding systems with addition require external normalization state | The register (carry chain buffer) |
| **Logical** | Computability, metamathematics | The register's normalization is undecidable (halting problem); the system can't prove its own state is final (incompleteness) | The state whose termination is undecidable |

Each level explains WHY the level above fails:

- The trilemma fails because ⊕ is non-local (information-theoretic level)
- ⊕ is non-local because carry propagation requires state (computational level)
- State can't be self-normalized because that's the halting problem (logical level)
- The halting problem is undecidable because of self-reference + negation (Gödel/Turing)

### The common thread

At every level, the same structure appears: **a self-referential system whose power (addition, self-encoding) creates the very limitation it cannot overcome (state normalization, undecidability).**

| System | Power | Creates | Cannot decide |
|---|---|---|---|
| PA | Self-encoding via Gödel numbers | The Gödel sentence G | Its own consistency |
| Turing machines | Self-simulation via universal TM | The halting configuration | Whether it halts |
| Eigenvalue framework | Self-representation via eigenstates | The register (carry chain for ⊕) | Whether the register holds a final value |

The register, the Gödel sentence, and the halting configuration are the SAME object viewed through different lenses. They are all instances of: "a self-referential construction that the system can build and represent but cannot resolve."

---

## Part 4: The Expanded Eval-Quote Diagram

### The original diagram (encoding-obstruction.md)

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

This diagram doesn't commute because the bottom path (encode → syntactic obs) involves addition (from the Leibniz rule), which requires carry propagation, which requires a register.

### The expanded diagram

```
        eval
Terms ──────────────────→ State
  |                          |
  | ⌜·⌝                     | obs_semantic (eigenvalue scaling, local)
  |                          |
  ↓           ⊕              ↓
State ──→ Register ──→ State
  encode   (carry     re-encode
            chain)
  |                      |
  | normalize?           |
  ↓                      |
 HALT? ←── undecidable ──┘
```

The register sits in the bottom path, between encoding and re-encoding. It's where addition's non-locality is resolved. The question "is the register value final?" is undecidable.

The top path (eval → obs_semantic) doesn't pass through a register — eigenvalue scaling is a single multiplicative step, fully local. This asymmetry — semantic obs is local, syntactic obs requires a register — is the structural reason the diagram doesn't commute.

### Why the asymmetry exists

Semantic observation (obs_semantic) reads off an eigenvalue: obs(f_n) = n · f_n. This is multiplication by a scalar — each bit position is independent (multiplication can be done digit-by-digit with only local carry within each partial product, and even that can be structured to be local with the right representation).

Syntactic observation (obs_code) rewrites a term and re-encodes. The Leibniz rule produces a SUM of terms. Encoding that sum requires... addition. And addition requires carry propagation. And carry propagation requires the register.

The Leibniz rule is the structural reason for the asymmetry: it forces addition into the syntactic path but not into the semantic path. The semantic path is multiplicative (eigenvalue scaling). The syntactic path is additive (Leibniz sum). The multiplicative path is local; the additive path is not.

---

## Part 5: Normal Form ≠ Termination

### The quiescence problem

A state that hasn't changed might be:

1. **A final answer.** The carry chain resolved, addition completed, and the register holds the correct sum. The computation is genuinely done.

2. **A fixed point.** The state satisfies f(s) = s — applying the computation again gives the same state. But this might be an INTERMEDIATE fixed point, not a final answer. Example: 0 is a fixed point of "add 0" but that doesn't mean any computation involving 0 is complete.

3. **A quiescent cycle.** The computation cycles through states including this one. It will change eventually (when the cycle continues) but at the moment of observation, it appears stable.

4. **A waiting state.** The carry chain from a distant bit position hasn't arrived yet. The register appears stable but will change when the carry propagates. In an asynchronous system, "hasn't changed yet" and "won't change ever" are indistinguishable at finite observation time.

5. **A divergent computation.** The computation never terminates, but happens to pass through this state infinitely often. Each visit looks like quiescence; the system never settles.

### Why the system can't distinguish these

The system can observe its own state (self-encoding: encode the register contents as an eigenstate). But distinguishing cases 1-5 requires knowing the FUTURE behavior of the computation:

- Case 1 vs. Case 4: "Will a carry arrive?" requires knowing whether distant bit positions will generate a carry — which depends on the full computation, not just the local state.
- Case 1 vs. Case 5: "Will the state change again?" is exactly the halting problem.
- Case 2 vs. Case 3: "Is this fixed point stable under all future operations?" requires knowing all future inputs.

By Rice's theorem: any non-trivial semantic property of a computation (including "this computation has produced its final output") is undecidable for a sufficiently powerful self-encoding system.

### The connection to confluence

The confluence proof (confluence.md) establishes that every term has a unique normal form — the rewriting system is Church-Rosser. But this guarantees the EXISTENCE of a normal form, not the DECIDABILITY of reaching it. A term may have a unique normal form that is unreachable in finite steps (if reduction sequences can be infinite), or reachable but unrecognizable (if we can't decide "is this the normal form?").

For the rewriting system specifically, confluence + termination (both proved) DO guarantee that every term reaches its normal form in finite steps. But when the rewriting system operates on CODES (self-execution), the situation changes: the codes being rewritten encode terms of unbounded complexity, and the meta-level question "has this sequence of rewrite-on-codes stabilized?" is undecidable even though each individual rewrite terminates.

---

## Part 6: The Impossibility as a Structural Theorem

### Statement

**Theorem (The Self-Encoding State Impossibility, conjectured).** Let S be a system that is:

1. **Self-encoding:** Injective, decodable mapping from terms to states (unique positional representation with ordering)
2. **Self-executing:** Computation on codes uses the system's own operations
3. **Additive:** Includes cancellative, characteristic-zero ⊕
4. **PA-strength:** At least as strong as Peano Arithmetic

Then:

**(a)** The execution of ⊕ on encoded states requires normalization state (a register) external to the positional encoding. (Addition non-locality theorem)

**(b)** No encoding of terms into states is a coalgebra morphism for the system's observation operator. (Encoding obstruction trilemma)

**(c)** The system can represent but cannot decide the normalization status of its own register. (Halting problem / incompleteness)

**(d)** (a), (b), and (c) are manifestations of the same structural fact: **addition's carry propagation is non-local, and this non-locality is irreducible in any unique positional representation that supports self-encoding.**

### The structural fact in one sentence

**A self-encoding system with addition can build, represent, and compute on its own state, but cannot decide when that computation is complete — because the state exists to normalize addition, and addition normalization completion is undecidable.**

### Why the impossibility is tight

Each condition (1)-(4) is individually satisfiable. Pairs are satisfiable. The impossibility is specifically about the conjunction:

| Conditions satisfied | Example | Why it works |
|---|---|---|
| (2)+(3)+(4) without (1) | Standard PA with external Gödel encoding | The encoding is in a separate system; no self-reference constraint on the number representation |
| (1)+(2)+(3) without (4) | Presburger arithmetic (addition without multiplication) | Too weak for Gödel encoding — can't define prime factorization, so self-encoding doesn't produce the Computes predicate |
| (1)+(2)+(4) without (3) | A tropical self-encoding system | max is local, so no register needed — but max isn't cancellative, so no division, no factorization, no meaningful self-encoding |
| (1)+(3)+(4) without (2) | PA with Gödel encoding but no internal execution | Can encode terms and prove things ABOUT computations but doesn't execute on its own codes |

All four together create the trap: the system must do addition on its own codes, addition requires a register, and the register's status is undecidable.

---

## Part 7: Implications

### For the encoding obstruction

The impossibility hierarchy provides the FOUNDATION for the encoding obstruction trilemma. The trilemma says: eigenvalue arithmetic + self-encoding + coalgebra morphism are jointly unsatisfiable. The hierarchy says WHY: the coalgebra morphism fails because the syntactic path through the eval-quote diagram must pass through a register (for addition), while the semantic path doesn't. The asymmetry between the two paths — one additive (syntactic), one multiplicative (semantic) — is irreducible.

### For the bisimulation conjecture

The original discrete-continuous conjecture (self-representation.md, Part 10) asked whether the self-referential loop closes. The hierarchy says: **the loop cannot close because it must pass through undecidable state normalization.**

The loop:
```
obs → eigenvalue arithmetic → self-encoding → computation on codes → ???  → obs
```

The ??? is "normalize the state produced by computation on codes." This requires deciding whether the computation has terminated — the halting problem. The loop's closure requires solving an undecidable problem at the normalization step.

### For computer architecture

The von Neumann bottleneck — the separation between memory (encoding) and processor (computation including addition) — is not an engineering limitation but a mathematical necessity. The register file / ALU separation in CPU architecture is the physical manifestation of the impossibility: encoding (memory) is positional and local, addition (ALU) is non-local, and the two cannot be unified without either sacrificing uniqueness (redundant representation), ordering (RNS), or cancellation (tropical).

### For foundations of mathematics

Every foundational system that includes arithmetic (PA, ZF, type theory, this framework) is a self-encoding system with addition. The impossibility hierarchy applies to all of them:

- **PA:** Gödel's incompleteness IS the impossibility hierarchy for PA
- **ZF:** Gödel's incompleteness for ZF IS the same hierarchy, relativized to set-theoretic encoding
- **Type theory:** Normalization (deciding whether a term has a normal form) is undecidable for sufficiently powerful type theories — the same hierarchy
- **This framework:** The encoding obstruction + halting problem IS the hierarchy for eigenvalue systems

The hierarchy isn't a bug in any particular system. It's a structural theorem about self-encoding systems with addition. Every foundational system that can do arithmetic will have this structure. The only question is where in the hierarchy the system encounters the impossibility — at the algebraic level (trilemma), the computational level (registers), or the logical level (undecidability).

---

## Part 8: The Document Stack

This document completes a four-document stack, from foundation to capstone:

```
┌──────────────────────────────────────────────────────┐
│  impossibility-hierarchy.md  (this document)          │
│  The unified view: addition → state → halting →       │
│  incompleteness as one impossibility at four levels   │
├──────────────────────────────────────────────────────┤
│  addition-non-locality.md                             │
│  Carry propagation is non-local; self-encoding with   │
│  addition requires external state (registers)         │
├──────────────────────────────────────────────────────┤
│  information-domain.md                                │
│  Growth rates match in bits; the real obstruction     │
│  is ⊕ (becomes tropical max, destroying PA)           │
├──────────────────────────────────────────────────────┤
│  encoding-obstruction.md                              │
│  The trilemma: eigenvalue arithmetic + self-encoding  │
│  + coalgebra morphism are jointly unsatisfiable       │
└──────────────────────────────────────────────────────┘
```

Each document adds a layer:
1. **encoding-obstruction.md** identifies the trilemma
2. **information-domain.md** localizes the obstruction to ⊕
3. **addition-non-locality.md** explains WHY ⊕ is the obstruction (carry non-locality)
4. **impossibility-hierarchy.md** (this document) shows that the register forced by carry non-locality is the same state whose normalization is undecidable

The capstone connects to the base: the algebraic trilemma (document 1) fails because of undecidable state normalization (document 4), which exists because addition is non-local (document 3), which is the refined obstruction identified by information-domain analysis (document 2).

---

## Related

- [observer-as-register.md](observer-as-register.md) — Physical interpretation: the observer as the register addition forces into existence
- [encoding-obstruction.md](encoding-obstruction.md) — The trilemma: eigenvalue arithmetic + self-encoding + coalgebra morphism
- [information-domain.md](information-domain.md) — Bitwise encoding, tropical algebra, and the refined ⊕ obstruction
- [addition-non-locality.md](addition-non-locality.md) — Carry propagation forces external state in self-encoding systems
- [self-representation.md](self-representation.md) — Gödel encoding, the self-representation chain, and the discrete-continuous conjecture
- [confluence.md](confluence.md) — Confluence and termination of the rewriting system

## References

- Gödel, K. (1931). *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I.* Monatshefte für Mathematik und Physik, 38:173-198
- Turing, A.M. (1936). *On Computable Numbers, with an Application to the Entscheidungsproblem.* Proceedings of the London Mathematical Society, 42:230-265
- Rice, H.G. (1953). *Classes of recursively enumerable sets and their decision problems.* Transactions of the AMS, 74(2):358-366
- Gurevich, Y. (2000). *Sequential Abstract State Machines Capture Sequential Algorithms.* ACM Transactions on Computational Logic, 1(1):77-111
- Avizienis, A. (1961). *Signed-digit number representations for fast parallel arithmetic.* IRE Transactions on Electronic Computers, EC-10(3):389-400
- Hastad, J. (1987). *Computational Limitations of Small-Depth Circuits.* MIT Press
