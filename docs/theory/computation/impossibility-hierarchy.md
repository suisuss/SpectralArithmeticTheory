# The Impossibility Hierarchy: From Substitution to Undecidability

## Date: 2026-02-20 (revised 2026-02-21)

## Summary

The encoding obstruction is one impossibility viewed at four levels. This document unifies them into a hierarchy, starting from the fundamental insight that **mathematics is substitution** and substitution is open-ended:

1. **Philosophical**: Substitution never reaches a fixed point — the intension/extension gap is irreducible in any self-naming system (encoding-obstruction.md)
2. **Information-theoretic**: For executable encoding (not just passive labeling), the intension/extension switch must be *performed* — this requires manipulating positions, and the Leibniz rule introduces addition (⊕) into the switch
3. **Computational**: Addition on unique positional encodings requires carry propagation; carry is non-local; non-locality requires external state (the register) — (addition-non-locality.md)
4. **Logical**: The register's normalization is undecidable (the halting problem); the system can represent but cannot decide its own state is final (Gödel/Turing)

The common thread: **a self-naming system whose substitution operation (extensionalization) introduces addition, and addition introduces state whose termination is undecidable.** The register that carry propagation forces into existence is the same state whose normalization the system cannot decide. The impossibility is self-referential: the system needs addition to execute its own encoding, addition needs state to normalize, and the system cannot decide when its own state normalization is complete.

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

### Step 4: There is no bottom

The halting problem is not a separate result that needs to be "connected" to the encoding obstruction. It IS the encoding obstruction viewed temporally.

A self-executing encoding must perpetually switch between intensional and extensional modes:
- **Extensionalize**: unfold a named form via the Leibniz rule (substitution)
- **Re-intensionalize**: give the unfolded result a new name (re-encode)
- **Extensionalize again**: unfold the new name...

"The computation has halted" would mean this switching has reached a fixed point — that some extensionalization produces the same form as the intensionalization before it. But `substitution_chain_distinct` (proved in Lean, sorry-free) shows **there is no fixed point**: every level of extensionalization produces a structurally distinct term. The intensional form, the one-step extensional form, and the deeply extensional form are all provably different.

Therefore: a self-executing encoding can never report "done," because "done" would mean a fixed point of substitution, and substitution has no fixed point. **The halting problem for self-executing encodings is not that we can't determine whether the switching has stopped — it's that the switching doesn't stop.** There is no final normalization. There is no bottom.

And a system that could prove the switching doesn't stop would need to encode the entire infinite chain of extensionalizations — which would itself be a form that could be extensionalized further. The proof of non-termination is itself subject to non-termination.

This is not an appeal to Turing 1936 or Rice 1953 as external results. It is a direct reading of theorems already proved in the Lean formalization:
- `no_coalgebra_morphism`: the encoding never commutes with extensionalization (for ANY encoding, ANY term)
- `substitution_chain_distinct`: each level of extensionalization produces a new, distinct form
- `semantic_invariance_general`: the meaning is preserved at every level — the system isn't diverging semantically, it's diverging formally

The perpetual switching IS the halting problem for self-executing encodings, realized algebraically.

**A quiescent state is not necessarily a final state.** A register that hasn't changed might be:

| Observation | Possible reality |
|---|---|
| Register holds value v, unchanged for k steps | The addition is complete and v is the final answer |
| Register holds value v, unchanged for k steps | A carry is propagating through a long chain and hasn't reached this register yet |
| Register holds value v, unchanged for k steps | The computation is in an infinite loop that includes v as a recurring state |
| Register holds value v, unchanged for k steps | The computation is waiting for input from another process that will trigger further state changes |
| Register holds value v, unchanged for k steps | v is a fixed point of the computation — stable but never was "computing" in the first place |

The system cannot distinguish these cases in general. That is Rice's theorem: no non-trivial semantic property of programs (including "this computation has terminated") is decidable.

### Step 5: Why this is the same as Gödel/Turing

The classical impossibility results are specific instances of the same structure — substitution has no fixed point, and there is no bottom:

| Classical result | What it says | How it maps to perpetual switching |
|---|---|---|
| **Gödel 1931** | The system can name (intensionalize) "I am not provable" but unfolding (extensionalizing) the name never resolves it | The Gödel sentence IS a form where the intension/extension switching cycles: name → unfold → re-name → unfold → ... with no fixed point |
| **Turing 1936** | No program can decide whether another program halts | "Halts" means the intension/extension switching stops. It doesn't stop, because substitution has no fixed point. A program that could decide this would need to reach the non-existent bottom. |
| **Rice 1953** | No non-trivial semantic property of programs is decidable | Any semantic property requires resolving the intension/extension chain to a fixed point. No fixed point exists. |

These are not three separate theorems requiring separate formal connections. They are three formulations of: **substitution is open-ended, and there is no bottom.** The Lean formalization proves this at the algebraic level (`substitution_chain_distinct`, `no_coalgebra_morphism`), and the classical results are what it looks like from the logical level.

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

| Level | Domain | Impossibility | Lean status |
|---|---|---|---|
| **Philosophical** | Intension/extension, substitution | Substitution never reaches a fixed point; any form can be re-named; the encoding of execution ≠ execution of encoding | `no_coalgebra_morphism`, `substitution_chain_distinct` — **proved** |
| **Information-theoretic** | Positions, bits, eigenvalues | For executable encoding, the intension/extension switch introduces ⊕ (Leibniz rule); no bitwise realization of ⊕ satisfies the framework's requirements | `oplus_bitwise_impossible`, `bitwise_inherits_char_two` — **proved** |
| **Computational** | Circuit complexity, hardware | Carry propagation in ⊕ is non-local; self-encoding systems with executable addition require external normalization state (the register) | `carry_propagation_general` — **proved** |
| **Logical** | Computability, metamathematics | There is no bottom: substitution has no fixed point, so no self-executing encoding can report completion. This IS the halting problem for executable self-reference. | **Direct reading** of the three levels above — not a separate theorem |

The key insight: the logical level is not a separate result requiring a separate formal connection. It is what the first three levels **mean** when read temporally:

- Substitution has no fixed point (proved) → there is no "done" state
- ⊕ is non-local (proved) → the state tracking the switching requires external machinery
- Carry propagation is general (proved) → this holds in any base, any positional system

"The halting problem" is the name we give to the observation that self-executing encodings can never report completion. The Lean formalization proves the structural fact; the halting problem is its temporal reading.

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

**Theorem (The Self-Encoding State Impossibility).** Let S be a system with a term algebra that includes observation (obs) and composition (compose), where observation obeys the Leibniz rule (product rule). Then:

**(a) [Proved in Lean, sorry-free]** No injective encoding ε : Term → ℕ is a coalgebra morphism for the observation operator. For ALL terms a, b: ε(obsRewrite(obs(compose(a,b)))) ≠ ε(obs(compose(a,b))). The extensionalized (Leibniz-unfolded) form is always structurally distinct from the intensional (original) form, and any injective encoding must reflect this. (`no_coalgebra_morphism`)

**(b) [Proved in Lean, sorry-free]** The meaning is preserved across the gap: eval(obs(compose(a,b))) = eval(obsRewrite(obs(compose(a,b)))) for all a, b, in all models. (`semantic_invariance_general`)

**(c) [Proved in Lean, sorry-free]** Substitution has no fixed point: the intensional form, the one-step extensional form, and the deeply extensional form are three provably distinct terms. Each level of extensionalization produces a new form. (`substitution_chain_distinct`)

**(d) [Direct reading of (a)-(c)]** The halting problem for self-executing encodings: "the computation has finished" would require the intension/extension switching to reach a fixed point. By (c), no fixed point exists. Therefore no self-executing encoding can report completion. There is no bottom.

**(e) [Proved in Lean, sorry-free]** The ⊕ that extensionalization introduces cannot be realized as a position-local (bitwise) operation while satisfying the framework's algebraic requirements (commutative, cancellative, characteristic zero). Any such operation has characteristic 2. (`oplus_bitwise_impossible`, `bitwise_inherits_char_two`)

**(f) [Proved in Lean, sorry-free]** Carry propagation is general: for any base b ≥ 2 and any k ≥ 1, addition produces non-local effects (output at position k depending on inputs at all positions 0..k-1). (`carry_propagation_general`)

### The structural fact in one sentence

**Substitution is open-ended — every extensionalized form can be re-intensionalized, and every intensionalized form can be re-extensionalized — so there is no fixed point, no bottom, and no self-executing encoding that can report "done."**

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

This document unifies a four-document stack, from obstruction through mechanism to consequence:

```
┌──────────────────────────────────────────────────────┐
│  encoding-obstruction.md                              │
│  THE OBSTRUCTION: intension/extension gap;            │
│  substitution is open-ended; no fixed point exists    │
├──────────────────────────────────────────────────────┤
│  information-domain.md                                │
│  The refinement: in bits, ⊕ becomes tropical max;     │
│  the gap can't be worked around in any domain         │
├──────────────────────────────────────────────────────┤
│  addition-non-locality.md                             │
│  THE MECHANISM: for executable encoding, the gap      │
│  introduces ⊕ via Leibniz; carry is non-local;        │
│  external state (register) is forced                  │
├──────────────────────────────────────────────────────┤
│  impossibility-hierarchy.md  (this document)          │
│  THE CONSEQUENCE: the register's normalization is     │
│  undecidable; all four levels are one impossibility   │
└──────────────────────────────────────────────────────┘
```

The reading order follows the logical chain:
1. **encoding-obstruction.md** identifies the fundamental obstruction: intension/extension irreducibility in self-naming systems, the passive/executable distinction
2. **information-domain.md** confirms the gap can't be resolved by domain change: ⊕ becomes tropical max, destroying the arithmetic needed for self-encoding
3. **addition-non-locality.md** identifies the mechanism for executable encodings: carry propagation is non-local, forcing external state
4. **impossibility-hierarchy.md** (this document) shows the consequence: the forced state's normalization is undecidable, connecting to Gödel/Turing

---

## Related

- [observer-as-register.md](observer-as-register.md) — Physical interpretation: the observer as the register addition forces into existence
- [encoding-obstruction.md](encoding-obstruction.md) — The trilemma: eigenvalue arithmetic + self-encoding + coalgebra morphism
- [information-domain.md](information-domain.md) — Bitwise encoding, tropical algebra, and the refined ⊕ obstruction
- [addition-non-locality.md](addition-non-locality.md) — Carry propagation forces external state in self-encoding systems
- [computing-as-external-state.md](computing-as-external-state.md) — The obstruction as metatheorem about Turing/Church: why computation requires external state
- [self-representation.md](self-representation.md) — Gödel encoding, the self-representation chain, and the discrete-continuous conjecture
- [confluence.md](confluence.md) — Confluence and termination of the rewriting system

## References

- Gödel, K. (1931). *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I.* Monatshefte für Mathematik und Physik, 38:173-198
- Turing, A.M. (1936). *On Computable Numbers, with an Application to the Entscheidungsproblem.* Proceedings of the London Mathematical Society, 42:230-265
- Rice, H.G. (1953). *Classes of recursively enumerable sets and their decision problems.* Transactions of the AMS, 74(2):358-366
- Gurevich, Y. (2000). *Sequential Abstract State Machines Capture Sequential Algorithms.* ACM Transactions on Computational Logic, 1(1):77-111
- Avizienis, A. (1961). *Signed-digit number representations for fast parallel arithmetic.* IRE Transactions on Electronic Computers, EC-10(3):389-400
- Hastad, J. (1987). *Computational Limitations of Small-Depth Circuits.* MIT Press
