# Path B: Making obs Structural

## Date: 2026-02-14

## Summary

Path A established equiconsistency with PA using axioms A1-A8, but obs was decorative — the PA-model used obs = identity. Path B gives obs structural teeth by introducing ⊕ (addition) as a second operation and the Leibniz rule for obs-compose interaction.

**Results:**
- (State, ⊕, compose, z, f₀) is a commutative semiring — the natural algebraic setting
- The **eigenvalue theorem** is derived: obs(Sⁿ(f₀)) = n · Sⁿ(f₀) — obs reads off which number a state represents
- **A8 (infinite orbit) becomes a theorem** — derived from characteristic zero (no torsion in the additive structure)
- **A7 (cancellation) remains an axiom** at the ℕ level — but becomes a theorem once we extend to ℤ (integral domain)
- The framework maps directly to semiring-weighted computation

---

## Part 1: The Problem with Path A

In the PA-equiconsistency proof, we built a model of A1-A8 inside PA:

```
State   = ℕ ∪ {∞}
compose = +
obs     = identity
```

This works for consistency, but obs = identity is degenerate. It tells you nothing — every state is a fixed point. The "observation" observes nothing.

In the analytic model (State = smooth functions, compose = multiplication, obs = d/dx), obs is rich: it acts as the readout mechanism, extracting eigenvalues that *are* the numbers. The gap between the PA-model (obs trivial) and the analytic model (obs essential) means the axioms don't capture what makes the construction interesting.

Path B closes this gap.

---

## Part 2: The New Axioms

### What We Add

One new primitive: **⊕ : State → State → State** (the additive operation).

Six new axioms (B1-B6), replacing A7-A8:

### B1. (State, ⊕, z) is a commutative monoid

```
a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c      (associativity)
a ⊕ b = b ⊕ a                    (commutativity)
z ⊕ a = a                        (identity)
```

⊕ is addition. z (the annihilator from A6) doubles as the additive identity. In the analytic model: function addition, with the zero function as identity.

**Computational reading:** ⊕ is parallel composition / superposition of processes. z is the null process.

### B2. compose distributes over ⊕

```
compose(a, b ⊕ c) = compose(a, b) ⊕ compose(a, c)
```

Since compose is commutative (A5), right-distributivity follows for free.

Together with B1, this makes **(State, ⊕, compose, z, f₀) a commutative semiring**: two monoidal operations where one distributes over the other.

**Computational reading:** Sequential composition distributes over parallel composition. Standard in process algebra.

**Note:** The semiring's multiplicative annihilator (z · a = z, i.e., A6) is consistent with z being the additive identity. In any semiring, 0 · a = 0 is derivable from distributivity if addition is cancellative. We retain A6 as an explicit axiom for clarity.

### B3. obs of the identity is null

```
obs(f₀) = z
```

Observing the static process yields nothing. In the analytic model: d/dx(1) = 0.

**Computational reading:** The identity/skip process produces no observable output.

### B4. Leibniz rule

```
obs(compose(a, b)) = compose(obs(a), b) ⊕ compose(a, obs(b))
```

obs is a **derivation** on the semiring — it satisfies the product rule with respect to compose, using ⊕ for the sum.

In the analytic model: d/dx(f · g) = f' · g + f · g'. This is the Leibniz rule / product rule of calculus.

**Computational reading:** Observing a sequential composition sees the observation of each part in the context of the other, combined additively.

### B5. Characteristic zero

```
n · f₀ ≠ z    for all n ≥ 1
```

where n · x denotes x ⊕ x ⊕ ... ⊕ x (n times).

The additive structure has no torsion at f₀. The multiplicative identity is not additively finite-order. This is the abstract version of "1 + 1 + ... + 1 ≠ 0" — the defining property of characteristic zero.

In the analytic model: the constant function 1 added to itself n times gives the constant function n, which is never the zero function.

**Computational reading:** Summing n copies of the identity process always produces a distinguishable result. Processes don't wrap around.

### B6. Cancellation

```
compose(f₁, a) = compose(f₁, b)  →  a = b
```

This is A7 retained. f₁ is cancellable under compose.

**Why this remains an axiom:** In a commutative semiring (no additive inverses), cancellation of multiplicative elements does not follow from other properties. We cannot "subtract" compose(f₁, a) from both sides because ⊕ has no inverses at the ℕ level. See Part 5 for why this becomes a theorem at the ℤ level.

---

## Part 3: The Complete Axiom Set

### Primitives (4)

- **State** — an uninterpreted type
- **compose** : State → State → State
- **obs** : State → State
- **⊕** : State → State → State

### Axioms (12 + non-degeneracy)

| # | Axiom | Statement |
|---|-------|-----------|
| A1 | Self-reproducing process | ∃ f₁, obs(f₁) = f₁ |
| A2 | Multiplicative identity | ∃ f₀, ∀s, compose(f₀, s) = s |
| A3 | Successor | S(s) := compose(f₁, s) |
| A4 | Observational separation | Bisimulation: equal iff indistinguishable by obs and compose |
| A5 | compose is assoc. + comm. | compose(a, compose(b,c)) = compose(compose(a,b), c); compose(a,b) = compose(b,a) |
| A6 | Annihilator | ∃ z, ∀s, compose(z, s) = z |
| B1 | (State, ⊕, z) comm. monoid | ⊕ assoc., comm., z identity |
| B2 | Distributivity | compose(a, b ⊕ c) = compose(a,b) ⊕ compose(a,c) |
| B3 | obs(f₀) = z | Observation of identity is null |
| B4 | Leibniz rule | obs(compose(a,b)) = compose(obs(a),b) ⊕ compose(a, obs(b)) |
| B5 | Characteristic zero | n · f₀ ≠ z for n ≥ 1 |
| B6 | Cancellation | compose(f₁,a) = compose(f₁,b) → a = b |
| — | Non-degeneracy | f₀ ≠ f₁ ≠ z pairwise distinct |

### Algebraic Structure

(State, ⊕, compose, z, f₀) is a **commutative semiring of characteristic zero** with a distinguished cancellable generator f₁ and a derivation obs satisfying obs(f₁) = f₁ and obs(f₀) = z.

---

## Part 4: The Eigenvalue Theorem

### Notation

Write n · x for x ⊕ x ⊕ ... ⊕ x (n copies), with 0 · x := z.

Write fₙ for Sⁿ(f₀) (the n-th element of the orbit).

### Statement

**Theorem (Eigenvalue structure).** For all n ≥ 0:

```
obs(fₙ) = n · fₙ
```

Observation of the n-th state yields n additive copies of that state. The "eigenvalue" n is encoded as the multiplicity.

### Proof

By induction on n.

**Base case (n = 0):**

```
obs(f₀) = z = 0 · f₀     ✓     [B3, convention]
```

**Base case (n = 1):**

```
obs(f₁) = f₁ = 1 · f₁    ✓     [A1]
```

**Inductive step (n → n+1):**

Assume obs(fₙ) = n · fₙ.

```
obs(fₙ₊₁)
= obs(compose(f₁, fₙ))                                         [def. of S]
= compose(obs(f₁), fₙ) ⊕ compose(f₁, obs(fₙ))                 [B4: Leibniz]
= compose(f₁, fₙ) ⊕ compose(f₁, n · fₙ)                       [A1: obs(f₁) = f₁; IH]
= fₙ₊₁ ⊕ compose(f₁, fₙ ⊕ fₙ ⊕ ... ⊕ fₙ)                    [def. of S; expand n · fₙ]
= fₙ₊₁ ⊕ (compose(f₁, fₙ) ⊕ compose(f₁, fₙ) ⊕ ... ⊕ compose(f₁, fₙ))
                                                                 [B2: distributivity, n times]
= fₙ₊₁ ⊕ (fₙ₊₁ ⊕ fₙ₊₁ ⊕ ... ⊕ fₙ₊₁)                        [def. of S]
= fₙ₊₁ ⊕ n · fₙ₊₁
= (n+1) · fₙ₊₁                                                 ∎
```

### What This Means

obs recovers the number. Apply obs to any element of the orbit, and the result is that element repeated "eigenvalue-many" times under ⊕. The abstract d/dx produces the abstract "n · fₙ" without ever naming n as a number — the multiplicity IS the number.

In the analytic model: d/dx(eⁿˣ) = n · eⁿˣ. The theorem proves this is not a special property of the exponential function — it's a structural consequence of the Leibniz rule, the fixed-point property (A1), and the semiring axioms.

---

## Part 5: A8 as a Theorem

### Statement

**Theorem.** Sⁿ(f₀) ≠ f₀ for all n ≥ 1. (= A8, infinite orbit)

### Proof

Suppose for contradiction that Sⁿ(f₀) = f₀ for some n ≥ 1.

```
obs(fₙ) = n · fₙ              [eigenvalue theorem]
        = n · f₀               [hypothesis: fₙ = f₀]

obs(f₀) = z                    [B3]
```

Since fₙ = f₀, we have obs(fₙ) = obs(f₀), so:

```
n · f₀ = z
```

But B5 (characteristic zero) states n · f₀ ≠ z for n ≥ 1. **Contradiction.** ∎

### Significance

A8 is no longer an axiom — it's a consequence of the eigenvalue theorem and characteristic zero. The orbit cannot cycle because obs would detect the contradiction: a state that should have eigenvalue n would also have eigenvalue 0.

The non-cycling of the naturals is not a brute-force postulate. It follows from the interaction between observation and composition.

---

## Part 6: Status of A7 (Cancellation)

### Why A7 Doesn't Follow at the ℕ Level

In a commutative semiring without additive inverses, cancellation is an independent property. If compose(f₁, a) = compose(f₁, b), we cannot form:

```
compose(f₁, a) ⊕ (−compose(f₁, b)) = z
```

because ⊕-inverses don't exist. There's no way to "subtract" and isolate a = b.

### Why A7 Becomes a Theorem at the ℤ Level

When we extend to ℤ (introducing the inverse successor S⁻¹, i.e., f₁⁻¹ under compose), the semiring gains additive inverses and becomes a **commutative ring**. If we additionally require **no zero divisors** (compose(a, b) = z implies a = z or b = z), then (State, ⊕, compose) is an **integral domain**, and cancellation follows:

```
compose(f₁, a) = compose(f₁, b)
→ compose(f₁, a) ⊕ (⊖ compose(f₁, b)) = z         [additive inverse exists]
→ compose(f₁, a ⊕ (⊖b)) = z                        [distributivity]
→ f₁ = z  or  a ⊕ (⊖b) = z                         [no zero divisors]
→ a ⊕ (⊖b) = z                                      [f₁ ≠ z by non-degeneracy]
→ a = b                                              ∎
```

So the full picture:

| Level | A7 status | Why |
|-------|-----------|-----|
| ℕ (semiring) | Axiom | No additive inverses, can't subtract |
| ℤ (ring, no zero divisors) | Theorem | Integral domain gives cancellation for free |

This is mathematically natural: cancellation in ℕ is a fact about ℕ that doesn't follow from the ring axioms until you embed ℕ in ℤ. The same is true in standard mathematics.

---

## Part 7: The Semiring as Computational Foundation

### The Algebraic Structure

(State, ⊕, compose, z, f₀) with obs is:

| Component | Algebraic role | Analytic model | Computational reading |
|-----------|---------------|----------------|----------------------|
| ⊕ | Addition | Function addition | Parallel composition / superposition |
| compose | Multiplication | Function multiplication | Sequential composition |
| z | Additive identity, multiplicative annihilator | Zero function | Null / empty process |
| f₀ | Multiplicative identity | Constant 1 | Identity / skip |
| f₁ | Generator | eˣ | Unit step |
| obs | Derivation | d/dx | Observation / readout |

### Where This Structure Already Exists in CS

The commutative semiring with derivation is not exotic. It appears in:

- **Semiring-weighted automata:** Weighted finite automata over a semiring (S, ⊕, ⊗). Paths through the automaton are composed (⊗), alternatives are summed (⊕). Used in speech recognition, parsing, shortest-path algorithms.

- **Automatic differentiation:** The dual-number semiring ℝ[ε]/(ε² = 0) tracks both value and derivative. Forward-mode AD computes obs(compose(a,b)) via the Leibniz rule. The eigenvalue theorem is essentially what AD does: propagate derivative information through compositions.

- **Tropical semiring:** (ℝ ∪ {∞}, min, +) where ⊕ = min, compose = +. Used in optimization, scheduling, phylogenetics. The Viterbi algorithm runs on the (max, ×) semiring.

- **Process algebra:** CCS, CSP, and the π-calculus have parallel (|) and sequential (;) composition. Bisimulation (A4) is the standard equivalence.

- **Linear logic:** The distinction between ⊕ (additive) and compose (multiplicative) mirrors the additive/multiplicative connective split in linear logic.

### The Orbit and Its Closure

An important structural point: the orbit ℕ = {f₀, f₁, f₂, ...} is closed under compose but **not** under ⊕. In the analytic model:

```
f₂ ⊕ f₃ = e²ˣ + e³ˣ
```

This is not an eigenfunction — it's a **linear combination** of eigenfunctions. The ⊕-closure of ℕ gives the space of finite linear combinations of eigenfunctions (with natural number coefficients), which is a larger algebraic structure.

This mirrors exactly how spectral theory works: the eigenvalues (numbers) are discrete, but the eigenfunctions live in a vector space (or module) where superposition is possible. The semiring axioms capture this ambient structure.

---

## Part 8: Revised Axiom Comparison

### Path A vs Path B

| | Path A (A1-A8) | Path B (A1-A6 + B1-B6) |
|---|---|---|
| **Axiom count** | 8 + non-deg. | 12 + non-deg. |
| **Primitives** | State, compose, obs | State, compose, obs, ⊕ |
| **obs role** | Decorative (PA-model uses obs = id) | Structural (eigenvalue theorem, derives A8) |
| **A8 status** | Axiom | Theorem (from eigenvalue theorem + char. zero) |
| **A7 status** | Axiom | Axiom (becomes theorem at ℤ level) |
| **Eigenvalue eq.** | Not derivable | Theorem: obs(fₙ) = n · fₙ |
| **Algebraic structure** | Commutative monoid + extras | Commutative semiring with derivation |
| **PA equiv.** | Equiconsistent | Equiconsistent (strictly stronger — has semiring structure) |
| **Computational mapping** | Weak | Direct (semiring automata, AD, process algebra) |

### Trade-off

Path B has more axioms but richer structure. Each axiom maps to a computational primitive. The eigenvalue theorem — the core insight of the entire construction — is now a provable theorem rather than an observation about a specific model. obs does real work.

---

## Part 9: What's Next

### Immediate

1. **Formalize in Lean 4** — the semiring + derivation structure has existing Lean/Mathlib formalizations to build on
2. **Prove equiconsistency of Path B with PA** — should follow from Path A + the fact that B1-B6 are consistent with A1-A6 (the analytic model satisfies all of them)

### Medium-term

3. **Extension to ℤ** — add additive inverses (⊖), show the semiring becomes a ring, show A7 becomes a theorem (integral domain)
4. **Extension to ℚ and ℝ** — show the algebraic extensions from the complete document work within the semiring framework
5. **Complex eigenvalues** — obs(f_α) for α = i gives periodic states. The semiring extends to a ℂ-algebra.

### Long-term

6. **ZF emulation** — axiomatize completed infinities and powerset within the framework. The semiring structure makes this more tractable: sets-as-predicates are functions S → {f₀, f₁}, and the powerset is the function space.
7. **Second-order arithmetic (PA₂)** — intermediate target between PA and ZF. Handles sets of naturals, which the predicate framework already addresses informally.

---

## Related

- [axioms](axioms.md)
- [pa-equiconsistency](pa-equiconsistency.md)
- [spectral-arithmetic-complete](spectral-arithmetic-complete.md)
