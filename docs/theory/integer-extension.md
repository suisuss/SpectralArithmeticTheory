# ℤ Extension: From Semiring to Integral Domain

## Date: 2026-02-14

## Summary

The ℕ-level framework (A1-A6 + B1-B6) is a commutative semiring with derivation. Extending to ℤ requires two things: a compose-inverse for f₁ (enabling decay / negative eigenvalues) and ⊕-inverses (enabling subtraction / ring structure). With a no-zero-divisors axiom, the ring becomes an **integral domain**, and A7 (cancellation) — the last remaining brute-force axiom — becomes a theorem.

**Results:**
- Three new axioms (C1-C3) extend the framework to ℤ
- A7 (cancellation) is now a **theorem** at every level — derived from integral domain structure
- The eigenvalue theorem extends to all of ℤ: obs(fₙ) = n · fₙ for n ∈ ℤ
- Negative eigenvalues are decay processes — the sign has dynamical content
- The **power rule** obs(gⁿ) = n · gⁿ⁻¹ · obs(g) is proved as a lemma — opens the path to ℚ

---

## Part 1: What's Missing at the ℕ Level

Two structural gaps:

**1. No compose-inverse for f₁.**

S(s) = compose(f₁, s) can go forward (growth) but not backward (decay). The orbit {f₀, f₁, f₂, ...} extends only in one direction. Negative eigenvalues don't exist.

In the analytic model, the inverse is f₁⁻¹(x) = e⁻ˣ — the decaying eigenfunction. It exists because e^x · e^{-x} = 1.

**2. No ⊕-inverses (no subtraction).**

(State, ⊕, z) is a commutative monoid, not a group. You can add processes but not subtract them. This prevents algebraic manipulation — you can't move terms across equations.

Consequence: A7 (cancellation) must remain an axiom because you can't derive compose(f₁, a) = compose(f₁, b) → a = b by subtracting.

---

## Part 2: New Axioms (C1-C3)

### C1. Compose-inverse of f₁ exists

```
∃ f₁⁻¹ : State,  compose(f₁, f₁⁻¹) = f₀
```

The unit process has an inverse under composition. In the analytic model: e^x · e^{-x} = 1.

**Computational reading:** Every unit step can be undone. Reversible computation.

Combined with commutativity (A5): compose(f₁⁻¹, f₁) = f₀ as well.

### C2. ⊕-inverses exist

```
∀ s : State,  ∃ ⊖s : State,  s ⊕ (⊖s) = z
```

Every state has an additive inverse. This upgrades (State, ⊕, z) from a commutative monoid to a commutative (abelian) group. The semiring becomes a **commutative ring**.

In the analytic model: for any function f, the function -f exists and f + (-f) = 0.

**Computational reading:** Every process has a cancellation / undo in the additive layer.

### C3. No zero divisors

```
compose(a, b) = z  →  a = z  ∨  b = z
```

The ring has no zero divisors. A product is null only if a factor is null. This makes (State, ⊕, compose, z, f₀) an **integral domain**.

In the analytic model: if f · g = 0 (the zero function everywhere), then f = 0 or g = 0 (since pointwise multiplication of non-zero-somewhere functions is non-zero-somewhere).

**Computational reading:** Composing two non-null processes always produces a non-null process. Nullity doesn't arise from composition of real processes.

---

## Part 3: A7 (Cancellation) Is Now a Theorem

### Statement

**Theorem.** compose(f₁, a) = compose(f₁, b) → a = b.

### Proof

```
compose(f₁, a) = compose(f₁, b)
```

Since (State, ⊕) is now a group (C2), additive inverses exist:

```
compose(f₁, a) ⊕ ⊖(compose(f₁, b)) = z
```

In any ring, ⊖(compose(x, y)) = compose(x, ⊖y). Proof:

```
compose(x, y) ⊕ compose(x, ⊖y)
= compose(x, y ⊕ ⊖y)                    [B2: distributivity]
= compose(x, z)                          [C2: y ⊕ ⊖y = z]
= z                                      [A6: z is annihilator]
```

So compose(x, ⊖y) is the additive inverse of compose(x, y). ✓

Continuing:

```
compose(f₁, a) ⊕ compose(f₁, ⊖b) = z    [ring property above]
compose(f₁, a ⊕ ⊖b) = z                  [B2: distributivity]
```

By C3 (no zero divisors): f₁ = z or a ⊕ ⊖b = z.

f₁ ≠ z by non-degeneracy.

Therefore a ⊕ ⊖b = z, which means a = b. ∎

### Significance

A7 is no longer an axiom at any level. It's a consequence of the ring being an integral domain. The axiom count for Path B was:

| Before (ℕ level) | After (ℤ level) |
|---|---|
| A1-A6 + B1-B6 (12 axioms, B6 = cancellation) | A1-A6 + B1-B5 + C1-C3 (14 axioms, cancellation derived) |

More axioms total, but one fewer *ad hoc* axiom. B6 (cancellation) was a brute-force constraint. C1-C3 are structural (inverse exists, subtraction exists, no zero divisors) and each maps to a computational primitive.

---

## Part 4: The Integer Orbit

### Construction

Define the inverse successor:

```
S⁻¹(s) := compose(f₁⁻¹, s)
```

The integers are the orbit of f₀ under both S and S⁻¹:

```
ℤ := {..., S⁻²(f₀), S⁻¹(f₀), f₀, S(f₀), S²(f₀), ...}
   = {..., f₋₂, f₋₁, f₀, f₁, f₂, ...}
```

where f₋ₙ = (f₁⁻¹)ⁿ = compose(f₁⁻¹, f₁⁻¹, ..., f₁⁻¹) composed with f₀.

### Dynamical Meaning

| Eigenvalue | State | Behavior |
|---|---|---|
| 3 | f₃ = f₁³ | Growth at rate 3 |
| 1 | f₁ | Unit growth |
| 0 | f₀ | Stasis |
| -1 | f₋₁ = f₁⁻¹ | Unit decay |
| -3 | f₋₃ = (f₁⁻¹)³ | Decay at rate 3 |

The sign of a number is the **direction of the process**: positive is growth, negative is decay, zero is the boundary.

---

## Part 5: Eigenvalue Theorem for ℤ

### Lemma: obs(f₁⁻¹) = ⊖f₁⁻¹

From the Leibniz rule applied to compose(f₁, f₁⁻¹) = f₀:

```
obs(compose(f₁, f₁⁻¹)) = obs(f₀) = z                              [B3]

compose(obs(f₁), f₁⁻¹) ⊕ compose(f₁, obs(f₁⁻¹)) = z              [B4: Leibniz]

compose(f₁, f₁⁻¹) ⊕ compose(f₁, obs(f₁⁻¹)) = z                   [A1: obs(f₁) = f₁]

f₀ ⊕ compose(f₁, obs(f₁⁻¹)) = z                                   [C1: f₁ · f₁⁻¹ = f₀]

compose(f₁, obs(f₁⁻¹)) = ⊖f₀                                      [C2: additive inverse]
```

Apply compose with f₁⁻¹ to both sides (cancellation, now a theorem):

```
obs(f₁⁻¹) = compose(f₁⁻¹, ⊖f₀)
           = ⊖(compose(f₁⁻¹, f₀))                                  [ring: x · (⊖y) = ⊖(x·y)]
           = ⊖f₁⁻¹                                                  [A2: f₀ is identity]
           = (⊖1) · f₋₁                                             ∎
```

In the analytic model: d/dx(e⁻ˣ) = -e⁻ˣ = (-1) · e⁻ˣ. ✓

### Theorem (Eigenvalue for ℤ)

For all n ∈ ℤ:

```
obs(fₙ) = n · fₙ
```

where n · x for negative n means ⊖(|n| · x).

### Proof

The positive case (n ≥ 0) is established in [path-b-obs-structure](path-b-obs-structure.md).

For the negative case, by downward induction from 0.

**Base (n = 0):** obs(f₀) = z = 0 · f₀. ✓

**Step (n → n-1):** Assume obs(fₙ) = n · fₙ for some n ≤ 0. Show obs(fₙ₋₁) = (n-1) · fₙ₋₁.

```
fₙ₋₁ = compose(f₁⁻¹, fₙ)                                           [def: inverse successor]

obs(fₙ₋₁) = obs(compose(f₁⁻¹, fₙ))
           = compose(obs(f₁⁻¹), fₙ) ⊕ compose(f₁⁻¹, obs(fₙ))      [B4: Leibniz]
           = compose(⊖f₁⁻¹, fₙ) ⊕ compose(f₁⁻¹, n · fₙ)           [Lemma; IH]
```

For the first term:

```
compose(⊖f₁⁻¹, fₙ) = ⊖compose(f₁⁻¹, fₙ)                           [ring: (⊖a)·b = ⊖(a·b)]
                     = ⊖fₙ₋₁                                        [definition of fₙ₋₁]
```

For the second term:

```
compose(f₁⁻¹, n · fₙ)
= n · compose(f₁⁻¹, fₙ)                                             [distributivity, extended to ℤ-multiples]
= n · fₙ₋₁
```

Combining:

```
obs(fₙ₋₁) = ⊖fₙ₋₁ ⊕ n · fₙ₋₁
           = (-1 + n) · fₙ₋₁
           = (n - 1) · fₙ₋₁                                          ∎
```

### What This Means

Observation reads off the eigenvalue for all integers — positive, negative, and zero. The eigenvalue theorem is universal across ℤ:

```
obs(f₃)  = 3 · f₃       three copies (growth at rate 3)
obs(f₁)  = f₁            one copy (unit growth)
obs(f₀)  = z             zero copies (stasis)
obs(f₋₁) = ⊖f₋₁         negative one copy (unit decay)
obs(f₋₃) = (⊖3) · f₋₃   negative three copies (decay at rate 3)
```

Negative eigenvalues are additive inverses of positive eigenvalues. Decay is the ⊖ of growth.

---

## Part 6: The Power Rule

### Statement

**Lemma (Power Rule).** For any state g and positive integer n:

```
obs(gⁿ) = n · gⁿ⁻¹ · obs(g)
```

where gⁿ = compose(g, g, ..., g) [n times] and · stands for compose.

### Proof

By induction on n.

**Base (n = 1):** obs(g¹) = obs(g) = 1 · g⁰ · obs(g) = 1 · f₀ · obs(g) = obs(g). ✓

**Step (n → n+1):**

```
obs(gⁿ⁺¹) = obs(compose(g, gⁿ))
           = compose(obs(g), gⁿ) ⊕ compose(g, obs(gⁿ))              [B4: Leibniz]
           = compose(obs(g), gⁿ) ⊕ compose(g, n · gⁿ⁻¹ · obs(g))    [IH]
           = gⁿ · obs(g) ⊕ n · gⁿ · obs(g)                          [assoc., comm.]
           = (1 + n) · gⁿ · obs(g)
           = (n+1) · gⁿ · obs(g)                                      ∎
```

### Why This Matters: The Path to ℚ

The power rule is the abstract version of d/dx(xⁿ) = n · xⁿ⁻¹ — but for compose-powers of any state, not just the variable x. It's the key to extending eigenvalues to rationals.

For the ℚ extension, we introduce q-th roots: states g such that gᵍ = f₁. If such a g exists, then:

```
obs(gᵍ) = obs(f₁) = f₁                                    [A1]
q · gᵍ⁻¹ · obs(g) = f₁                                    [power rule]
q · gᵍ⁻¹ · obs(g) = gᵍ                                    [since gᵍ = f₁]
```

This gives:

```
obs(g) = gᵍ / (q · gᵍ⁻¹) = g / q = (1/q) · g
```

(where division by q means the unique element x such that q · x = g, which exists in a ℚ-module).

So the q-th root of f₁ has eigenvalue 1/q. The rational eigenvalues emerge from roots and the power rule.

---

## Part 7: The Complete Axiom Set (ℤ Level)

### Primitives (4)

State, compose, obs, ⊕

### Axioms (15 + non-degeneracy)

**Process core (A1-A6):**

| # | Name | Statement |
|---|------|-----------|
| A1 | Self-reproducing | ∃ f₁, obs(f₁) = f₁ |
| A2 | Identity | ∃ f₀, ∀s, compose(f₀, s) = s |
| A3 | Successor | S(s) := compose(f₁, s) |
| A4 | Bisimulation | Equal iff indistinguishable by obs and compose |
| A5 | Assoc. + comm. | compose is associative and commutative |
| A6 | Annihilator | ∃ z, ∀s, compose(z, s) = z |

**Semiring + observation (B1-B5):**

| # | Name | Statement |
|---|------|-----------|
| B1 | Additive monoid | (State, ⊕, z) assoc., comm., z identity |
| B2 | Distributivity | compose(a, b ⊕ c) = compose(a,b) ⊕ compose(a,c) |
| B3 | obs(f₀) = z | Observation of identity is null |
| B4 | Leibniz | obs(compose(a,b)) = compose(obs(a), b) ⊕ compose(a, obs(b)) |
| B5 | Char. zero | n · f₀ ≠ z for n ≥ 1 |

**Ring + integral domain (C1-C3):**

| # | Name | Statement |
|---|------|-----------|
| C1 | Compose-inverse | ∃ f₁⁻¹, compose(f₁, f₁⁻¹) = f₀ |
| C2 | ⊕-inverses | ∀s, ∃ ⊖s, s ⊕ ⊖s = z |
| C3 | No zero divisors | compose(a,b) = z → a = z ∨ b = z |

**Non-degeneracy:** f₀ ≠ f₁ ≠ z pairwise distinct.

### What We Dropped

B6 (cancellation) is gone — it's now a theorem derived from C2 + C3 (integral domain). The axiom set has grown from 12 to 14 proper axioms, but every axiom is structural (no ad hoc constraints).

### Algebraic Structure

(State, ⊕, compose, z, f₀) is a **commutative integral domain of characteristic zero** with:
- a distinguished generator f₁ (invertible under compose)
- a derivation obs satisfying obs(f₁) = f₁ and obs(f₀) = z

---

## Part 8: Derived Results Summary

| Result | Proof technique | Uses |
|---|---|---|
| Eigenvalue theorem (ℕ): obs(fₙ) = n · fₙ | Induction, Leibniz, distributivity | B4, B2, A1 |
| A8 (infinite orbit): Sⁿ(f₀) ≠ f₀ | Eigenvalue + char. zero | B5 |
| Cancellation (was A7/B6): f₁ · a = f₁ · b → a = b | Integral domain | C2, C3 |
| obs(f₁⁻¹) = ⊖f₁⁻¹ | Leibniz on f₁ · f₁⁻¹ = f₀ | B4, C1, C2 |
| Eigenvalue theorem (ℤ): obs(fₙ) = n · fₙ for n ∈ ℤ | Downward induction | Lemma + IH |
| Power rule: obs(gⁿ) = n · gⁿ⁻¹ · obs(g) | Induction, Leibniz | B4 |
| Ring properties: ⊖(a·b) = a·(⊖b) = (⊖a)·b | Distributivity + uniqueness of inverses | B2, C2 |
| PA (all 9 axioms) | Path A arguments | A1-A6, B5, derived cancellation |

---

## Part 9: What's Next

### ℚ Extension

Introduce q-th roots of f₁:

```
D1. ∀ q ≥ 1, ∃ g : State, gᵍ = f₁    (q-th root of the generator)
```

The power rule then gives obs(g) = (1/q) · g — rational eigenvalues. The integral domain extends to a **field of fractions**. The eigenvalue theorem covers all of ℚ.

### ℝ Extension

Cauchy completion of ℚ. The ordered field structure (f(x) > 0 for rational x, f monotone) extends by continuity. The Taylor series is a theorem about the completed f, not its definition.

### Toward ZF

With the integral domain established, the algebraic machinery is strong enough to:
- Define sets as predicates S → {f₀, f₁} (already done informally)
- Define ∈ as predicate application (already done)
- Axiomatize powerset, infinity, replacement as existence claims about predicates

The integral domain structure gives us the arithmetic needed to count, measure, and compute within the set interpretation.

---

## Related

- [axioms](axioms.md)
- [pa-equiconsistency](pa-equiconsistency.md)
- [path-b-obs-structure](path-b-obs-structure.md)
- [extending-the-number-systems](extending-the-number-systems.md)
