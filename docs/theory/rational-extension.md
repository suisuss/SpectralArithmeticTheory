# ℚ Extension: Roots, Rational Eigenvalues, and the Field of Fractions

## Date: 2026-02-14

## Summary

The ℤ-level framework is a commutative integral domain of characteristic zero with a Leibniz derivation. Extending to ℚ requires two things: q-th roots of f₁ (giving fractional eigenvalues) and unique divisibility of the additive group (giving rational scalar multiples). The power rule — already proved at the ℤ level — does the heavy lifting.

**Results:**
- Two new axioms (D1-D2) extend the framework to ℚ
- **Torsion-freeness lemma:** no non-zero element has finite additive order — derived from characteristic zero + integral domain
- **Eigenvalue theorem extends to ℚ:** obs(f_{p/q}) = (p/q) · f_{p/q} for all p/q ∈ ℚ
- **Rational arithmetic is captured:** compose(f_{a/b}, f_{c/d}) = f_{a/b + c/d}
- The integral domain extends to a **ℚ-algebra** — the natural home for rational eigenvalues
- The path to ℝ is now clear: Cauchy completion, with all algebraic structure in place

---

## Part 1: What's Missing at the ℤ Level

Two gaps prevent rational eigenvalues:

**1. No q-th roots of f₁.**

The orbit {fₙ : n ∈ ℤ} has integer-indexed states. There is no f_{1/2} — no state whose compose-square is f₁. Without roots, eigenvalue 1/2 doesn't exist.

In the analytic model: f_{1/2}(x) = e^{x/2}, and (e^{x/2})² = e^x = f₁. The functional equation f(a+b) = f(a)·f(b) guarantees these roots exist.

**2. No rational scalar multiples.**

The eigenvalue theorem gives obs(fₙ) = n · fₙ where n · x means x ⊕ x ⊕ ... ⊕ x (n copies). For rational eigenvalues, we need (1/q) · x — the element y such that q · y = x. The ring has integer multiples but not division by integers.

---

## Part 2: A Key Lemma — Torsion-Freeness

Before adding new axioms, we derive a result that's already latent in the ℤ-level system.

### Statement

**Lemma (Torsion-free).** In a characteristic zero integral domain, if n · x = z for some n ≥ 1, then x = z. No non-zero element has finite additive order.

### Proof

First, observe that integer multiples factor through compose:

```
n · x = x ⊕ x ⊕ ... ⊕ x                                            [n copies]
      = compose(f₀, x) ⊕ compose(f₀, x) ⊕ ... ⊕ compose(f₀, x)    [A2: compose(f₀, x) = x]
      = compose(f₀ ⊕ f₀ ⊕ ... ⊕ f₀, x)                            [B2: distributivity]
      = compose(n · f₀, x)
```

So **n · x = compose(n · f₀, x)** for all n ≥ 1.

If n · x = z, then compose(n · f₀, x) = z.

By C3 (no zero divisors): n · f₀ = z or x = z.

By B5 (characteristic zero): n · f₀ ≠ z for n ≥ 1.

Therefore **x = z**. ∎

### Corollary: Uniqueness of ⊕-Division

If n · y₁ = a and n · y₂ = a, then:

```
n · (y₁ ⊕ ⊖y₂) = n · y₁ ⊕ n · (⊖y₂) = a ⊕ ⊖a = z
```

By torsion-freeness: y₁ ⊕ ⊖y₂ = z, so **y₁ = y₂**.

If a solution to n · y = a exists, it is **unique**. Division by n, when it exists, is well-defined.

---

## Part 3: New Axioms (D1-D2)

### D1. q-th roots of f₁ exist

```
∀ q ≥ 1,  ∃ f_{1/q} : State,  (f_{1/q})^q = f₁
```

where g^q denotes compose(g, g, ..., g) [q times].

The unit process has roots of every positive integer order. The q-th root is a "sub-unit" process: it takes q applications of compose to accumulate to one full unit.

In the analytic model: f_{1/q}(x) = e^{x/q}, and (e^{x/q})^q = e^x = f₁. ✓

**Computational reading:** The unit step can be subdivided into q equal sub-steps. Processes have arbitrary granularity.

### D2. Unique divisibility

```
∀ n ≥ 1,  ∀ a : State,  ∃ x : State,  n · x = a
```

For every positive integer n and every state a, there exists a state x such that n additive copies of x equal a. Combined with the uniqueness corollary above, this x is unique. We write (1/n) · a for this element.

This upgrades (State, ⊕, z) from a torsion-free abelian group to a **uniquely divisible** abelian group — equivalently, a ℚ-vector space. The ring (State, ⊕, compose) becomes a **ℚ-algebra**.

In the analytic model: for any function f and n ≥ 1, the function (1/n)·f exists (scalar division). ✓

**Computational reading:** Any process can be evenly partitioned into n identical sub-processes under ⊕.

---

## Part 4: Rational States and Eigenvalues

### Constructing f_{p/q}

For any rational p/q (with p ∈ ℤ, q ≥ 1), define:

```
f_{p/q} := (f_{1/q})^p
```

where negative powers use the compose-inverse: (f_{1/q})^{-1} exists because (f_{1/q})^q = f₁ and f₁ has compose-inverse f₁⁻¹, so (f_{1/q})^{-1} = (f_{1/q})^{q-1} · f₁⁻¹.

### Consistency: Well-Definedness

If p/q = r/s (same rational, different representation), then f_{p/q} = f_{r/s}.

Since p/q = r/s means ps = qr:

```
(f_{1/q})^p and (f_{1/s})^r
```

Need: (f_{1/q})^p = (f_{1/s})^r.

Both f_{1/q} and f_{1/s} are roots of f₁. We can relate them via f_{1/(qs)}, the qs-th root of f₁:

```
f_{1/q} = (f_{1/(qs)})^s         since ((f_{1/(qs)})^s)^q = (f_{1/(qs)})^{qs} = f₁
f_{1/s} = (f_{1/(qs)})^q         since ((f_{1/(qs)})^q)^s = (f_{1/(qs)})^{qs} = f₁
```

Then:

```
(f_{1/q})^p = ((f_{1/(qs)})^s)^p = (f_{1/(qs)})^{ps}
(f_{1/s})^r = ((f_{1/(qs)})^q)^r = (f_{1/(qs)})^{qr}
```

Since ps = qr, we have (f_{1/(qs)})^{ps} = (f_{1/(qs)})^{qr}. ✓

### The Functional Equation

**Theorem.** compose(f_{a/b}, f_{c/d}) = f_{a/b + c/d} for all rationals a/b, c/d.

**Proof.** Express in terms of a common root. Let g = f_{1/(bd)}. Then:

```
f_{a/b} = g^{ad}      and      f_{c/d} = g^{bc}

compose(f_{a/b}, f_{c/d}) = compose(g^{ad}, g^{bc})
                           = g^{ad + bc}
                           = f_{(ad + bc)/(bd)}
                           = f_{a/b + c/d}                             ∎
```

Addition of rationals is compose on the rational orbit. ✓

### Rational Arithmetic

```
ADDITION:        compose(f_{a/b}, f_{c/d}) = f_{a/b + c/d}
                 Compose of rational eigenfunctions = addition of rational eigenvalues

MULTIPLICATION:  (f_{a/b})^{c/d} = f_{ac/bd}
                 Compose-exponentiation = multiplication of rational eigenvalues
```

(The second equation uses fractional powers, which are defined via roots: (f_{a/b})^{1/d} is the d-th root of f_{a/b}.)

---

## Part 5: Eigenvalue Theorem for ℚ

### The Key Step: Eigenvalue of f_{1/q}

From the power rule (proved at ℤ level):

```
obs(g^q) = q · g^{q-1} · obs(g)
```

Apply to g = f_{1/q}, where g^q = f₁:

```
obs(f₁) = q · (f_{1/q})^{q-1} · obs(f_{1/q})
f₁ = q · (f_{1/q})^{q-1} · obs(f_{1/q})                              [A1: obs(f₁) = f₁]
```

Now, f₁ = (f_{1/q})^q = compose((f_{1/q})^{q-1}, f_{1/q}). So:

```
compose((f_{1/q})^{q-1}, f_{1/q}) = q · compose((f_{1/q})^{q-1}, obs(f_{1/q}))
```

Cancel (f_{1/q})^{q-1} (cancellation is a theorem, and (f_{1/q})^{q-1} ≠ z since (f_{1/q})^q = f₁ ≠ z and no zero divisors):

```
f_{1/q} = q · obs(f_{1/q})
```

By D2 (unique divisibility):

```
obs(f_{1/q}) = (1/q) · f_{1/q}                                        ∎
```

The q-th root of the unit process has eigenvalue 1/q.

### General Rational Eigenvalue

**Theorem.** For all p/q ∈ ℚ:

```
obs(f_{p/q}) = (p/q) · f_{p/q}
```

**Proof.** f_{p/q} = (f_{1/q})^p. Apply the power rule:

```
obs((f_{1/q})^p) = p · (f_{1/q})^{p-1} · obs(f_{1/q})
                 = p · (f_{1/q})^{p-1} · (1/q) · f_{1/q}
```

The scalar (1/q) commutes with compose (proven below):

```
                 = (1/q) · p · (f_{1/q})^{p-1} · f_{1/q}
                 = (1/q) · p · (f_{1/q})^p
                 = (p/q) · f_{p/q}                                     ∎
```

**Scalar-compose commutation:** compose(a, (1/q) · b) = (1/q) · compose(a, b).

Proof: Let y = (1/q) · b, so q · y = b. Then:

```
q · compose(a, y) = compose(a, q · y)                                  [distributivity]
                  = compose(a, b)
```

So compose(a, y) = (1/q) · compose(a, b) by uniqueness of ⊕-division. ✓

### The Full Eigenvalue Picture

```
obs(f₃)    = 3 · f₃           three copies (growth at rate 3)
obs(f₁)    = f₁               one copy (unit growth)
obs(f_{1/2}) = (1/2) · f_{1/2}  half a copy (half-rate growth)
obs(f₀)    = z                 zero copies (stasis)
obs(f_{-1/3}) = (-1/3) · f_{-1/3}  negative third of a copy (slow decay)
obs(f_{-2}) = (-2) · f_{-2}    negative two copies (decay at rate 2)
```

Every rational eigenvalue is realized. Observation reads it off.

---

## Part 6: What Fractions Mean

In Peano arithmetic, fractions are "parts of wholes" — an informal notion that requires careful formalization via equivalence classes of integer pairs.

In this framework, fractions have dynamical content:

| Rational | State | Dynamical meaning |
|---|---|---|
| 3 | f₃ = f₁³ | Three full units of growth per step |
| 1 | f₁ | One unit of growth per step |
| 1/2 | f_{1/2} = √f₁ | Half a unit — needs two steps to accumulate one full unit |
| 1/q | f_{1/q} | Sub-unit process — needs q steps to accumulate one unit |
| p/q | f_{p/q} = (f_{1/q})^p | p sub-units of granularity q |
| -1/3 | f_{-1/3} | Slow decay — needs three steps to lose one unit |

Fractions are **sub-unit growth rates**. The denominator is the granularity (how many steps to make a whole), the numerator is the intensity (how many sub-units per step), and the sign is the direction (growth or decay).

This is not a metaphor. It's the content of the eigenvalue equation obs(f_{p/q}) = (p/q) · f_{p/q}.

---

## Part 7: The Complete Axiom Set (ℚ Level)

### Primitives (4)

State, compose, obs, ⊕

### Axioms (16 + non-degeneracy)

**Process core (A1-A6):** Self-reproducing f₁, identity f₀, successor, bisimulation, assoc+comm, annihilator z.

**Semiring + observation (B1-B5):** Additive monoid, distributivity, obs(f₀) = z, Leibniz rule, characteristic zero.

**Ring + integral domain (C1-C3):** Compose-inverse of f₁, ⊕-inverses, no zero divisors.

**Rational extension (D1-D2):**

| # | Name | Statement |
|---|------|-----------|
| D1 | q-th roots | ∀q ≥ 1, ∃ f_{1/q}, (f_{1/q})^q = f₁ |
| D2 | Unique divisibility | ∀n ≥ 1, ∀a, ∃x, n · x = a |

**Non-degeneracy:** f₀ ≠ f₁ ≠ z pairwise distinct.

### Algebraic Structure

(State, ⊕, compose, z, f₀) is a **commutative ℚ-algebra of characteristic zero** (integral domain, uniquely divisible) with:
- a distinguished generator f₁ (invertible, with roots of all orders)
- a derivation obs satisfying obs(f₁) = f₁ and obs(f₀) = z

---

## Part 8: Derived Results Summary (Cumulative)

| Result | Level | Proof |
|---|---|---|
| Eigenvalue (ℕ): obs(fₙ) = n · fₙ | ℕ | Induction + Leibniz |
| A8 (infinite orbit) | ℕ | Eigenvalue + char. zero |
| Cancellation (was A7/B6) | ℤ | Integral domain |
| obs(f₁⁻¹) = ⊖f₁⁻¹ | ℤ | Leibniz on f₁ · f₁⁻¹ = f₀ |
| Eigenvalue (ℤ): obs(fₙ) = n · fₙ | ℤ | Downward induction |
| Power rule: obs(gⁿ) = n · gⁿ⁻¹ · obs(g) | ℤ | Induction + Leibniz |
| Torsion-free: n · x = z → x = z | ℤ | Char. zero + integral domain |
| Uniqueness of ⊕-division | ℤ | Torsion-free |
| Scalar-compose commutation | ℚ | Distributivity + unique divisibility |
| Functional equation: f_{a/b} · f_{c/d} = f_{a/b+c/d} | ℚ | Common root + associativity |
| obs(f_{1/q}) = (1/q) · f_{1/q} | ℚ | Power rule + cancellation + D2 |
| **Eigenvalue (ℚ): obs(f_{p/q}) = (p/q) · f_{p/q}** | ℚ | Power rule + scalar commutation |

---

## Part 9: The Path to ℝ

Everything needed for ℝ is now in place structurally. The remaining step:

### What ℝ Requires

**E1. Cauchy completeness.** Every Cauchy sequence {f_{rₙ}} of rational eigenstates (where {rₙ} is a Cauchy sequence of rationals) converges to a state f_α.

This is the same construction used in [extending-the-number-systems](extending-the-number-systems.md), now restated in the abstract framework:

1. ℚ is constructed (done — the orbit of f₀ under S, S⁻¹, and roots)
2. ℝ is the Cauchy completion of ℚ (using only ℚ and ℕ, both already built)
3. The eigenfunction f extends to ℝ by continuity (monotone on dense subset → unique continuous extension)
4. The eigenvalue theorem extends: obs(f_α) = α · f_α for all α ∈ ℝ

### What's Already Resolved

The circularity issue (ℝ defined via Taylor series which requires ℝ) was resolved in the earlier documents. f is determined on ℚ by the functional equation without referencing ℝ. The Cauchy completion uses only ℚ and ℕ. The Taylor series is a theorem about the completed f, not its definition.

### What's New

At the ℚ level, the abstract framework now has all the algebraic structure needed for the completion:
- Ordered field structure (from the integral domain + ordering on eigenvalues)
- Cauchy sequences (defined using ℚ-valued distances)
- The eigenvalue theorem extends by continuity

The ℝ document would formalize this as axiom E1 and prove the eigenvalue theorem for reals.

---

## Related

- [axioms](axioms.md)
- [integer-extension](integer-extension.md)
- [path-b-obs-structure](path-b-obs-structure.md)
- [extending-the-number-systems](extending-the-number-systems.md)
