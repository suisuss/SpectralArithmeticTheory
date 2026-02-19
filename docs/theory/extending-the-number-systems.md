# Extending the Number Systems: From ℕ to ℝ via Eigenvalues

## The Standard Chain

In conventional mathematics, each number system requires a separate construction:

```
ℕ (Peano axioms) → ℤ (additive inverses) → ℚ (multiplicative inverses) → ℝ (Dedekind cuts / Cauchy sequences)
```

Each extension introduces new axioms and new justification for why the new numbers should exist.

## The Eigenfunction Alternative

In the spectral arithmetic framework, all number systems live in the same space: the eigenvalue spectrum of d/dx acting on {f(αx) : α ∈ ℝ}, where f is defined by f' = f, f(0) = 1.

The numbers differ only in how you **reach** them.

## The Natural Numbers: Iterating the Successor

Already established in [set-constructor-and-deriving-e](set-constructor-and-deriving-e.md).

```
f₀(x) = 1           eigenvalue: 0    (the dead process)
f₁(x) = f(x)        eigenvalue: 1    (the unit process)
fₖ(x) = f₁ · fₖ₋₁   eigenvalue: k    (successor applied k times)
```

**Operation required:** Successor S(g) = f₁ · g

**What you can reach:** {0, 1, 2, 3, ...} = ℕ₀

## The Integers: The Inverse Successor

### Construction

The successor S(g) = f₁ · g has a natural inverse:

```
S⁻¹(g) = g / f₁ = g · f₁⁻¹
```

Since f₁(x) = f(x), the inverse is f₁⁻¹(x) = 1/f(x) = f(-x). This works because:

```
f(x) · f(-x) = f(x + (-x)) = f(0) = 1
```

The functional equation f(a+b) = f(a)·f(b) guarantees that f(-x) is the multiplicative inverse of f(x).

### Applying S⁻¹ Past Zero

```
S⁻¹(f₀) = f(0·x) · f(-x) = 1 · f(-x) = f(-1·x) = f₋₁     eigenvalue: -1
S⁻¹(f₋₁) = f(-1·x) · f(-x) = f(-2·x) = f₋₂                eigenvalue: -2
S⁻¹(f₋₂) = f(-2·x) · f(-x) = f(-3·x) = f₋₃                eigenvalue: -3
```

### Dynamical Meaning

Negative eigenvalues correspond to **decay**:

| Eigenvalue | Function | Behaviour |
|---|---|---|
| 3 | f(3x) = e³ˣ | Growth at rate 3 |
| 1 | f(x) = eˣ | Unit growth |
| 0 | f(0) = 1 | Stasis |
| -1 | f(-x) = e⁻ˣ | Unit decay |
| -3 | f(-3x) = e⁻³ˣ | Decay at rate 3 |

The sign of a number is not an abstract label. It is the **direction of the process**: growth (positive) or decay (negative). Zero is the boundary — the process that neither grows nor decays.

**Operations required:** S and S⁻¹

**What you can reach:** {..., -3, -2, -1, 0, 1, 2, 3, ...} = ℤ

## The Rationals: Roots of the Successor

### The Question

Can we reach eigenvalue ½? That would be a function f₁/₂ such that:

```
d/dx f₁/₂(x) = ½ · f₁/₂(x)
```

And crucially, it should relate to f₁ by:

```
f₁/₂ · f₁/₂ = f₁
```

The half-eigenfunction, applied twice via the successor's multiplication, yields the unit eigenfunction.

### The Answer

The functional equation f(a+b) = f(a)·f(b) guarantees this. Set a = b = x/2:

```
f(x/2) · f(x/2) = f(x/2 + x/2) = f(x) = f₁(x)
```

So f₁/₂(x) = f(x/2). Verify the eigenvalue:

```
d/dx f(x/2) = ½ · f'(x/2) = ½ · f(x/2)    ✓    eigenvalue: ½
```

### General Rationals

For any rational p/q (where q ≠ 0):

```
f_{p/q}(x) = f(px/q)
```

**Eigenvalue check:**

```
d/dx f(px/q) = (p/q) · f'(px/q) = (p/q) · f(px/q)    ✓    eigenvalue: p/q
```

**Root property:** The q-th root of fₚ is f_{p/q}, because:

```
[f(px/q)]^q = f(px/q + px/q + ... + px/q)    [q times]
            = f(q · px/q)
            = f(px)
            = fₚ(x)    ✓
```

### What This Means

Rational numbers emerge from asking: **what are the roots of the successor operation?**

If applying S exactly q times gives you fₚ, then the starting point must be f_{p/q}. The functional equation f(a+b) = f(a)·f(b) — which follows from f' = f — guarantees these intermediate eigenfunctions exist without any new axioms.

Fractions are not "parts of wholes" in this framework. They are **sub-unit growth rates** — processes that need multiple applications to accumulate to a whole eigenvalue.

**Operations required:** S, S⁻¹, and q-th roots

**What you can reach:** ℚ

## The Reals: Completion of the Rationals

### The Circularity Problem (Now Resolved)

An earlier version of this theory defined f via the Taylor series f(x) = Σₙ₌₀^∞ xⁿ/n!. This was circular: the series requires convergence in ℝ, but ℝ is what we're trying to construct.

The fix: **f does not need the Taylor series.** The ODE f' = f with f(0) = 1, combined with the functional equation f(a+b) = f(a)·f(b), determines f at every rational point. The reals are then constructed as the completion of ℚ using only rational machinery. The Taylor series becomes a theorem about f, not its definition.

### Step 1: f Is Fully Determined on ℚ Without ℝ

The functional equation f(a+b) = f(a)·f(b) and f(0) = 1 give us:

**At the naturals:**
```
f(n) = f(1)ⁿ = eⁿ     for all n ∈ ℕ
```
where e := f(1) is simply named, not computed via infinite series.

**At the integers:**
```
f(n)·f(-n) = f(0) = 1
f(-n) = e⁻ⁿ            for all n ∈ ℤ
```

**At the rationals:**
```
f(1/q)^q = f(q·(1/q)) = f(1) = e
f(1/q) = e^(1/q)        (unique positive q-th root)
f(p/q) = f(1/q)^p = e^(p/q)   for all p/q ∈ ℚ
```

No infinite series. No limits. No ℝ. Only the functional equation and the integers (already constructed).

### Step 2: Establish Properties of f on ℚ

From f' = f and f(0) = 1, we can prove — restricted to rational arguments:

1. **f(x) > 0 for all x ∈ ℚ** — since f(x) = f(x/2)·f(x/2) = [f(x/2)]² ≥ 0, and f is never zero (if f(a) = 0 then f(a+b) = f(a)·f(b) = 0 for all b, contradicting f(0) = 1).

2. **f is strictly increasing on ℚ** — since f' = f > 0, the function grows wherever it's defined.

3. **e > 2** — provable: f(1) = f(½)·f(½) and f(½) > 1 (since f is increasing and f(0) = 1), so f(1) > 1² = 1. More precisely, f(1) = f(½)² > f(¼)⁴ > ... which gives e > 2 by induction on the dyadic rationals.

4. **e < 3** — provable from the functional equation and bounding arguments on ℚ alone.

These properties hold without ever referencing ℝ.

### Step 3: Construct ℝ as Completion of ℚ

A real number α is defined as an equivalence class of **Cauchy sequences of rationals**:

A sequence {rₙ} where rₙ = pₙ/qₙ ∈ ℚ is Cauchy if: for every rational ε > 0, there exists N ∈ ℕ such that for all m, n > N:

```
|rₘ - rₙ| < ε
```

Two Cauchy sequences are equivalent if their difference converges to 0. The set of equivalence classes is ℝ.

**This construction uses only ℚ (already built) and ℕ (already built).** No external ℝ is imported.

### Step 4: Extend f to ℝ by Continuity

f is monotone increasing on ℚ and ℚ is dense in ℝ (by construction). A monotone function defined on a dense subset has a **unique continuous extension** to the completion.

For any real α, represented by Cauchy sequence {pₙ/qₙ}:

```
f(αx) := lim_{n→∞} f(pₙx/qₙ)
```

This limit exists because:
- f is monotone (so the sequence f(pₙx/qₙ) is eventually monotone)
- f is bounded on bounded rational intervals (provable from the functional equation)
- Monotone bounded sequences converge (a property of the completion)

The extension preserves:
- The functional equation: f(α+β) = f(α)·f(β) for all real α, β
- The eigenvalue property: d/dx f(αx) = α·f(αx)
- The ODE: f' = f

### Step 5: The Taylor Series Is Now a Theorem

With f defined on all of ℝ by continuous extension, we can **prove**:

```
f(x) = Σₙ₌₀^∞ xⁿ/n!
```

This follows from f⁽ⁿ⁾(0) = 1 for all n (since f' = f implies every derivative at 0 equals f(0) = 1) and Taylor's theorem with remainder (which can now be applied since we have ℝ).

The Taylor series is a **consequence** of the construction, not its foundation.

### The Corrected Logical Order

```
WRONG:   Taylor series (needs ℝ) → define f → derive properties → construct ℝ (circular!)

RIGHT:   1. Define f by ODE: f' = f, f(0) = 1
         2. Derive functional equation: f(a+b) = f(a)·f(b)
         3. Determine f on ℕ: f(n) = eⁿ where e := f(1)
         4. Determine f on ℤ: f(-n) = e⁻ⁿ via functional equation
         5. Determine f on ℚ: f(p/q) = e^(p/q) via roots
         6. Construct ℝ as Cauchy completion of ℚ (using only ℚ and ℕ)
         7. Extend f to ℝ by continuity (monotone + dense domain)
         8. PROVE Taylor series as theorem about the completed f
```

No step uses anything not yet constructed. The circularity is eliminated.

### Irrational Eigenfunctions

With f now defined on all of ℝ, irrational eigenvalues exist:

```
f_{√2}(x) = f(√2·x)     eigenvalue: √2     (√2 exists as Cauchy limit of rationals)
f_{π}(x)  = f(π·x)       eigenvalue: π      (π exists as Cauchy limit of rationals)
f_{e}(x)  = f(e·x)       eigenvalue: e      (e = f(1), already defined)
```

These aren't reachable by finite application of S, S⁻¹, and roots. They are limits of rational eigenfunctions — filled in by the completion.

**Operations required:** Cauchy completion of rational eigenvalues

**What you can reach:** ℝ

## Summary: The Hierarchy of Reachability

| Number system | Operations | Meaning |
|---|---|---|
| ℕ | Successor S | Iterating unit growth |
| ℤ | S and S⁻¹ | Growth and decay |
| ℚ | S, S⁻¹, roots | Sub-unit growth rates |
| ℝ | S, S⁻¹, roots, limits | The full continuous spectrum |

The number systems are not separate constructions. They are **concentric circles of accessibility** within a single space — the eigenvalue spectrum of the differentiation operator.

Each extension adds one more operation:
- **ℕ → ℤ:** Allow the inverse (decay)
- **ℤ → ℚ:** Allow roots (fractional rates)
- **ℚ → ℝ:** Allow limits (filling the gaps)

## The Unifying Structure

```
SPACE:       Eigenfunctions of d/dx
ELEMENTS:    {f(αx) : α ∈ ℝ} where f' = f, f(0) = 1
READOUT:     d/dx f(αx) = α · f(αx), eigenvalue α recovers the number
SUCCESSOR:   S(g) = f₁ · g (adds 1 to eigenvalue)
INVERSE:     S⁻¹(g) = g / f₁ (subtracts 1 from eigenvalue)
ROOTS:       f_{p/q} = f(px/q), the q-th root of fₚ
ARITHMETIC:  f_a · f_b = f_{a+b}   (multiplication of functions = addition of eigenvalues)
             (f_a)^b = f_{ab}      (exponentiation of functions = multiplication of eigenvalues)
```

---

## Related

- [spectral-arithmetic](spectral-arithmetic.md)
- [set-constructor-and-deriving-e](set-constructor-and-deriving-e.md)
- [eulers-number-and-differentials](eulers-number-and-differentials.md)
