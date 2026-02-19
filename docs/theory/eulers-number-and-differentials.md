# Euler's Number and Differentials

## The Eigenfunction Story

From finite differences, we know Δ reduces polynomial degree by 1. Apply Δ enough times to any polynomial and you kill it — Δ^(d+1) of a degree-d polynomial is 0. Polynomials are **mortal** under Δ.

**Question:** Is there a function that Δ can never kill? A function where applying Δ just gives you back the same function (possibly scaled)?

Try f(n) = aⁿ for some base a:

```
Δ(aⁿ) = a^(n+1) - aⁿ = aⁿ(a - 1)
```

So **Δ(aⁿ) = (a-1) · aⁿ**. The exponential is an **eigenfunction** of Δ — applying the operator just scales it by (a-1). No matter how many times you apply Δ, you never kill it. Exponentials are **immortal** under differencing.

In programming terms: polynomials are like data structures that get consumed by Δ. Exponentials are like generators — Δ produces a copy of the original.

## Moving to the Continuous Case

The finite difference / derivative analogy:

| Discrete | Continuous |
|----------|-----------|
| Δf(n) = f(n+1) - f(n) | f'(x) = lim[h→0] (f(x+h) - f(x))/h |

In the continuous case, the same eigenfunction question applies. For f(x) = aˣ:

```
d/dx(aˣ) = ln(a) · aˣ
```

The continuous derivative of an exponential is the exponential scaled by **ln(a)** (instead of (a-1) in the discrete case).

## Where *e* Enters

In the discrete world: **what base gives eigenvalue 1?** That is, what a makes Δ(aⁿ) = 1 · aⁿ?

```
a - 1 = 1  →  a = 2
```

So **2ⁿ is its own discrete difference.** It's the "discrete *e*."

In the continuous world: **what base gives eigenvalue 1 under d/dx?**

```
ln(a) = 1  →  a = e
```

**e is the unique base such that eˣ is its own derivative.** That's its defining property: d/dx(eˣ) = eˣ.

## The Bridge: Step Size Shrinks to Zero

Suppose instead of step size 1, you use step size h:

```
Δₕf(x) = (f(x+h) - f(x)) / h
```

You want Δₕf = f, so for f(x) = aˣ:

```
aˣ(aʰ - 1)/h = aˣ
(aʰ - 1)/h = 1
aʰ = 1 + h
a = (1 + h)^(1/h)
```

As h → 0:

**e = lim(h→0) (1 + h)^(1/h)**

That's the classical definition of *e*. It falls straight out of asking: "what base makes the eigenvalue exactly 1 as step size becomes infinitesimal?"

Equivalently, with n = 1/h:

**e = lim(n→∞) (1 + 1/n)ⁿ ≈ 2.71828...**

## Framework Summary

| Level | Insight |
|-------|---------|
| **L1 (Identification)** | e ≈ 2.71828, base of natural logarithm |
| **L2 (Axiomatization)** | d/dx(eˣ) = eˣ — the eigenvalue-1 property |
| **L3 (Evaluation)** | e = lim(1 + 1/n)ⁿ, computable from the discrete-to-continuous bridge |
| **L4 (Abstraction)** | Exponentials are eigenfunctions of difference/derivative operators. *e* is the base where the eigenvalue is 1 under d/dx |
| **L5 (Transportation)** | Same structure appears in compound interest (finance), radioactive decay (physics), population growth (biology) — anywhere the rate of change is proportional to the current value |

## How It Relates to Differentials

The differential equation **dy/dx = y** (rate of change equals current value) has the solution **y = Ceˣ**. This is the continuous version of the discrete recurrence f(n+1) = 2f(n) giving f(n) = C·2ⁿ.

The entire calculus of differentials is built on the fact that eˣ is the fixed point of differentiation. Every other exponential aˣ can be rewritten as e^(x·ln(a)), so *e* is the natural unit for measuring continuous growth, the same way 2 is the natural unit for discrete doubling.

---

## Related

- [spectral-arithmetic](spectral-arithmetic.md)
- [set-constructor-and-deriving-e](set-constructor-and-deriving-e.md)
