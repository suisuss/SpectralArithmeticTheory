# PA-Equiconsistency of Spectral Arithmetic

## Date: 2026-02-14

## Summary

We show that axioms A1-A6 (as stated in [axioms](axioms.md)) are **insufficient** to derive the Peano axioms. We identify two countermodels exposing the gaps, introduce two additional axioms (A7, A8), and prove:

1. **PA is derivable from A1-A8** — all Peano axioms including the arithmetic axioms for + and ·
2. **A1-A8 has a model inside PA** — the additive monoid ℕ ∪ {∞}
3. **Therefore A1-A8 is equiconsistent with PA** — each is consistent iff the other is

---

## Part 1: A1-A6 Are Insufficient

### Countermodel for P4 (Injectivity of S)

P4 requires: S(a) = S(b) → a = b, i.e., compose(f₁, a) = compose(f₁, b) → a = b.

This is **cancellation** of f₁ in the monoid (State, compose). Commutative monoids do not guarantee cancellation. Countermodel:

```
State = {f₀, f₁, z}
compose(f₀, x) = x           (A2: identity)
compose(f₁, f₀) = f₁         (by identity + commutativity)
compose(f₁, f₁) = f₁         (IDEMPOTENT — the collapse)
compose(z, x)   = z           (A6: annihilator)
obs(f₁) = f₁                 (A1)
obs(z)  = z
obs(f₀) = z
```

Verification: A1 ✓, A2 ✓, A5 ✓ (check all 27 triples for associativity), A6 ✓, non-degeneracy ✓.

But S(f₀) = f₁ and S(f₁) = f₁, so S(f₀) = S(f₁) while f₀ ≠ f₁. **S is not injective.** The orbit collapses: ℕ = {f₀, f₁}, a two-element "number system."

### Countermodel for P3 (f₀ is not a successor)

P3 requires: there is no s ∈ ℕ with S(s) = f₀.

Nothing in A1-A6 prevents the orbit from cycling. Countermodel:

```
State = {f₀, f₁, z}
compose(f₀, x) = x
compose(f₁, f₀) = f₁
compose(f₁, f₁) = f₀         (CYCLING — f₁ is its own inverse)
compose(z, x)   = z
obs, non-degeneracy as above
```

This is the group ℤ/2ℤ with an absorbing element adjoined. S(f₁) = compose(f₁, f₁) = f₀, so **f₀ is a successor of f₁**. The orbit cycles: f₀, f₁, f₀, f₁, ...

### Diagnosis

A1-A6 define a commutative monoid with identity and annihilator. Two properties are missing:

1. **Cancellation** — f₁ must not be idempotent or a zero divisor
2. **Infinite orbit** — the orbit of f₀ under S must not cycle back

---

## Part 2: The Augmented Axioms (A1-A8)

### Existing Axioms (unchanged)

- **A1.** ∃ f₁ : State, obs(f₁) = f₁
- **A2.** ∃ f₀ : State, ∀s, compose(f₀, s) = s
- **A3.** S(s) := compose(f₁, s)
- **A4.** Observational separation (bisimulation)
- **A5.** compose is associative and commutative
- **A6.** ∃ z : State, ∀s, compose(z, s) = z
- **Non-degeneracy:** f₀ ≠ f₁ ≠ z pairwise distinct

### New Axioms

**A7. Cancellation.**

```
∀ a b : State,  compose(f₁, a) = compose(f₁, b)  →  a = b
```

f₁ is cancellable under compose. Equivalently: the successor function S is injective.

In the analytic model: e^x · f = e^x · g implies f = g because e^x is never zero.

**A8. Infinite orbit.**

```
∀ n ≥ 1,  Sⁿ(f₀) ≠ f₀
```

The orbit of f₀ under S does not cycle. Equivalently: f₁ has infinite order in (State, compose, f₀).

In the analytic model: e^(nx) ≠ 1 for n ≥ 1 because e^(nx) is strictly increasing for n > 0.

### Why These Are Necessary and Sufficient

**Necessary:** The countermodels above satisfy A1-A6 but violate P4 (without A7) and P3 (without A8). No proof of P3 or P4 from A1-A6 alone is possible — the countermodels are witnesses.

**Sufficient:** See Part 3.

### Analytic Model Check

The standard analytic model (State = smooth functions, compose = pointwise multiplication, obs = d/dx) satisfies A7 and A8:

- **A7:** e^x · f = e^x · g implies f = g (divide by e^x, which is everywhere positive). ✓
- **A8:** e^(nx) = 1 for all x would require n = 0. For n ≥ 1, e^(nx) is non-constant. ✓

---

## Part 3: Derivation of PA from A1-A8

### Setup

Define:
- **ℕ** := the smallest set containing f₀ and closed under S (inductive definition)
- **0** := f₀
- **S** := compose(f₁, -)
- **+** := compose restricted to ℕ × ℕ (we verify this is well-defined below)

Elements of ℕ: f₀, S(f₀), S²(f₀), S³(f₀), ... Written as f₁⁰, f₁¹, f₁², f₁³, ... where f₁⁰ := f₀ and f₁ⁿ := compose(f₁, f₁ⁿ⁻¹).

### PA Axiom 1: 0 ∈ ℕ

f₀ ∈ ℕ by definition (it's the starting element of the orbit). ∎

### PA Axiom 2: ∀n ∈ ℕ, S(n) ∈ ℕ

If n ∈ ℕ then S(n) = compose(f₁, n) ∈ ℕ by closure of the orbit under S. ∎

### PA Axiom 3: ∀n ∈ ℕ, S(n) ≠ 0

We need: compose(f₁, Sⁿ(f₀)) ≠ f₀ for all n ≥ 0.

compose(f₁, Sⁿ(f₀)) = Sⁿ⁺¹(f₀).

By **A8**, Sᵐ(f₀) ≠ f₀ for all m ≥ 1. Since n+1 ≥ 1, we have Sⁿ⁺¹(f₀) ≠ f₀. ∎

### PA Axiom 4: ∀a,b ∈ ℕ, S(a) = S(b) → a = b

S(a) = S(b) means compose(f₁, a) = compose(f₁, b). By **A7** (cancellation), a = b. ∎

### PA Axiom 5: Induction Schema

Let P be a property of elements of ℕ. Suppose P(f₀) and ∀n(P(n) → P(S(n))).

ℕ is defined as the **smallest** set containing f₀ and closed under S. The set {n ∈ ℕ : P(n)} contains f₀ and is closed under S, so it equals ℕ by minimality. Therefore P holds for all n ∈ ℕ. ∎

### PA Axiom 6: ∀a, a + 0 = a

a + 0 = compose(a, f₀) = a by **A2** (f₀ is identity) and **A5** (commutativity). ∎

### PA Axiom 7: ∀a,b, a + S(b) = S(a + b)

```
a + S(b) = compose(a, compose(f₁, b))       (definition of + and S)
         = compose(compose(a, f₁), b)        (A5: associativity)
         = compose(compose(f₁, a), b)        (A5: commutativity)
         = compose(f₁, compose(a, b))        (A5: associativity)
         = S(a + b)                           (definition of S)    ∎
```

### PA Axiom 8: ∀a, a · 0 = 0

Multiplication is defined by recursion on ℕ (justified by induction, PA5):

```
a · 0     := f₀
a · S(b)  := (a · b) + a
```

Then a · 0 = f₀ = 0 by definition. ∎

### PA Axiom 9: ∀a,b, a · S(b) = a · b + a

By definition of ·. ∎

### Well-definedness of + on ℕ

We need: if a, b ∈ ℕ then compose(a, b) ∈ ℕ.

By induction on b. Base: compose(a, f₀) = a ∈ ℕ. Step: compose(a, S(b)) = S(compose(a, b)) ∈ ℕ by closure under S and induction hypothesis. ∎

### Result

**All nine PA axioms are derivable from A1-A8.** The orbit of f₀ under S, with compose as addition and recursively-defined multiplication, is a model of Peano Arithmetic.

---

## Part 4: Model of A1-A8 Inside PA

### Construction

Working inside PA (so ℕ with 0, S, +, · is given), define:

```
State  := ℕ ∪ {∞}              (adjoin one extra element)
f₀     := 0
f₁     := 1
z      := ∞
compose(a, b) := a + b          for a, b ∈ ℕ
compose(∞, s) := ∞              for any s
compose(s, ∞) := ∞              for any s
obs    := identity function     (obs(s) = s for all s)
```

### Verification

| Axiom | Check | |
|-------|-------|-|
| A1 | obs(1) = 1 | ✓ |
| A2 | compose(0, s) = 0 + s = s | ✓ |
| A3 | S(s) = compose(1, s) = 1 + s = s + 1 | ✓ (matches PA successor) |
| A4 | obs = id, so distinct states are trivially separated | ✓ |
| A5 | + is assoc. and comm. in PA | ✓ |
| A6 | compose(∞, s) = ∞ | ✓ |
| A7 | 1 + a = 1 + b → a = b (cancellation in PA) | ✓ |
| A8 | Sⁿ(0) = n ≠ 0 for n ≥ 1 | ✓ |
| Non-deg. | 0 ≠ 1 ≠ ∞ | ✓ |

### Result

**A1-A8 has a model constructible inside PA.** If PA is consistent, so is A1-A8.

### Note on obs

The model uses obs = identity, which is degenerate — obs does no structural work. This is sufficient for consistency but means A4 (observational separation) is trivially satisfied. A richer model where obs does real work would use the analytic model (obs = d/dx), but that requires analysis, not just PA. This motivates Path B.

---

## Part 5: Equiconsistency Theorem

**Theorem.** A1-A8 is equiconsistent with PA.

**Proof.**

(→) Suppose A1-A8 is consistent, i.e., has a model M. In M, the orbit of f₀ under S satisfies all PA axioms (Part 3). So PA has a model. So PA is consistent.

(←) Suppose PA is consistent, i.e., has a model. Inside that model, construct (State, compose, obs, f₀, f₁, z) as in Part 4. This satisfies A1-A8. So A1-A8 has a model. So A1-A8 is consistent.

Therefore: Con(PA) ↔ Con(A1-A8). ∎

---

## Part 6: On ZF Equivalence

### PA ≠ ZF

PA and ZF are **not** equiconsistent. ZF is strictly stronger:

- Con(ZF) → Con(PA), but NOT Con(PA) → Con(ZF)
- ZF proves Con(PA) (Gentzen's theorem is formalizable in much less than ZF)
- ZF handles infinite sets, powerset, transfinite induction — PA does not

The current axiom system A1-A8 is at the **PA level**. It handles:
- ✓ Natural numbers and arithmetic
- ✓ Induction
- ✓ Recursive definitions (+, ·)

It does **not** handle:
- ✗ Infinite sets as objects (only finite predicate-based sets from Part 6 of the complete document)
- ✗ Powerset as an axiom (2^|S| is computed, not axiomatized)
- ✗ Transfinite ordinals (ω, ω+1, ...)
- ✗ Axiom of Choice
- ✗ Replacement schema
- ✗ The continuum hypothesis question

### What ZF-Equivalence Would Require

To reach ZF, the axiom system would need to be extended with:

1. **An axiom of infinity** — asserting ℕ (the orbit) exists as a completed totality, not just a generation procedure. PA has induction but not the set ℕ as an object.

2. **A powerset axiom** — the predicate-based powerset from Part 8 of the complete document works for finite sets, but needs to be axiomatized for infinite sets. Something like: "For any predicate P over a state-set S, the collection of all sub-predicates exists as a state-set."

3. **Axiom of replacement** — if f is a definable function and S is a state-set, then {f(s) : s ∈ S} is a state-set.

4. **Handling transfinite ordinals** — the orbit of f₀ under S gives ω (the first limit ordinal). But ω + 1, ω + ω, ε₀, etc. require successor and limit operations on ordinals, which the current framework doesn't address.

This is a substantially larger project. The recommended path:

```
DONE:    A1-A8 ≡ PA  (this document)
NEXT:    Path B — make obs do structural work
THEN:    Second-order arithmetic (PA₂) — intermediate strength
LATER:   ZF-level axiomatization
```

### Honest Assessment

Reaching ZF equivalence requires the framework to handle objects that the current process-based ontology hasn't addressed: completed infinities, arbitrary set-sized collections, and ordinal arithmetic beyond ω. These are not insurmountable, but they're not straightforward extensions of the eigenfunction idea either. The powerset section (Part 8) is suggestive but informal — it computes |P(S)| = 2^|S| without axiomatizing what it means for P(S) to exist as an object in the theory.

---

## Part 7: Status and Next Steps

### Established

- [x] A1-A6 are insufficient for PA (countermodels exhibited)
- [x] A7 (cancellation) and A8 (infinite orbit) are necessary
- [x] A1-A8 derive all PA axioms (P1-P5, arithmetic axioms for +, recursive definition of ·)
- [x] A1-A8 has a model in PA
- [x] **Equiconsistency: Con(A1-A8) ↔ Con(PA)**

### Next: Path B — Making obs Structural

The PA-model uses obs = identity (degenerate). The analytic model uses obs = d/dx (rich). Path B asks: can we add axioms governing how obs interacts with compose, such that:

1. obs does real work (distinguishes Sⁿ(f₀) from Sᵐ(f₀) via observation, not just by axiom)
2. A7 and A8 become **theorems** rather than axioms — derived from the obs interaction
3. The eigenvalue structure (obs(fₙ) = "n · fₙ" in some abstract sense) emerges from the axioms

The challenge: the Leibniz rule obs(compose(a,b)) = compose(obs(a), b) ⊕ compose(a, obs(b)) introduces a second binary operation ⊕, which should be **derivable as addition** rather than imported. This is the key technical problem for Path B.

### Later: Toward ZF

Extend the axiom system to handle:
- Completed infinities (ℕ as an object, not just a generation rule)
- Powerset as axiom
- Transfinite ordinals
- Replacement

---

## Related

- [axioms](axioms.md)
- [spectral-arithmetic-complete](spectral-arithmetic-complete.md)
