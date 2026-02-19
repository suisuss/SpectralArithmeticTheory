# Spectral Arithmetic: Axioms

## Date: 2026-02-14

## Summary

Process-based axioms for the natural numbers and their extensions, stated without presupposing set theory, analysis, or arithmetic. Derived from the "Spectral Arithmetic" construction (numbers as eigenfunctions of differentiation), reformulated to eliminate circularity.

---

## Primitives

Three undefined terms:

- **State** — an uninterpreted type
- **compose**: State → State → State — how processes combine
- **obs**: State → State — what you read off (the abstract d/dx)

---

## Axioms

### A1. Self-reproducing process exists

There exists a state `f₁` such that `obs(f₁) = f₁`.

The observation of the unit process is itself. This is the abstract version of `f' = f` — stated in terms of observation on states rather than derivatives on real-valued functions.

In MLTT: `Σ (f₁ : State), obs f₁ = f₁`

**Note:** The annihilator z (A6) is also a fixed point of obs. A1 is distinguished from A6 by behavior under compose: f₁ generates successor (A3), z annihilates (A6).

### A2. Identity state exists

There exists a state `f₀` such that `compose(f₀, s) = s` for any state s.

The zero process — the multiplicative identity under composition. This is the "static one" (eigenvalue 0, constant, dead). As stated this is a left identity; commutativity of compose (A5) gives the right identity for free.

In MLTT: `Σ (f₀ : State), Π (s : State), compose f₀ s = s`

### A3. Successor

Define `S(s) = compose(f₁, s)`.

Successor is composition with the unit process. The natural numbers are the orbit of f₀ under S:

```
f₀, S(f₀), S(S(f₀)), S(S(S(f₀))), ...
```

This is a definition, not a claim. Given f₁ (A1) and compose (primitive), S is fully determined.

### A4. Observational separation

States s₁ and s₂ are equal if and only if no finite sequence of obs and compose operations distinguishes them.

This is bisimulation — identity defined by behavior, not by construction. The coalgebraic core: two states are the same iff no experiment can tell them apart.

**Why no scalars:** The original formulation used eigenvalue equations (`obs(s) = n · s`), which presuppose numbers. This restated version defines equality purely in terms of observation sequences, with no reference to arithmetic.

In MLTT: coinductive equality — equality defined by observations rather than by construction.

### A5. Compose is associative and commutative

- `compose(a, compose(b, c)) = compose(compose(a, b), c)`
- `compose(a, b) = compose(b, a)`

**Why not the functional equation:** The original formulation stated `compose(s_a, s_b) = s_{a+b}`, which presupposes addition and number-subscripted states. Instead, we axiomatize the structural properties of compose (associativity, commutativity) and *define* addition as what compose does on the orbit of f₀ under S. Addition is derived, not assumed.

### A6. Annihilator exists

There exists a state `z` such that `compose(z, s) = z` for any state s.

The zero state — absorbing element under composition. In the analytic model, this is the zero function: 0 · anything = 0. Also a fixed point of obs (obs(z) = z), but distinguished from f₁ by its annihilating behavior.

**z lives outside the number system.** The naturals are the orbit of f₀ under S. None of those are z. The annihilator is structural scaffolding, not a number.

### A7. Cancellation

`compose(f₁, a) = compose(f₁, b) → a = b`

f₁ is cancellable under compose. Equivalently: the successor function S is injective.

**Why this is needed:** Without cancellation, f₁ can be idempotent (compose(f₁, f₁) = f₁), collapsing the orbit to a finite set. See [pa-equiconsistency](pa-equiconsistency.md) Part 1 for the countermodel.

In the analytic model: eˣ · f = eˣ · g implies f = g because eˣ is everywhere positive (never zero).

### A8. Infinite orbit

`Sⁿ(f₀) ≠ f₀ for all n ≥ 1`

The orbit of f₀ under S does not cycle back. Equivalently: f₁ has infinite order in (State, compose, f₀).

**Why this is needed:** Without this, the orbit can have ℤ/kℤ structure (e.g., compose(f₁, f₁) = f₀ gives ℤ/2ℤ). See [pa-equiconsistency](pa-equiconsistency.md) Part 1 for the countermodel.

In the analytic model: eⁿˣ ≠ 1 for n ≥ 1, since eⁿˣ is strictly increasing.

### Non-degeneracy

`f₀ ≠ f₁ ≠ z`, and all three are pairwise distinct.

Prevents trivial one-element models where all distinguished states collapse.

---

## Distinguished States

| State | Axiom | Property | Analytic model | Role |
|-------|-------|----------|----------------|------|
| f₀ | A2 | compose(f₀, s) = s | e⁰ˣ = 1 | Identity (static one) |
| f₁ | A1 | obs(f₁) = f₁ | eˣ | Generator (dynamic one) |
| z | A6 | compose(z, s) = z | 0 | Annihilator (zero) |

Both f₁ and z are fixed points of obs. They are separated by their behavior under compose: f₁ generates, z annihilates.

---

## What Falls Out

From A1-A8, the following are **derived** (see [pa-equiconsistency](pa-equiconsistency.md) Part 3 for full proofs):

**Peano axioms (all derived):**
- P1: f₀ ∈ ℕ — by definition of ℕ as orbit of f₀ under S
- P2: S(n) ∈ ℕ whenever n ∈ ℕ — closure of orbit under S
- P3: f₀ is not a successor — from **A8** (Sⁿ⁺¹(f₀) ≠ f₀ for n ≥ 0)
- P4: S is injective — from **A7** (cancellation of f₁)
- P5: Induction — from ℕ defined as the **smallest** set containing f₀ and closed under S

**Arithmetic (all derived):**
- Addition := compose on ℕ (well-defined by induction)
- a + 0 = a — from A2 (identity) and A5 (commutativity)
- a + S(b) = S(a + b) — from A5 (associativity + commutativity)
- Multiplication defined by recursion: a · 0 = 0, a · S(b) = a · b + a (justified by P5)

**Equiconsistency:** Con(A1-A8) ↔ Con(PA). Proof in both directions.

**Number system extensions:**
- ℤ: introduce inverse of S (compose with inverse of f₁)
- ℚ: introduce roots of S
- ℝ: Cauchy completion of ℚ

---

## What's Been Done

1. **P3 and P4 cannot follow from A1-A6 alone** — countermodels exhibited (idempotent model, ℤ/2ℤ model)
2. **A7 (cancellation) and A8 (infinite orbit) added** — necessary and sufficient for PA
3. **All Peano axioms derived from A1-A8** — including arithmetic axioms for + and ·
4. **Equiconsistency with PA established** — Con(A1-A8) ↔ Con(PA)

See [pa-equiconsistency](pa-equiconsistency.md) for the complete proofs.

## What's Needed Next

1. **Path B: Make obs structural** — add axioms for obs-compose interaction so that A7 and A8 become derivable theorems rather than assumed axioms. The Leibniz rule introduces ⊕ (addition) as a second operation — the challenge is deriving ⊕ rather than importing it.
2. **Formalization in a proof assistant** (Lean 4, Coq, or Agda)
3. **Toward ZF** — extend to handle completed infinities, powerset as axiom, transfinite ordinals, replacement schema. Current system is PA-level; ZF is strictly stronger.
4. **Engagement with existing literature** — this is a special case of Lie theory (exponential map from Lie algebra to Lie group) and spectral theory (spectrum of self-adjoint operators on function spaces)

---

## Relationship to Existing Foundations

The construction is built on algebraic primitives (State, compose, obs, ⊕) and verified against Peano and ZF — all PA axioms are derived as theorems, and ZF axioms are verified under a predicate interpretation. The system is equiconsistent with both PA and ZF: it proves the same theorems, not more.

| Foundation | Primitives | Relationship to this construction |
|-----------|-----------|-------------------|
| ZF | set, ∈ | Equiconsistent — sets emulated as predicates, ZF axioms verified under interpretation |
| Peano | zero, successor | Equiconsistent — all PA axioms derived as theorems |
| Lambda calculus | function, application | Language layer (retained for logic: AND, OR, NOT) |
| Coalgebra | state, observation | Core framework — the primitives |
| MLTT | type, term, judgment | Formalization target |

---

## Related

- [spectral-arithmetic-complete](spectral-arithmetic-complete.md)