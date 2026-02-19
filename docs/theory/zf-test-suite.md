# ZF Test Suite: Verifying Set-Theoretic Axioms in the Process Framework

## Date: 2026-02-14

## Summary

The framework is PA-equiconsistent (proved in [pa-equiconsistency](pa-equiconsistency.md)) and extends through ℝ. ZF is the next test suite — strictly stronger than PA. This document systematically tests each ZF axiom against the process-based framework.

**Setup:** Sets are predicates (characteristic functions) mapping states to {f₀, f₁}. Membership is predicate application: x ∈ S iff S(x) = f₁. Set operations are Church boolean composition (already established in [spectral-arithmetic-complete](spectral-arithmetic-complete.md), Parts 6-8).

**Results:**

| # | Axiom | Status | Mechanism |
|---|-------|--------|-----------|
| ZF1 | Extensionality | **PASS** | Definitional — predicates equal iff they agree on all inputs |
| ZF2 | Empty Set | **PASS** | λx.f₀ — the always-false predicate |
| ZF3 | Pairing | **PASS** | Equality predicate on eigenstates via eigenvalue comparison |
| ZF4 | Union | **PASS** (finite); **CONDITIONAL** (infinite) | OR-composition; infinite case needs bounded quantification |
| ZF5 | Power Set | **PASS** (finite); **REQUIRES F1** (infinite) | 2^n computed; infinite case needs second-order comprehension |
| ZF6 | Infinity | **PASS** with **F1** | ℕ-orbit as completed totality |
| ZF7 | Separation | **PASS** | AND-composition of predicates |
| ZF8 | Replacement | **CONDITIONAL** | Requires definable functions; passes for eigenstate-definable maps |
| ZF9 | Foundation | **PASS** | Type stratification prevents self-membership |
| ZF10 | Choice | **INDEPENDENT** | Same status as in ZF — neither provable nor refutable |

**Bottom line:** 6 axioms pass outright. 3 require new axioms (F1-F3) to handle infinite collections as completed objects. 1 is independent (same as in ZF). With F1-F3, the framework emulates ZF.

---

## Part 1: The Interpretation

### Sets in the Framework

A **set** is a predicate — a function from states to the boolean eigenstates:

```
S : State → {f₀, f₁}
```

- x ∈ S  :⟺  S(x) = f₁  (present)
- x ∉ S  :⟺  S(x) = f₀  (absent)

### Membership

Membership is predicate application. This is not an encoding trick — it's the Church/Curry tradition: a set IS its characteristic function. The set {2, 5, 7} is the function that returns f₁ on f₂, f₅, f₇ and f₀ on everything else.

### Set Operations (Already Established)

From [spectral-arithmetic-complete](spectral-arithmetic-complete.md) Part 6:

```
UNION(A, B)        := λx. OR(A(x), B(x))
INTERSECTION(A, B) := λx. AND(A(x), B(x))
COMPLEMENT(A)      := λx. NOT(A(x))
DIFFERENCE(A, B)   := λx. AND(A(x), NOT(B(x)))
```

Where AND, OR, NOT are Church boolean combinators.

### The Type Structure

The framework has a natural type stratification:

```
Level 0:  States (elements of State — the eigenstates f_α)
Level 1:  Predicates over states (State → {f₀, f₁}) — "sets of states"
Level 2:  Predicates over predicates — "sets of sets"
Level 3:  ...
```

This stratification is crucial for Foundation (ZF9) and for understanding the limitations at each level.

---

## Part 2: ZF1 — Extensionality

### Statement

```
∀A ∀B (∀x (x ∈ A ↔ x ∈ B) → A = B)
```

Two sets are equal if and only if they have the same members.

### Verification

Sets are predicates. Two predicates A and B are extensionally equal iff they return the same value on every input:

```
A = B  :⟺  ∀x : State,  A(x) = B(x)
```

This is the definition of function equality. Extensionality is not an axiom here — it's **definitional**. There is no way for two predicates to have the same membership and be different, because predicates ARE their membership functions.

In the abstract framework, this connects to **bisimulation (A4)**: states (and by extension, predicates on states) are equal iff no observation distinguishes them. Two predicates that agree on all inputs are indistinguishable under any observation.

**Status: PASS** — definitional.

---

## Part 3: ZF2 — Empty Set

### Statement

```
∃A ∀x (x ∉ A)
```

There exists a set with no members.

### Verification

Define:

```
∅ := λx. f₀
```

The predicate that classifies every state as absent. For any state s:

```
∅(s) = f₀ = FALSE
```

So s ∉ ∅ for all s. ✓

### Cardinality Check

The product of membership indicators is empty (no f₁ factors), which yields f₀ — eigenvalue 0. |∅| = 0. ✓

**Status: PASS.**

---

## Part 4: ZF3 — Pairing

### Statement

```
∀a ∀b ∃C ∀x (x ∈ C ↔ x = a ∨ x = b)
```

For any two objects a and b, there exists a set {a, b}.

### Verification

For any states a, b : State, define:

```
{a, b} := λx. OR(eq(x, a), eq(x, b))
```

where eq(x, y) is the equality predicate on states.

### The Equality Predicate

For eigenstates (states in the orbit), equality is decidable via eigenvalue comparison:

```
eq(f_α, f_β) := if obs reads off α from f_α and β from f_β,
                 then α = β is decidable in ℝ (or ℚ, or ℤ, depending on level)
```

More concretely: eigenstate f_α has eigenvalue α (by the eigenvalue theorem). Two eigenstates are equal iff their eigenvalues are equal. Since eigenvalues live in an ordered field (ℚ or ℝ), equality is decidable.

For the general case (states that might not be eigenstates of obs), decidable equality requires that bisimulation (A4) be implementable as a boolean predicate. This is a stronger requirement than A4 alone provides — A4 defines equality, but doesn't guarantee a computable decision procedure.

**For eigenstates:** eq(f_α, f_β) = f₁ if α = β, f₀ otherwise. Well-defined and computable.

**For the ℕ orbit specifically:**

```
eq(fₘ, fₙ) = f₁ if m = n, f₀ otherwise
```

Decidable because natural number equality is decidable.

### Construction

Given eigenstates a = f_α and b = f_β:

```
{f_α, f_β} := λx. OR(eq(x, f_α), eq(x, f_β))
```

Check: {f_α, f_β}(f_α) = OR(f₁, eq(f_α, f_β)) = f₁ ✓
Check: {f_α, f_β}(f_γ) = OR(f₀, f₀) = f₀ for γ ∉ {α, β} ✓

**Status: PASS** — for eigenstate sets (which is the domain we care about). Decidable equality on eigenstates comes from the eigenvalue theorem.

---

## Part 5: ZF4 — Union

### Statement

```
∀F ∃A ∀x (x ∈ A ↔ ∃B (B ∈ F ∧ x ∈ B))
```

For any collection of sets F, the union ⋃F exists.

### Finite Case

For a finite family {S₁, S₂, ..., Sₖ}:

```
⋃{S₁, ..., Sₖ} := λx. OR(S₁(x), OR(S₂(x), ... OR(Sₖ₋₁(x), Sₖ(x))...))
```

Iterated OR. Well-defined, computable. ✓

### Binary Union (Already Established)

```
A ∪ B = λx. OR(A(x), B(x))
```

From [spectral-arithmetic-complete](spectral-arithmetic-complete.md) Part 6. ✓

### Infinite Case

For an infinite family F (a predicate over predicates — Level 2), the union is:

```
⋃F := λx. ∃S (F(S) = f₁ ∧ S(x) = f₁)
```

This requires **existential quantification over predicates** — a second-order operation. The issue: "∃S" ranges over all Level-1 predicates, which is an uncountable domain.

In ZF, this works because ZF treats sets as first-class objects with ∈ as a primitive. In the predicate framework, predicates are functions, and quantifying over all functions requires second-order comprehension.

**What's needed:** An axiom asserting that for any Level-2 predicate F, the union predicate ⋃F exists as a Level-1 predicate. This is a closure condition on the predicate universe.

**Status: PASS (finite), CONDITIONAL (infinite)** — the infinite case requires the framework to support second-order quantification over predicates. See Part 12 for the required axiom (F2).

---

## Part 6: ZF5 — Power Set

### Statement

```
∀A ∃B ∀C (C ∈ B ↔ C ⊆ A)
```

For any set A, the power set P(A) exists.

### Finite Case

Already established in [spectral-arithmetic-complete](spectral-arithmetic-complete.md) Part 8:

- A subset of A is a predicate that returns f₁ only where A returns f₁
- For |A| = n, there are 2ⁿ such predicates (each element independently f₀ or f₁)
- |P(A)| = 2^|A| ✓

### Infinite Case

For A = ℕ (the natural number orbit), P(ℕ) is the collection of all predicates ℕ → {f₀, f₁} — all infinite binary sequences.

This is a Level-2 object: a predicate over predicates. The power set axiom asserts it *exists* as an object in the theory.

**What the framework already gives:**
- Each individual subset of ℕ exists as a Level-1 predicate (e.g., "the even numbers" = λfₙ. f₁ if n is even, f₀ otherwise)
- The cardinality formula |P(ℕ)| = 2^|ℕ| is computable
- Cantor's theorem (no bijection ℕ → P(ℕ)) follows from the diagonal argument

**What's missing:**
- The **totality** P(ℕ) existing as a single Level-2 predicate
- This requires an axiom asserting that the collection of all sub-predicates of any set-predicate exists

**Status: PASS (finite), REQUIRES F1 (infinite)** — see Part 12.

---

## Part 7: ZF6 — Infinity

### Statement

```
∃A (∅ ∈ A ∧ ∀x (x ∈ A → x ∪ {x} ∈ A))
```

There exists an infinite set (an inductive set).

### Verification

The natural number orbit ℕ = {f₀, f₁, f₂, ...} is exactly such a set.

Define the predicate:

```
ℕ_pred := λx. f₁ if x = fₙ for some n ∈ ℕ, f₀ otherwise
```

More formally: x ∈ ℕ_pred iff x is in the orbit of f₀ under S.

Check the axiom's conditions:

**1. ∅ ∈ A interpretation:**

In the von Neumann encoding, 0 = ∅ and the inductive set contains 0. Here, f₀ plays the role of 0.

```
ℕ_pred(f₀) = f₁     ✓     (f₀ is in the orbit — it's the starting point)
```

**2. Closure under successor:**

If fₙ ∈ ℕ_pred, then S(fₙ) = f_{n+1} ∈ ℕ_pred.

```
ℕ_pred(fₙ) = f₁  →  ℕ_pred(f_{n+1}) = f₁     ✓
```

**3. Infinity:**

The orbit is infinite by A8 (or its derived version from the eigenvalue theorem + characteristic zero). Sⁿ(f₀) ≠ Sᵐ(f₀) for n ≠ m. ✓

### The Subtlety: Completed Totality

The axiom of infinity doesn't just say "there are infinitely many things." It says there exists **a set** — a single object — containing all of them. In ZF, this is the crucial step from potential infinity (you can always generate one more) to actual infinity (the completed collection exists).

In the framework:
- The orbit generation rule (A3: S(s) = compose(f₁, s)) gives **potential** infinity — you can always compute S(fₙ) = f_{n+1}
- A8 (infinite orbit, derived from eigenvalue theorem) guarantees non-termination
- But does ℕ_pred exist as a Level-1 predicate?

The predicate ℕ_pred = λx.(∃n, Sⁿ(f₀) = x) requires existential quantification over ℕ — which is the very set being constructed. This is the standard bootstrapping issue.

**Resolution:** The orbit {f₀, f₁, f₂, ...} is definable as the **smallest** set containing f₀ and closed under S — this is how P5 (induction) was derived. The set is characterized by a closure condition, not by enumeration. If the framework can form predicates by closure conditions (which it needs for induction anyway), then ℕ_pred exists.

**What's needed:** An axiom asserting that the orbit of f₀ under S exists as a completed totality — a Level-1 predicate. This is the process-framework analogue of the set-theoretic axiom of infinity.

**Status: PASS with F1** — the orbit exists and is infinite; asserting it as a completed set-predicate requires axiom F1 (see Part 12).

---

## Part 8: ZF7 — Separation (Comprehension Schema)

### Statement

```
∀A ∃B ∀x (x ∈ B ↔ x ∈ A ∧ φ(x))
```

For any set A and any property φ, the subset {x ∈ A : φ(x)} exists.

### Verification

Given a set-predicate A and a property φ (itself a predicate), define:

```
{x ∈ A : φ(x)} := λx. AND(A(x), φ(x))
```

This is AND-composition of predicates. The result is a predicate that returns f₁ exactly when both A(x) = f₁ and φ(x) = f₁.

Check:
- x ∈ B iff AND(A(x), φ(x)) = f₁ iff A(x) = f₁ and φ(x) = f₁ iff x ∈ A and φ(x) ✓

### What "Property" Means

In ZF, φ is any first-order formula in the language of set theory. In the framework, φ is any definable predicate State → {f₀, f₁}. The separation schema holds for every such predicate.

**Key point:** Separation is weaker than unrestricted comprehension (which Russell's paradox kills). It only forms subsets of already-existing sets. This avoids paradox: {x ∈ A : x ∉ x} is well-defined because x ranges over states (Level 0), not predicates (Level 1), so "x ∉ x" is type-invalid — a state can't be a member of itself because states aren't predicates.

The type stratification handles this automatically.

### Example

The set of even numbers:

```
A := ℕ_pred
φ := λfₙ. f₁ if n is even, f₀ if n is odd

{x ∈ ℕ : x is even} = λx. AND(ℕ_pred(x), φ(x))
```

This is a well-defined Level-1 predicate. ✓

**Status: PASS** — AND-composition of predicates handles separation directly. Type stratification prevents paradoxes.

---

## Part 9: ZF8 — Replacement

### Statement

```
∀A (∀x ∈ A ∃!y φ(x,y) → ∃B ∀y (y ∈ B ↔ ∃x ∈ A φ(x,y)))
```

If F is a definable function (for every x in A there's a unique y with φ(x,y)), then the image F[A] = {y : ∃x ∈ A, F(x) = y} exists as a set.

### Verification

Given a set-predicate A and a function F : State → State:

```
F[A] := λy. ∃x (A(x) = f₁ ∧ eq(F(x), y) = f₁)
```

The image predicate returns f₁ on y iff there exists some x in A that F maps to y.

### Finite Case

If A is finite (a finite number of states with A(x) = f₁), the existential quantifier is a finite OR:

```
F[A] = λy. OR(eq(F(a₁), y), OR(eq(F(a₂), y), ... eq(F(aₙ), y)))
```

Well-defined, computable. ✓

### Infinite Case

If A is infinite (e.g., A = ℕ_pred), the existential quantifier ranges over countably many states. The image predicate becomes:

```
F[ℕ] = λy. ∃n ∈ ℕ (eq(F(fₙ), y) = f₁)
```

This requires:
1. F to be definable in the framework (a function State → State expressible in the language)
2. The existential quantifier over ℕ to produce a well-defined predicate

**What's needed:** An axiom asserting that for any definable function F and any set-predicate A, the image predicate F[A] exists as a Level-1 predicate. This is a closure condition on the predicate universe.

### What Replacement Does

Replacement is the most powerful of the ZF axioms. Combined with the axiom of infinity, it enables:
- Transfinite recursion
- Construction of ordinals beyond ω
- Building sets that separation alone can't reach

The framework's current machinery (predicates + Church booleans) handles the *logic* of replacement. What it needs is the *existence* guarantee — that image predicates are always well-defined. This is axiom F3 (Part 12).

**Status: PASS (finite), CONDITIONAL (infinite)** — requires F3 for infinite domains.

---

## Part 10: ZF9 — Foundation (Regularity)

### Statement

```
∀A (A ≠ ∅ → ∃x ∈ A (x ∩ A = ∅))
```

Every non-empty set has an ∈-minimal element. Equivalently: there are no infinite descending ∈-chains (... ∈ c ∈ b ∈ a), and no set is a member of itself (x ∉ x).

### Verification

Foundation is **automatically satisfied** by the type stratification.

**Why x ∈ x is impossible:**

In the framework:
- **States** live at Level 0: elements of the type State
- **Sets** (predicates) live at Level 1: functions State → {f₀, f₁}
- Membership x ∈ S means S(x) = f₁, requiring x : State and S : State → {f₀, f₁}

A state cannot be a predicate. They are different types. Therefore:
- x ∈ x requires x to be both a State and a predicate on State — **type error**
- {x : x ∉ x} is ill-typed — the clause "x ∉ x" applies a state to itself

**No infinite descending ∈-chains:**

For an ∈-chain a₃ ∈ a₂ ∈ a₁ ∈ a₀:
- a₃ ∈ a₂ requires a₃ : Level 0, a₂ : Level 1
- a₂ ∈ a₁ requires a₂ : Level 0, a₁ : Level 1

But a₂ can't be both Level 0 (to be a member of a₁) and Level 1 (to have a₃ as a member). Each step up the ∈-chain requires bumping the type level. An ∈-chain of length k requires k+1 type levels.

**In a finitely stratified type system, ∈-chains have bounded length.** Foundation holds automatically.

### Comparison with ZF

In ZF, Foundation is an axiom because the language (first-order logic with a single binary relation ∈) doesn't distinguish types. Sets and elements live in the same universe, so x ∈ x is syntactically well-formed and must be explicitly ruled out.

In a typed framework (whether MLTT, higher-order logic, or the predicate hierarchy here), Foundation is a consequence of typing discipline. This is one of the advantages of the process-based approach: the type structure does work that ZF must axiomatize.

### Caveat: Sets of Sets

If we introduce Level-2 predicates (predicates over predicates — "sets of sets"), then ∈-chains of length 2 become possible:

```
Level 0: state s
Level 1: predicate P with P(s) = f₁        (s ∈ P)
Level 2: predicate Q with Q(P) = f₁        (P ∈ Q)
```

This gives s ∈ P ∈ Q — a chain of length 2. But Q can't be a member of anything at Level 2 — it would need a Level-3 predicate. The chain is bounded by the number of type levels.

Foundation holds at every level of the hierarchy. ✓

**Status: PASS** — type stratification prevents self-membership and infinite ∈-chains.

---

## Part 11: ZF10 — Choice

### Statement (Axiom of Choice)

```
∀F (∅ ∉ F → ∃f : F → ⋃F,  ∀A ∈ F (f(A) ∈ A))
```

For any family of non-empty sets, there exists a function selecting one element from each.

### Status in ZF

Choice is **independent** of ZF — Gödel (1938) showed ZF + Choice is consistent (if ZF is), and Cohen (1963) showed ZF + ¬Choice is also consistent (if ZF is). It can be neither proved nor disproved from the other axioms.

### Status in the Framework

The same independence applies. The framework's axioms (A1-A6, B1-B5, C1-C3, D1-D2, E1) don't resolve Choice one way or the other, just as ZF's axioms don't.

**Countable choice:** For countable families (indexed by ℕ), a choice function can be constructed by induction over the orbit. If each set Sₙ is non-empty, then Sₙ has at least one element — pick any fixed one and define f(Sₙ) = that element. This works because ℕ is well-ordered.

**Uncountable choice:** For uncountable families, no construction is available without an additional axiom. This is the same situation as in ZF.

**If Choice is desired:** Add it as an axiom (making the framework analogous to ZFC rather than ZF). If it is not desired, leave it out.

**Status: INDEPENDENT** — same as in ZF. Neither provable nor refutable from the framework's axioms.

---

## Part 12: The Gap — New Axioms for Infinite Collections (F1-F3)

The test suite reveals a systematic pattern: axioms about finite sets pass outright (predicates + Church booleans handle them). Axioms about infinite sets require one additional commitment: **infinite collections exist as completed objects.**

This is the same gap that separates PA from ZF in classical mathematics. PA has induction (you can always go further) but not completed infinities (the totality exists as a single object). ZF has both.

### F1. Completed Orbit (Axiom of Infinity for the Framework)

```
The orbit {Sⁿ(f₀) : n ∈ ℕ} exists as a Level-1 predicate ℕ_pred : State → {f₀, f₁}.
```

This asserts that the orbit — which is already generated by A3 (successor) and guaranteed infinite by the eigenvalue theorem — exists as a **completed totality**. The predicate ℕ_pred(x) returns f₁ iff x = fₙ for some n.

**What this buys:** The axiom of infinity (ZF6) passes fully. ℕ_pred is the inductive set.

**Computational reading:** The natural numbers are not just a generation procedure — they are a completed data structure that can be quantified over.

**Relationship to ZF:** This is the direct analogue of ZF's axiom of infinity (∃ω). The content is the same: the step from potential to actual infinity.

### F2. Predicate Comprehension (Powerset for the Framework)

```
For any Level-1 predicate A, the collection of all sub-predicates of A exists
as a Level-2 predicate P(A).
```

Formally: P(A) : (State → {f₀, f₁}) → {f₀, f₁}, defined by:

```
P(A)(S) = f₁  iff  ∀x (S(x) = f₁ → A(x) = f₁)     (S ⊆ A)
```

**What this buys:**
- Power set (ZF5) passes fully for infinite sets
- |P(ℕ)| = 2^|ℕ| — the uncountable totality exists
- Union over infinite families (ZF4) — ⋃F defined via existential quantification over the predicate universe
- Cantor's theorem: |P(A)| > |A| for all sets A (including infinite ones)

**Computational reading:** The space of all observers (predicates) over a state space is itself a well-defined state space.

**Relationship to ZF:** This combines the power set axiom and (implicitly) the union axiom. It asserts that the function space State → {f₀, f₁} is itself a legitimate domain.

### F3. Definable Image Closure (Replacement for the Framework)

```
For any definable function F : State → State and any Level-1 predicate A,
the image predicate F[A] := λy. ∃x(A(x) = f₁ ∧ F(x) = y) exists as a Level-1 predicate.
```

**What this buys:**
- Replacement (ZF8) passes fully
- Transfinite recursion becomes available (define ordinals beyond ω)
- The image of any set under a definable function is a set

**What "definable" means:** F is a function expressible in the language of the framework — built from compose, obs, ⊕, and the logical operations. This is the analogue of "definable in the first-order language of set theory" in ZF's replacement schema.

**Computational reading:** If you can define a transformation, the output of applying it to a completed collection is itself a completed collection.

**Relationship to ZF:** Direct analogue of the replacement schema.

---

## Part 13: The Full Axiom Set (ZF Level)

### Primitives (4)

State, compose, obs, ⊕

### Axioms (20 + non-degeneracy)

| Group | Axioms | Count | Level |
|---|---|---|---|
| Process core | A1-A6 | 6 | ℕ |
| Semiring + observation | B1-B5 | 5 | ℕ |
| Ring + integral domain | C1-C3 | 3 | ℤ |
| Rational extension | D1-D2 | 2 | ℚ |
| Completion | E1 | 1 | ℝ |
| Set-theoretic closure | F1-F3 | 3 | ZF |
| **Total** | | **20** |  |

Plus non-degeneracy (f₀ ≠ f₁ ≠ z pairwise distinct).

### F-Group Summary

| # | Name | Statement | ZF analogue |
|---|------|-----------|-------------|
| F1 | Completed orbit | ℕ orbit exists as a predicate | Axiom of Infinity |
| F2 | Predicate comprehension | Sub-predicate collections exist | Power Set + Union |
| F3 | Definable image closure | Images of sets under definable functions are sets | Replacement Schema |

### What F1-F3 Don't Cover

- **Foundation:** Already handled by type stratification (Part 10). No axiom needed.
- **Extensionality:** Definitional (Part 2). No axiom needed.
- **Empty Set, Pairing, Separation:** Follow from predicate construction + Church booleans. No axioms needed.
- **Choice:** Independent. Can be added as F4 if desired.

---

## Part 14: Verification — All ZF Axioms Revisited

With F1-F3, let's re-verify every axiom.

### ZF1. Extensionality ✓

Definitional: predicates equal iff they agree on all inputs. No axiom needed.

### ZF2. Empty Set ✓

∅ = λx.f₀. Exists as a Level-1 predicate. Membership check: ∅(s) = f₀ for all s.

### ZF3. Pairing ✓

{a, b} = λx. OR(eq(x,a), eq(x,b)). Exists for eigenstates with decidable equality.

### ZF4. Union ✓

**Finite:** Iterated OR.
**Infinite:** Given family F (Level-2 predicate), ⋃F = λx. ∃S(F(S) = f₁ ∧ S(x) = f₁). The existential quantifier ranges over the predicate space, which exists by F2. The resulting predicate exists by F3 (or by closure of the predicate space under boolean operations).

### ZF5. Power Set ✓

**Finite:** 2^n computed.
**Infinite:** P(A) exists as Level-2 predicate by F2. P(A)(S) = f₁ iff S ⊆ A.

### ZF6. Infinity ✓

ℕ_pred exists as Level-1 predicate by F1. Contains f₀ (the "empty set" / zero element). Closed under successor: fₙ ∈ ℕ_pred → f_{n+1} ∈ ℕ_pred. Infinite by eigenvalue theorem.

### ZF7. Separation ✓

{x ∈ A : φ(x)} = λx. AND(A(x), φ(x)). AND-composition of predicates. Well-defined for any definable φ.

### ZF8. Replacement ✓

F[A] = λy. ∃x(A(x) = f₁ ∧ F(x) = y). Exists as Level-1 predicate by F3.

### ZF9. Foundation ✓

Type stratification prevents self-membership and infinite ∈-chains. No axiom needed.

### ZF10. Choice — INDEPENDENT

Same status as in ZF. Add as F4 if desired.

---

## Part 15: Honest Assessment

### What Works Well

1. **Extensionality, Empty Set, Separation, Foundation** pass without new axioms. The predicate-as-set interpretation handles them naturally, and type stratification gives Foundation for free.

2. **Pairing** works cleanly for eigenstates because the eigenvalue theorem provides decidable equality.

3. **The pattern is clean:** finite set operations are already handled by Church booleans. The only new axioms (F1-F3) address the same gap that separates PA from ZF in classical mathematics: the step from potential to actual infinity.

### What's Honest About the Limitations

1. **F1-F3 are doing the heavy lifting.** The "test suite passes" claim is only as strong as F1-F3. These axioms assert that infinite collections exist as completed objects — which is exactly what ZF's axiom of infinity, power set axiom, and replacement schema assert. We're not deriving ZF from the process framework; we're adding ZF-equivalent axioms stated in process-framework language.

2. **The type hierarchy raises a question.** ZF uses a single sort (sets) with ∈ as the only relation. The framework uses a typed hierarchy (states, predicates, predicates-over-predicates, ...). These are different logical architectures. The framework's type discipline gives Foundation for free but makes it harder to express self-referential constructions (which ZF can express and then rules out with Foundation). The tradeoff: we get some axioms for free, but our language is more restricted.

3. **"Definable function" in F3 needs precision.** The replacement schema quantifies over all formulas in the language. What counts as "definable" in the process framework? This needs a precise specification of the framework's formal language — which formulas are allowed, what quantifiers are available, and how the hierarchy of types is navigated. Without this, F3 is stated informally.

4. **No transfinite ordinals yet.** ZF's replacement schema enables transfinite recursion and the construction of ordinals beyond ω (like ω+1, ω·2, ε₀). The framework has ℕ (which is ω) but hasn't constructed higher ordinals. F1-F3 provide the machinery, but the actual constructions haven't been carried out.

5. **Equiconsistency is plausible but not proved.** For PA, equiconsistency was proved both ways (model of A1-A8 in PA, model of PA in A1-A8). For ZF, we've shown the ZF axioms are *satisfied* under the interpretation (sets-as-predicates), but we haven't constructed a model of the full 20-axiom system inside ZF, or vice versa. The equiconsistency proof would require:
   - **ZF → Framework:** Model the 20 axioms inside ZF (likely straightforward — take State = ℝ, compose = multiplication, obs = d/dx, ⊕ = addition, predicates as functions)
   - **Framework → ZF:** Interpret ZF's ∈ and set variables in the framework's type hierarchy (this is what F1-F3 aim to enable)

### The Key Insight

The gap between PA and ZF is the same in the process framework as it is in classical mathematics: **actual infinity**. PA has potential infinity (you can always go further). ZF has actual infinity (the totality exists). The process framework reproduces this gap exactly — and F1-F3 bridge it exactly as ZF's axioms do.

This is evidence that the framework is not hiding or avoiding the hard problems. The same foundational issues arise, and they're resolved by the same logical commitments (actual infinity, powersets, replacement). The contribution is not avoiding these commitments but expressing them in process-native language.

---

## Part 16: Comparison with ZF

### Axiom-by-Axiom Mapping

| ZF Axiom | Framework mechanism | New axiom needed? |
|---|---|---|
| Extensionality | Definitional (predicate equality) | No |
| Empty Set | λx.f₀ | No |
| Pairing | OR(eq(x,a), eq(x,b)) | No |
| Union | Iterated OR (finite) / ∃-quantification (infinite) | F2 for infinite |
| Power Set | 2^n (finite) / sub-predicate collection (infinite) | F2 for infinite |
| Infinity | ℕ orbit as completed predicate | F1 |
| Separation | AND-composition of predicates | No |
| Replacement | Image predicate via ∃-quantification | F3 |
| Foundation | Type stratification | No |
| Choice | Independent | F4 if desired |

### What's Gained

- **Foundation is free** — type discipline replaces an axiom
- **Extensionality is free** — definitional from predicate interpretation
- **Separation is free** — AND-composition of predicates
- **Empty Set, Pairing are free** — predicate construction
- **5 of 9 ZF axioms are automatic** in the predicate framework

### What's Not Gained

- **Infinity, Power Set, Replacement** still require axioms (F1-F3)
- These are the axioms that carry ZF's strength beyond PA
- The process framework reproduces them, but doesn't derive them from weaker principles

### Axiom Count Comparison

| System | Axiom count |
|---|---|
| ZF | 9 axioms (2 are schemas) |
| ZFC | 10 axioms |
| Process framework (ℝ level) | 17 axioms |
| Process framework (ZF level) | 20 axioms |

The process framework has more axioms because it builds the number tower explicitly (A1-A6 for ℕ, B1-B5 for semiring structure, C1-C3 for ℤ, D1-D2 for ℚ, E1 for ℝ). ZF builds numbers implicitly through set-theoretic constructions. The tradeoff: ZF's axioms are fewer but the constructions within ZF are more complex.

---

## Part 17: Next Steps

### Equiconsistency Proof

Prove Con(20 axioms) ↔ Con(ZF). This requires:

1. **Forward (ZF → Framework):** Build a model of the 20 axioms inside ZF.
   - State = ℝ (or a suitable function space)
   - compose = multiplication
   - obs = differentiation
   - ⊕ = addition
   - Predicates = characteristic functions ℝ → {0, 1}
   - Verify all 20 axioms hold in this model

2. **Backward (Framework → ZF):** Interpret ZF inside the framework.
   - Define "set" as a Level-1 predicate
   - Define ∈ as predicate application
   - Verify all 9 ZF axioms hold (this document does this, modulo F1-F3)

### Transfinite Ordinals

Construct ordinals beyond ω using F3 (replacement):
- ω + 1: the image of ℕ ∪ {ℕ} under the identity
- ω · 2: the image of ℕ × {0, 1}
- ε₀: the limit of ω, ω^ω, ω^ω^ω, ...

### Formalization

The 20-axiom system is a candidate for proof assistant formalization. The type-stratified predicate hierarchy maps naturally to dependent type theory (MLTT/Lean 4).

---

## Related

- [axioms](axioms.md)
- [pa-equiconsistency](pa-equiconsistency.md)
- [real-extension](real-extension.md)
- [spectral-arithmetic-complete](spectral-arithmetic-complete.md)
