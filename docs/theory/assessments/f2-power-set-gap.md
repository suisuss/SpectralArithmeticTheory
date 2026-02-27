# The F2 Gap: Separation vs Power Set

**Date:** 2026-02-27
**Scope:** The discrepancy between F2 as documented (Power Set) and F2 as implemented (Separation), and what it would take to close the gap.

---

## The Problem

The theory documents (`zf-test-suite.md` Part 12, `layers.md` Level F) define F2 as:

> **Predicate Comprehension / Power Set:** For any Level-1 predicate A, the collection of all sub-predicates exists as a Level-2 predicate P(A).

The code (`ZFTest.lean`) implements F2 as:

```lean
sepEns : Ens → (State → Prop) → Ens
sepEns_spec : ∀ A φ s, mem s (sepEns A φ) ↔ (mem s A ∧ φ s)
```

This is **Separation** (ZF7), not **Power Set** (ZF5). These are different axioms with different logical strength. Separation produces sub-ensembles of existing ensembles. Power Set produces the *collection of all sub-ensembles* — a second-order object.

The code is honest about this: ZF4 (Union) and ZF5 (Power Set) are explicitly marked "deferred" at the Ens level, with metatheoretic fallbacks (`zf4_union_meta`, `zf5_powerset_meta`) using `State -> Prop` directly.

---

## Why It Matters

Without Power Set at the Ens level, the current framework has:
- **F1:** The orbit ensemble exists (Infinity)
- **F2:** Sub-ensembles exist (Separation)
- **F3:** Image ensembles exist (Replacement)

This gives you ZF1-ZF3, ZF6-ZF8 at the Ens level. You're missing ZF4 (Union over families) and ZF5 (Power Set). The consequence: you can't form sets-of-sets within the abstract Ens framework. Everything operates on `State`-level membership.

For ZF-equiconsistency, the backward direction (Framework -> ZF) needs Power Set. The current code punts to Lean's `Prop` universe for this, which works but makes the axiom trivial (metatheoretic). The abstract Ens formulation was introduced precisely to avoid this.

---

## What Power Set Requires

Power Set is fundamentally a *level-crossing* operation. Given an ensemble A (a set of states), P(A) is a set of ensembles — a different kind of object. The current `Ens` type is flat: ensembles contain states, period. There's no way to express "B is a sub-ensemble of A" as membership in some ensemble, because ensembles aren't states.

Three architectural approaches:

### Option A: Stratified Ens Hierarchy

Introduce indexed types:

```lean
Ens₀ : Type*           -- sets of states
Ens₁ : Type*           -- sets of Ens₀ (sets of sets)
mem₀ : State → Ens₀ → Prop
mem₁ : Ens₀ → Ens₁ → Prop
```

Power Set becomes:

```lean
powerEns : Ens₀ → Ens₁
powerEns_spec : ∀ A B, mem₁ B (powerEns A) ↔ ensSubset B A
```

**Tradeoffs:**
- Clean and explicit. Each level has its own type.
- Mirrors the cumulative hierarchy V₀ ⊂ V₁ ⊂ V₂ exactly.
- But: every new level requires new types, new membership relations, new axioms. Proofs don't generalize across levels without a universe-polymorphic abstraction.
- Finite depth: you commit to a fixed number of levels. For ZF you need the hierarchy to continue through all finite levels (V_ω), which a fixed-depth encoding can't express.

### Option B: Universe-Indexed Hierarchy

Generalize Option A with a family indexed by ℕ:

```lean
Ens : ℕ → Type*
mem : ∀ n, Ens n → Ens (n + 1) → Prop
```

Where `Ens 0` elements are states (or embed states into `Ens 0`), and `Ens (n+1)` contains sets of `Ens n` elements.

Power Set:

```lean
powerEns : ∀ n, Ens (n + 1) → Ens (n + 2)
powerEns_spec : ∀ n A B, mem (n+1) B (powerEns n A) ↔ ensSubset n B A
```

**Tradeoffs:**
- Fully general. Handles arbitrary finite depth.
- The equiconsistency argument's cumulative hierarchy is directly expressible.
- But: significantly more complex typeclass. Every operation needs a level index. Proofs become heavier. The relationship between `State` and `Ens 0` needs care (embedding or identification).
- Risk: the machinery may outweigh the mathematical content, especially for a formalization project where the interesting results are at Levels A-E.

### Option C: Single Ens with Self-Membership

Keep a single `Ens` type but allow ensembles to contain other ensembles:

```lean
Ens : Type*
mem : Ens → Ens → Prop
embed : State → Ens  -- embed states into the universe
```

Power Set:

```lean
powerEns : Ens → Ens
powerEns_spec : ∀ A B, mem B (powerEns A) ↔ ensSubset B A
```

**Tradeoffs:**
- Most ZF-like: a single-sorted universe with ∈.
- Power Set is natural to state.
- But: Foundation must now be asserted explicitly (type stratification no longer prevents self-membership). The `embed` function creates friction — states must be wrapped before they can be members. And the abstract `Ens` must now be rich enough to contain both "flat" ensembles (sets of states) and "higher" ensembles (sets of sets). Extensionality needs care: two ensembles are equal iff they have the same Ens-members, but states embedded via `embed` aren't ensembles.
- Risk: this is essentially re-axiomatizing ZF inside Lean. At that point, the question becomes: what does the spectral framework contribute to set theory beyond providing a model?

---

## Assessment

### What the current code actually achieves

The current F1-F3 (with abstract Ens) achieve something specific and valuable:

1. The F-axioms are non-trivial (countermodels prove this).
2. The forward model (`Ens = State -> Prop`) satisfies them.
3. ZF1-ZF3 and ZF6-ZF8 are derived at the Ens level.
4. The dependency structure is clear: what comes from F-axioms vs metatheory.

This is enough to demonstrate the PA-to-ZF bridge at the level of individual set operations. It's not enough for the full cumulative hierarchy.

### What Power Set would add

Adding Power Set at the Ens level would close the gap between the docs' F2 (Power Set) and the code's F2 (Separation). It would enable:

- ZF5 at the Ens level (currently metatheoretic)
- ZF4 at the Ens level (Union over families, currently metatheoretic)
- The beginning of transfinite ordinal constructions within Ens

### Recommendation

**Option A (stratified, two-level)** is the pragmatic choice:

- Add a single `Ens₂` type for sets-of-ensembles.
- Add `mem₂ : Ens → Ens₂ → Prop` and `ens_ext₂`.
- Add `powerEns : Ens → Ens₂` with the obvious spec.
- Prove ZF5 at this level.
- Defer the full ℕ-indexed hierarchy to a future phase.

This is honest about the scope: you get one level of Power Set, enough for ZF5 and ZF4, without the complexity of a fully indexed hierarchy. It extends the current architecture minimally.

The full ℕ-indexed hierarchy (Option B) is the correct long-term answer but is disproportionate to the current project's goals. The spectral framework's strength is at Levels A-E (eigenvalue theorem, number tower). The set-theoretic layer is verification, not the core contribution.

### What the forward model needs

For `Ens₂ = (State -> Prop) -> Prop` in the forward model. `mem₂ A P` means `P A`. `powerEns A` means `fun B => ensSubset B A`. The proofs are `Iff.rfl` in the forward model, as expected.

For countermodels: a restricted `Ens₂` that falsifies Power Set would need to show that some collection of sub-ensembles can't be captured. This is straightforward if `Ens₂` is restricted to finite families of ensembles — the power set of ℕ is uncountable, so no finite family suffices.

---

## Related

- [zf-test-suite](../zf-test-suite.md) — Part 12 (F1-F3 definitions), Part 14 (ZF verification)
- [layers](../layers.md) — Level F specification
- [zf-equiconsistency](../zf-equiconsistency.md) — Parts 7, 9-11 (F-axiom verification and backward direction)
