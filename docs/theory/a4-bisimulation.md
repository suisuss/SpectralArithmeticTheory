# A4: Observational Separation (Bisimulation)

## Date: 2026-02-19

## Summary

A4 is the coalgebraic identity criterion: two states are equal iff no finite sequence of obs and compose operations distinguishes them. It is philosophically central to the construction (identity is behavioral, not structural) but mathematically inert in everything proved so far. It is not formalized in Lean because Lean's built-in equality subsumes it for all current theorems.

---

## Part 1: The Axiom

### Statement

States s₁ and s₂ are equal if and only if no finite sequence of obs and compose operations distinguishes them.

Formally: s₁ = s₂ ↔ ∀ C ∈ Contexts, C(s₁) = C(s₂)

where Contexts is the set of all finite compositions of obs and compose applied to the state in question.

### In MLTT

Coinductive equality — equality defined by observations rather than by construction.

### What it means

This is **bisimulation**. Two processes are the same if and only if no experiment can tell them apart. You don't need to show they were built the same way; you need to show they behave the same way under all possible observations.

This is the coalgebraic dual of induction:
- **Induction** (constructive): two things are equal if they were built from the same parts
- **Coinduction** (observational): two things are equal if no observation separates them

A4 takes the coinductive side. Identity is earned by surviving all tests, not by having matching birth certificates.

---

## Part 2: Three Roles in the Theory

### 1. Coalgebraic identity criterion

A4 is the philosophical core of the "Spectral Arithmetic" framing. Numbers are not sets, not constructions, not syntax — they are **behaviors**. The number 3 is whatever behaves like 3 under every possible observation. This is the same principle behind:

- **Process algebra**: CCS, CSP, and the π-calculus define process equivalence via bisimulation
- **Coalgebra**: States of a coalgebra are identified up to behavioral equivalence
- **Physics**: Two quantum states are the same if no measurement distinguishes them

### 2. Trivially satisfied in every concrete model

| Model | How A4 is satisfied |
|---|---|
| PA model (obs = identity) | Distinct states are trivially separated — obs = id distinguishes everything |
| Analytic model (obs = d/dx) | Coefficient-wise equality; obs extracts coefficients that distinguish distinct functions |
| ZF model (distributions) | Coefficient-wise equality on distributions; obs amplifies the α-coefficient by α |

Every concrete model satisfies A4 for free because the model's equality relation already handles it. A4 never needs to be "checked" — it's a constraint on what kind of equality you're using, not a constraint on the model's behavior.

### 3. Not a rewrite rule

The confluence analysis (see [confluence](computation/confluence.md)) classifies axioms into four classes:

| Class | Examples | Role |
|---|---|---|
| Class 1: Oriented rewrites | A1, A2, A6, B3 | Direct computation |
| Class 2: Structural equalities | A5, B1 | Permutation, not reduction |
| Class 3: Constraints | **A4**, B5, C3, non-degeneracy | Don't rewrite — constrain |
| Class 4: Existential | C1, C2 | Assert existence |

A4 is Class 3. It doesn't produce computational steps. It constrains what equality means but doesn't generate equations.

---

## Part 3: Why A4 Is Not Formalized in Lean

### Lean's equality is intensional

In Lean 4, propositional equality (`=`) is the inductive type `Eq` with constructor `Eq.refl`:

```
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
```

Two terms are equal if:
- They reduce to the same normal form (**definitional equality**), or
- You prove they're equal using rewriting, congruence, etc. (**propositional equality**)

This is **intensional** — equality is about construction, not observation.

### A4 asks for extensional/coinductive equality

A4 says equality should be **extensional with respect to obs and compose**: two states are equal if they produce the same results under all contexts built from the primitives. This is a fundamentally different notion.

### What formalization would require

To formalize A4 in Lean, you would need:

**Option 1: Quotient construction**
1. Define `Context` as an inductive type of all finite compositions of obs and compose:
   ```
   inductive Context where
     | hole : Context
     | obs : Context → Context
     | composeL : State → Context → Context
     | composeR : Context → State → Context
   ```
2. Define evaluation: `eval : Context → State → State`
3. Define the bisimulation relation: `R(a, b) := ∀ C : Context, eval C a = eval C b`
4. Prove `R` is an equivalence relation
5. Take the quotient `State / R` (using `Quotient` or `Setoid`)
6. Lift all operations and axioms to the quotient
7. Prove all existing theorems still hold on the quotient

**Option 2: Axiom schema**
```
axiom obs_separation : ∀ a b : State,
  (∀ C : Context, eval C a = eval C b) → a = b
```
This is cleaner but adds a Lean axiom (beyond the type theory), which may interfere with definitional reduction.

**Option 3: Setoid + quotient**
```
instance bisimSetoid : Setoid State where
  r := fun a b => ∀ C : Context, eval C a = eval C b
  iseqv := ⟨fun _ _ => rfl, fun h C => (h C).symm, fun h1 h2 C => (h1 C).trans (h2 C)⟩
```
Then work with `Quotient bisimSetoid` throughout.

### Why none of these are worth doing (currently)

**No theorem uses A4.** The entire proof chain — eigenvalue theorem, A8-as-theorem, A7-as-theorem, power rule, eigenvalue for ℤ — works with Lean's built-in equality. A4 would only matter if you needed to prove two *syntactically different* states are equal by showing no observation separates them. That situation hasn't arisen because:

1. The orbit elements (`iterS n`) are **constructed**, not discovered — their equality is determined by construction
2. All proofs proceed by induction (the constructive direction), not coinduction
3. The algebraic manipulations (rewriting with associativity, distributivity, Leibniz) preserve Lean's equality

A4 is a constraint on the **metatheory** (what kind of equality the system uses), not on the **object theory** (what equations hold between states). Lean's built-in equality already satisfies a stronger condition than A4 requires for the orbit — if two iterates are equal in Lean, they're certainly observationally indistinguishable.

---

## Part 4: When A4 Would Matter

A4 becomes non-trivial when:

1. **States exist outside the orbit.** If State contains elements beyond {f₀, f₁, f₂, ...}, A4 would constrain which of those are identified. For example, if two different "representations" of a state exist, A4 says they're equal iff behaviorally indistinguishable.

2. **Working with models where State is not freely generated.** In a quotient model (e.g., polynomial ring modulo an ideal), two syntactically different polynomials might be the same element. A4 would say: they're the same iff obs and compose can't tell them apart.

3. **Formalizing the ⊕-closure.** The theory notes that ℕ is closed under compose but not under ⊕. The ⊕-closure (linear combinations of eigenfunctions) is a larger space. Elements like f₂ ⊕ f₃ are not in the orbit. A4 would govern equality in this larger space.

4. **Moving toward ZF.** Sets-as-predicates (S → {f₀, f₁}) live outside the orbit. Extensional equality of sets (same elements → same set) is a form of A4 applied to the predicate interpretation.

---

## Part 5: Relationship to Existing Mathematics

| Concept | Field | Connection to A4 |
|---|---|---|
| Bisimulation | Process algebra (CCS, CSP) | A4 IS bisimulation |
| Coinductive types | Type theory (Coq, Agda) | A4 is coinductive equality — Coq has native support via `CoInductive` |
| Observational equivalence | Programming languages | Two programs are equivalent if no context distinguishes them (contextual equivalence) |
| Leibniz's identity of indiscernibles | Philosophy | A4 is the formal version — indiscernible things are identical |
| Spectral theorem | Functional analysis | States determined by their eigenvalues under obs — spectral data determines the operator |
| Extensionality | Set theory (ZF) | Two sets are equal iff they have the same elements — A4 generalized beyond ∈ |

### The deepest connection: final coalgebra

A4 says State (modulo bisimulation) is a **final coalgebra** for the functor determined by obs and compose. In a final coalgebra:
- Every state is completely determined by its behavior
- The unique map from any other coalgebra to the final one identifies behaviorally equivalent states
- There are no "junk" states that can't be distinguished

This is the formal sense in which the construction is coalgebraic rather than set-theoretic.

---

## Related

- [axioms](axioms.md) — A4 in context of the full axiom set
- [confluence](computation/confluence.md) — A4 classified as constraint (Class 3)
- [pa-equiconsistency](pa-equiconsistency.md) — A4 trivially satisfied in PA model
- [zf-equiconsistency](zf-equiconsistency.md) — A4 satisfied via coefficient equality
-  — Formalization status (A4 not formalized)
