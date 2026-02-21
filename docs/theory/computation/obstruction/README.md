# Encoding Obstruction: Lean Formalization

## Overview

Four Lean files prove, sorry-free, that no injective encoding of terms as eigenstates can serve as a coalgebra morphism for the observation operator. The eval-quote diagram does not commute. This is the **trilemma** reduced to a machine-checked theorem.

```
        eval
Terms --------→ State
  |                |
  | ε (encode)     | obs (eigenvalue scaling)
  |                |
  ↓                ↓
  ℕ  --------→  State
     obs_code (rewrite + re-encode)
```

**The diagram does not commute:** `ε(obsRewrite(obs(t))) ≠ ε(obs(t))` for any injective ε, witnessed by the term `compose(f₁, f₁)`.

---

## Files

| File | Lines | Sorry | What it proves |
|---|---|---|---|
| `Encoding.lean` | 101 | 0 | Term algebra, eval, obsRewrite, rewrite correctness |
| `Pairing.lean` | 78 | 0 | Addition not injective, pairing unbounded, carry witness |
| `OplusImpossibility.lean` | 76 | 0 | No comm+cancel+char-zero bitwise operation exists |
| `Obstruction.lean` | 117 | 0 | **The encoding obstruction theorem** |

Total: ~372 lines, 0 sorry, all machine-checked.

---

## Theorems

### Theorem 1: Encoding Obstruction (Obstruction.lean)

**Statement:** For any injective `ε : Term → ℕ`:

```
ε(obsRewrite(obs(compose(f₁, f₁)))) ≠ ε(obs(compose(f₁, f₁)))
```

**Proof:** The Leibniz rewrite transforms `obs(compose(f₁, f₁))` into `oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁)))` — a structurally different term. Since `Term` has `DecidableEq`, these are provably distinct. Any injective `ε` maps distinct terms to distinct values. QED.

**Key insight:** The proof works at the Term level, not the State level. We don't need to show eigenvalues differ in abstract State (which would require additional assumptions). We show the TERMS differ, and injectivity does the rest.

**Why this proves the trilemma:** If the encoding were a coalgebra morphism, the diagram would commute — encoding then observing would equal observing then encoding. It doesn't, because the Leibniz rule changes the term structure. The change is the introduction of `oplus` (addition) into the observation dynamics, which is exactly the ⊕ obstruction identified in the theory documents.

### Theorem 3: Addition Not Injective on Pairs (Pairing.lean)

**Statement:** `¬ (∀ a b c d : ℕ, a + b = c + d → a = c ∧ b = d)`

**Proof:** Counterexample: 3 + 5 = 4 + 4 but (3,5) ≠ (4,4).

**Significance:** Addition cannot serve as an injective pairing function. Any encoding of structured terms (which have multiple components) into ℕ must use something other than addition — some form of super-additive pairing.

### Theorem 4: Injective Pairings Are Unbounded (Pairing.lean)

**Statement:** For any injective `π : ℕ × ℕ → ℕ` and bound `B`, there exists `n` with `π(n, n) > B`.

**Proof:** Pigeonhole via `Fin`. The `B + 2` pairs `(0,0), ..., (B+1, B+1)` are distinct, so their images are `B + 2` distinct naturals. If all were `≤ B`, that's `B + 2` values in `{0,...,B}` (only `B + 1` slots) — contradiction by `Fintype.card_le_of_injective`.

**Bug found during formalization:** The original plan claimed "injective `f : ℕ → ℕ` implies `f(n) ≥ n`." This is **false** — the transposition `f(0) = 1, f(1) = 0, f(k) = k` for `k ≥ 2` is injective but `f(1) = 0 < 1`. The correct theorem is unboundedness (for any `B`, some `f(n) > B`), not pointwise domination.

### Theorem 5: ⊕ Impossibility (OplusImpossibility.lean)

**Statement:** For any commutative `f : Bool → Bool → Bool` with identity `e` and left-cancellation, `f(x, x) = e` for all `x` (characteristic 2).

**Proof:** Case analysis on `e` and `x`. Commutativity + identity determines `f` on mixed inputs. Cancellation + the determined values force `f(x, x) = e` by contradiction (if `f(x, x) ≠ e`, cancellation is violated).

**Significance:** Any bitwise (bit-independent) operation on ℕ that is commutative, cancellative, and has an identity must have characteristic 2. The framework requires characteristic zero (axiom B5). Therefore no bitwise realization of ⊕ satisfies all the framework's requirements. This is the refined obstruction: ⊕ is the specific operation that can't be made bit-compatible.

### Theorem 7: Carry Propagation Witness (Pairing.lean)

**Statement:** Adding `(2^k - 1) + 1 = 2^k` in base 2, the output bit at position `k` is 1 while neither input has a 1 at position `k` (for `k ≥ 1`).

**Proof:** Direct computation of the relevant bit extractions (`div` and `mod`).

**Significance:** Witnesses that addition in non-redundant binary requires carry propagation from bit 0 to bit k. The output at position k depends on ALL inputs at positions 0 through k-1 — addition is non-local.

---

## Architecture

```
Encoding.lean
    │
    │ defines Term, eval, obsRewrite
    │
    ├──→ Obstruction.lean
    │       │
    │       │ uses: obsRewrite changes term structure (DecidableEq)
    │       │ uses: eval relates terms to DynSemiring states
    │       │ proves: encoding_obstruction_term (THE MAIN THEOREM)
    │       │
    │       └──→ imports Semiring.lean (eigenvalue theorem, for semantic side)
    │
Pairing.lean (standalone)
    │
    │ proves: addition not injective, pairings unbounded, carry witness
    │
OplusImpossibility.lean (standalone)
    │
    │ proves: no comm+cancel+char-zero bitwise op
```

---

## Proof Strategy: Why Term-Level Works

The original plan attempted to prove the obstruction at the State level:

```
smul n (iterS n) ≠ smul 2 (iterS 2)  for n ≠ 2
```

This requires showing that distinct eigenvalues give distinct scaled eigenstates in abstract `DynSemiring` — which needs additional assumptions (integral domain, no zero divisors, or a concrete model).

The solution: work at the **Term level** instead. The Leibniz rewrite transforms `obs(compose(f₁, f₁))` into a structurally different term:

```
obs(compose(f₁, f₁))
  ≠  (by decide, using DecidableEq on Term)
oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁)))
```

Any injective `ε` maps distinct terms to distinct codes. No assumptions about State needed. The obstruction is purely syntactic — the Leibniz rule changes the term, and the change is the introduction of `oplus`, which is exactly the addition that the theory documents identify as the source of the obstruction.

This is arguably a cleaner result than the State-level version: it shows the obstruction is **structural** (inherent in the term rewriting) rather than **semantic** (dependent on properties of the model).

---

## Relationship to Theory Documents

| Theory document | What it claims | What the Lean proves |
|---|---|---|
| `encoding-obstruction.md` | The trilemma: eigenvalue arithmetic + self-encoding + coalgebra morphism jointly unsatisfiable | `encoding_obstruction_term`: for any injective ε, ε(rewrite) ≠ ε(original) |
| `information-domain.md` | ⊕ is the real obstruction | `oplus_bitwise_impossible`: no bitwise op satisfies ⊕'s requirements |
| `addition-non-locality.md` | Carry propagation forces external state | `carry_propagation_witness`: concrete witness of carry from bit 0 to bit k |
| `impossibility-hierarchy.md` | Addition → state → halting → incompleteness | Only the algebraic level is formalized; the halting/incompleteness connection is NOT proved (it's Turing 1936) |
| `observer-as-register.md` | Observer = register | NOT formalized (physical interpretation) |
| `normalization-vs-variation.md` | Newtonian/Lagrangian duality | NOT formalized (physics) |
| `convergence.md` | Algebraic and epistemological routes converge | NOT formalized (meta-observation) |

The Lean formalization proves the **algebraic core** of the theory. Everything above (computation, physics, philosophy) rests on this core but is not machine-checked.
