# Plan: Encoding Obstruction — Formalizable Results

## Date: 2026-02-20

## Context

The encoding-obstruction branch has five theory documents developing a chain of arguments from the trilemma through carry non-locality to the impossibility hierarchy. Per the honest assessment, most of this is interpretive scaffolding around known results. **Three claims are concretely provable**. This plan focuses on those.

Everything below is ordered by: (1) most concrete and provable first, (2) dependencies respected, (3) diminishing returns acknowledged.

---

## What to prove (ranked by defensibility)

### Tier 1: The Trilemma Core (novel, formalizable, publishable)

**Theorem 1: No encoding is a coalgebra morphism for obs.**

Statement: Let (State, compose, oplus, obs) be a DynSemiring satisfying A1-B5. Let ε: Terms → ℕ be any injection with computable inverse, where Terms is the free term algebra over {compose, oplus, obs, f₀, f₁, z}. Define obs_ε(n) = ε(obs_rewrite(decode(n))), where obs_rewrite applies the Leibniz rule as an oriented rewrite. Then there exist terms t such that:

```
obs_semantic(f_{ε(t)}) ≠ f_{obs_ε(ε(t))}
```

i.e., eigenvalue scaling and syntactic rewriting on codes produce different results.

This is the weakest (easiest) version — existential, not universal. It says "at least one term breaks the morphism," not "every encoding breaks for every term."

**Why it's provable:** Take t = compose(f₁, f₁). Then:
- obs_semantic(f_{ε(t)}) = ε(t) · f_{ε(t)} — scales by ε(t)
- obs_rewrite(compose(f₁, f₁)) = oplus(compose(f₁, f₁), compose(f₁, f₁)) = oplus(f₂, f₂) — Leibniz expansion
- ε(oplus(f₂, f₂)) is a code for a sum, which for any injective ε must be different from ε(t) · f_{ε(t)} (because ε(t) · f_{ε(t)} is an oplus-sum of ε(t) copies, while ε(oplus(f₂, f₂)) is a single code)

The proof reduces to: ε(oplus(a, b)) ≠ ε(a) + ε(b) for generic a, b — which follows from the pairing lower bound (Part 2 below).

**Lean formalization path:** Define a Term inductive type, an eval function Terms → State, a rewrite function, and an encoding function. Prove the specific inequality for t = compose(f₁, f₁).

---

**Theorem 2 (stronger): No encoding preserves obs trajectories.**

Statement: For any injection ε: Terms → ℕ with computable inverse, there exist terms t and observation depth k such that the semantic trajectory and syntactic trajectory diverge:

```
obs^k_semantic(f_{ε(t)}) involves eigenvalue ε(t)^k
obs^k_code(ε(t)) = ε(obs_rewrite^k(t)) involves iterated re-encoding
```

and these are not bisimilar (the eigenvalues of the two states differ).

**Why it's provable:** At each Leibniz step, the number of terms doubles (one application of Leibniz on a product creates two summands). After k steps, there are O(2^k) terms. The encoding of 2^k terms via any pairing function grows faster than ε(t)^k for sufficiently large k. Trajectory divergence is a growth-rate comparison.

**Lean formalization path:** Prove by induction on k that the syntactic trajectory's code exceeds any polynomial bound on the semantic trajectory's eigenvalue.

---

### Tier 2: The Pairing Lower Bound (known, needs formalization)

**Theorem 3: No injective pairing is additive.**

Statement: There is no function π: ℕ × ℕ → ℕ that is simultaneously injective and satisfies π(m, n) = m + n.

**Proof:** π(3, 5) = π(4, 4) = 8. Injective contradicted. ∎

This is trivial but it's the foundation of everything. Formalizing it in Lean is 5 lines.

---

**Theorem 4: Injective pairings are super-linear on the diagonal.**

Statement: For any injection π: ℕ × ℕ → ℕ, π(n, n) ∈ ω(n). That is, lim_{n→∞} π(n,n)/n = ∞.

**Proof sketch:** The number of pairs (a, b) with a ≤ n and b ≤ n is (n+1)². For π to be injective, π must map these (n+1)² pairs to (n+1)² distinct values. If π(n,n) ≤ cn for all n, then all outputs up to cn are used, but there are only cn+1 values available for (n+1)² pairs. For n > c, this is impossible. Contradiction.

**Lean formalization path:** Pigeonhole principle argument. Mathlib has Finset.card_le_card for injection bounds. Straightforward.

---

### Tier 3: The ⊕ Impossibility (novel, algebraic, concrete)

**Theorem 5: No binary operation on ℕ is simultaneously cancellative, characteristic-zero, and bit-independent.**

Statement: There is no operation ⊕: ℕ × ℕ → ℕ satisfying:
1. Cancellative: a ⊕ b = a ⊕ c → b = c
2. Characteristic zero: for all n ≥ 1, the n-fold iterate n ⊕' x ≠ identity (where ⊕' is iterated ⊕)
3. Bit-independent: (a ⊕ b)[k] depends only on a[k] and b[k] (where [k] denotes the k-th bit)

**Proof sketch:** Bit-independence means ⊕ acts as a function φ: {0,1} × {0,1} → {0,1} applied independently at each bit position. The only cancellative bit-independent operations on {0,1} are:
- XOR (a ⊕ b = a ⊕ c → b = c ✓) — but 1 XOR 1 = 0, so characteristic is 2
- The other cancellative option: φ(0,0)=0, φ(0,1)=1, φ(1,0)=1, φ(1,1)=0 — this IS XOR

So the only bit-independent cancellative operation is XOR, and XOR has characteristic 2, not zero. ∎

**Lean formalization path:** Enumerate all 16 functions {0,1}² → {0,1}, filter for cancellative, check characteristic. Decidable and small.

---

### Tier 4: Blocked Exits (mostly argumentation, partially formalizable)

**Theorem 6: Self-encoding requires unique representation.**

Statement: If ε: Terms → ℕ is injective and decode: ℕ → Terms is a left inverse (decode(ε(t)) = t), then the representation is unique (each n ∈ range(ε) has exactly one preimage).

**Proof:** Immediate from injectivity. One line.

This is trivial but it's the lemma that rules out redundant number systems: self-encoding needs injection, injection needs uniqueness, uniqueness needs non-redundant representation, non-redundant representation has carry propagation.

---

**Theorem 7: Unique positional addition requires carry.**

Statement: In any base-b positional representation with digit set {0, 1, ..., b-1} (non-redundant), there exist inputs a, b such that the output digit at position k depends on inputs at positions 0 through k (carry propagation).

**Proof:** Take a = b^k - 1 (all digits b-1 from position 0 to k-1), b_input = 1. The sum is b^k, which has a 1 at position k and 0s below. The output digit at position k (which is 1) depends on the carry chain from position 0 through k-1 (each position generates a carry). ∎

**Lean formalization path:** Direct construction of the witness. Needs Mathlib's Nat.digits and carry arithmetic.

---

## What NOT to try to prove

These are explicitly out of scope because they're either known results in new language or speculative:

| Claim | Why not to formalize |
|---|---|
| "The halting problem makes register normalization undecidable" | This IS the halting problem. Formalizing it adds nothing to Turing 1936 |
| "The impossibility hierarchy is one impossibility at four levels" | This is an organizational claim, not a theorem |
| "Observer = register" | Physical interpretation, not mathematics |
| "Reality is normalization" | Philosophy |
| "The hierarchy connects to P vs NP" | Structural analogy, no theorem to prove |

---

## Implementation plan

### Phase 1: Term algebra and encoding infrastructure

**New file: `SpectralArithmetic/Encoding.lean`**

Define:
```
inductive Term where
  | f₀ : Term
  | f₁ : Term
  | z  : Term
  | compose : Term → Term → Term
  | oplus : Term → Term → Term
  | obs : Term → Term
```

Define eval: Term → State (interpretation in any DynSemiring).

Define obs_rewrite: Term → Term (one-step Leibniz rewrite — oriented rewriting from confluence.md).

Define obs_rewrite_iter: ℕ → Term → Term (k-step rewriting).

~50 lines. No dependencies beyond Basic.lean.

### Phase 2: Pairing lower bound

**New file: `SpectralArithmetic/Pairing.lean`**

Prove Theorems 3 and 4.

Theorem 3 (addition is not injective on pairs): direct counterexample, ~10 lines.

Theorem 4 (injective pairings are super-linear): pigeonhole argument, ~40 lines. Needs `Mathlib.Combinatorics.Pigeonhole` or equivalent.

### Phase 3: The ⊕ impossibility

**New file: `SpectralArithmetic/OplusImpossibility.lean`**

Prove Theorem 5 (no operation is cancellative + char-zero + bit-independent).

Enumerate the 16 Boolean functions, filter, check. ~60 lines. Decidable — `decide` tactic might close it.

### Phase 4: The core obstruction theorem

**New file: `SpectralArithmetic/Obstruction.lean`**

Prove Theorem 1 (existential version: some term breaks the morphism).

Depends on: Encoding.lean (term algebra), Semiring.lean (eigenvalue theorem), Pairing.lean (super-linearity).

Strategy:
1. Take t = compose(f₁, f₁)
2. Compute obs_semantic side: eigenvalue is ε(t), so obs(f_{ε(t)}) = ε(t) · f_{ε(t)}
3. Compute obs_rewrite side: Leibniz gives oplus(compose(f₁, compose(f₁, f₁)), compose(compose(f₁, f₁), f₁)) which simplifies to oplus(f₂, f₂) = smul 2 f₂
4. The encoding of smul 2 f₂ is ε(oplus(f₂, f₂)), which is a DIFFERENT eigenstate than ε(t) · f_{ε(t)} (which is smul ε(t) (f_{ε(t)}))
5. For any ε with ε(compose(f₁, f₁)) ≥ 3 (which any reasonable encoding satisfies), ε(t) ≠ 2, so the eigenvalues differ

~80-120 lines. This is the hardest proof. May need sorry on some steps initially.

### Phase 5 (stretch): Trajectory divergence

**Extend `SpectralArithmetic/Obstruction.lean`**

Prove Theorem 2 (trajectories diverge at some depth k).

Depends on: everything above + induction on k.

Strategy: Show by induction that after k Leibniz applications, the number of summands is 2^k, and the encoding of 2^k summands via any super-linear pairing exceeds the semantic eigenvalue ε(t)^k for large enough k.

~100-150 lines. May require significant Mathlib infrastructure for growth-rate comparison.

### Phase 6: Blocked exit lemmas

**Extend `SpectralArithmetic/Pairing.lean`**

Prove Theorems 6 and 7 (self-encoding needs uniqueness; unique positional addition has carry).

Theorem 6: one line from injectivity.
Theorem 7: explicit witness construction, ~30 lines.

---

## File summary

| File | Theorems | Lines (est.) | Dependencies |
|---|---|---|---|
| `Encoding.lean` | Term type, eval, rewrite | ~50 | Basic.lean |
| `Pairing.lean` | Thms 3, 4, 6, 7 | ~90 | Mathlib.Combinatorics |
| `OplusImpossibility.lean` | Thm 5 | ~60 | Mathlib basics |
| `Obstruction.lean` | Thms 1, 2 | ~200-270 | Encoding, Semiring, Pairing |

Total: ~400-470 lines of new Lean across 4 files.

---

## Sorry budget

**No sorry allowed:**
- Theorems 3, 5, 6 (trivial/decidable)
- Theorem 1 (the core result — this is the whole point)

**Sorry acceptable on first pass:**
- Theorem 4 (pigeonhole — may need Mathlib lemma hunting)
- Theorem 7 (carry witness — may need digit arithmetic infrastructure)
- Theorem 2 (trajectory divergence — growth-rate induction is hard)

---

## Success criteria

**Minimum viable result:** Theorems 1, 3, 5 proved sorry-free. These give: (a) addition is not injective on pairs, (b) no bit-independent operation is cancellative + char-zero, (c) there exists a term whose encoding breaks the coalgebra morphism. This is enough for a "the trilemma is a theorem" claim.

**Full result:** All 7 theorems proved. The encoding obstruction is machine-checked from pairing lower bounds through the ⊕ impossibility to the coalgebra morphism failure.

---

## What this does NOT prove

Even with all 7 theorems, the following remain pen-and-paper arguments:

1. The impossibility hierarchy (addition → state → halting) — organizational, not a theorem
2. The carry non-locality argument — an informal argument about hardware, not a formal proof about abstract algebra
3. Any physical interpretation — speculative
4. Connection to P vs NP — structural analogy

The Lean formalization proves the **trilemma** and its algebraic prerequisites. The rest of the document stack (information-domain.md, addition-non-locality.md, impossibility-hierarchy.md, observer-as-register.md) remains theory/speculation that the formalization does not address.

---

## Also update

- `SpectralArithmetic.lean` (root module): add imports for new files
- `README.md`: add new files to the table, add encoding obstruction to results
- The five theory documents: add notes pointing to formalized versions where applicable

## Verification

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /path/to/worktree
lake build
```
