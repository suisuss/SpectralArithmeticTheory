# Encoding Obstruction: Lean Formalization

> **Authoritative source:** [`SpectralArithmetic/Obstruction/README.md`](../../../../SpectralArithmetic/Obstruction/README.md)
> contains the up-to-date file listing, theorem counts, and interface description.
> This document provides the mathematical narrative.

## The Result

Five Lean files prove, sorry-free, that no injective encoding of terms can serve as a coalgebra morphism for the observation operator. The eval-quote diagram does not commute. This is the **intension/extension gap** made machine-checkable.

```
        eval
Terms --------→ State
  |                |
  | ε (encode)     | obs (eigenvalue scaling)
  |   [intensional:|   [intensional:
  |    naming]     |    reads eigenvalue]
  ↓                ↓
  ℕ  --------→  State
     obs_code (rewrite + re-encode)
     [extensional: Leibniz unfolds, then re-names]
```

**The diagram does not commute** — universally, for ALL injective encodings and ALL compound observation terms (`no_coalgebra_morphism`).

**The meaning is preserved** — universally, for ALL terms in ALL models (`semantic_invariance_general`).

**There is no fixed point** — three levels of extensionalization produce three provably distinct terms (`substitution_chain_distinct`).

**The gap grows** — each extensionalization more than doubles term size (`extensionalize_more_than_doubles`).

## Why Term-Level Is the Right Level

The intension/extension gap IS a gap between terms: the intensional term (folded, named) and the extensional term (unfolded by substitution) are structurally different:

```
obs(compose(f₁, f₁))                                    ← intensional: the form as a unit
  ≠  (by decide, using DecidableEq on Term)
oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁)))      ← extensional: the form unfolded by Leibniz
```

Any injective `ε` maps distinct terms to distinct codes. No assumptions about State needed. The `obsRewrite_eval` theorem confirms: at the State level, the two sides ARE equal (semantics is preserved). The gap is in the naming, not in the meaning.

## Relationship to Theory Documents

| Theory document | What it claims | What the Lean proves |
|---|---|---|
| `encoding-obstruction.md` | The intension/extension gap is irreducible | `no_coalgebra_morphism` (universal), `substitution_chain_distinct` (no fixed point), `semantic_invariance_general` (meaning preserved) |
| `information-domain.md` | ⊕ enters through extensionalization and can't be removed | `oplus_bitwise_impossible`, `bitwise_diagonal_char_two` (forced char 2 vs. required char 0) |
| `addition-non-locality.md` | Carry propagation forces external state | `carry_propagation_general` (any base b ≥ 2) |
| `impossibility-hierarchy.md` | No bottom: substitution → ⊕ → carry → halting | First three levels proved; fourth is a direct reading of `substitution_chain_distinct` |
| `convergence-conjecture.md` | Is there a non-divergent variant? | `WeakConvergence` vs `TotalDivergence` formalized as precise Prop definitions; `discrepancy_nonzero_at_zero` proved |

The Lean formalization proves the **complete algebraic core**. The halting/undecidability reading follows directly from "no fixed point." The interpretation (observer, physics) rests on this core but is not machine-checked.
