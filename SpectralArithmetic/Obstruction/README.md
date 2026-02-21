# Obstruction

This directory is the interface between SpectralArithmeticTheory and the general encoding obstruction results formalized in the standalone [Obstruction](https://github.com/suisuss/Obstruction) repository.

## The Crux

**Mathematics is substitution. Substitution is open-ended. There is no bottom.**

Every formal expression can be unfolded (extensionalized — substituting definitions, applying rules) or re-named (intensionalized — giving a form a symbol). These are the only two moves, and they never reach a fixed point. A "complete" system would be one where this switching stops — where an encoding faithfully captures its own execution. We prove it can't:

- **No coalgebra morphism exists** — for ANY injective encoding and ANY compound observation term, the extensionalized code differs from the intensionalized code (`no_coalgebra_morphism`)
- **The meaning is preserved** — semantics is invariant under extensionalization; the gap is in the form, not the content (`semantic_invariance_general`)
- **No fixed point** — each level of extensionalization produces a provably distinct term (`substitution_chain_distinct`)
- **The gap grows** — each extensionalization more than doubles term size (`extensionalize_more_than_doubles`)
- **There is no bottom** — the halting problem for self-executing encodings is not a separate result; it IS the non-existence of the fixed point, read temporally

This is the structural explanation behind Gödel incompleteness, the halting problem, and the necessary separation of compilation from execution. Not a new impossibility alongside them — the same impossibility, viewed algebraically.

## What lives where

| Location | Content |
|---|---|
| [`suisuss/Obstruction`](https://github.com/suisuss/Obstruction) | General obstruction framework: the crux formalized for PA, ZF, and universally for all term algebras with compose + obs + Leibniz |
| This directory (`encoding-obstruction` branch) | The obstruction applied to SpectralArithmeticTheory's `DynSemiring` axiom tower, plus the convergence conjecture |

The general results (Obstruction repo) are independent of SpectralArithmeticTheory. They prove the intension/extension gap is structural — it holds for Peano arithmetic's term algebra, for ZF's term algebra, and for any term algebra where observation obeys the Leibniz rule. The encoding-specific results (this directory) import `DynSemiring` and prove the obstruction for this project's eigenvalue framework.

## General results (Obstruction repo)

The standalone [Obstruction](https://github.com/suisuss/Obstruction) repository formalizes the crux as a self-contained Lean project, applicable to any formal system with arithmetic. The central result is the **encoding trilemma**: three properties — injectivity, homomorphism, non-trivial semantics — any two compatible, all three impossible.

- **`General.lean`** — `Obstruction`, `ConditionalObstruction`, `InjectiveObstruction` structures. Framework for stating and proving obstruction results parametrically over arbitrary atom types.
- **`Encoding.lean`** — The structural obstruction: for any term algebra with compose + obs + Leibniz rule, no injective encoding commutes with observation. The Leibniz rule extensionalizes observation of composed forms, introducing addition, which is structurally distinct from the original — and any injective encoding must reflect the distinction.
- **`Peano.lean`** — Both corners of the trilemma for PA. Corner 1: `eval` is a homomorphism but not injective (`S(S(0))` and `S(0)+S(0)` both map to 2). Corner 2: any injective encoding cannot respect PA semantics (three `InjectiveObstruction` witnesses for succ/add, mul/zero, succ/mul).
- **`ZF.lean`** — Both corners of the trilemma for ZF. Four set-theoretic identities (⋃∅ = ∅, {a,a} = {a}, ⋃{a} = a, 𝒫(∅) = {∅}) each independently produce both corners: any function respecting the identity is not injective; any injective encoding cannot respect the identity.
- **`Arithmetic.lean`** — Bool characteristic-2 impossibility, pairing unboundedness (pigeonhole), carry propagation witnesses. These close off representation-level escape routes: the oplus that extensionalization introduces is inherently non-local.

## Encoding-specific results (this directory)

### The obstruction (proved, sorry-free)

| File | Lines | Theorems | What it proves |
|---|---|---|---|
| `Encoding.lean` | 347 | 22 | Term algebra, eval, obsRewrite (extensionalization), deepRewrite (iterated), termSize, trajectory divergence (>2× growth), general obstruction for all a,b |
| `Main.lean` | 299 | 24 | `no_coalgebra_morphism` (universal), `compilation_ne_execution`, `semantic_invariance_general`, `no_encoding_fixpoint`, `trajectory_divergence` |
| `Oplus.lean` | 127 | 6 | No bitwise operation satisfies comm + cancel + identity + char 0; Bool→ℕ bridge |
| `Pairing.lean` | 119 | 7 | Addition not injective on pairs, injective pairings unbounded, carry propagation (general, any base b ≥ 2) |

### The convergence conjecture (open)

| File | Lines | Theorems | What it proves |
|---|---|---|---|
| `Convergence.lean` | 337 | 24 | Iterated extensionalization, encoding families, discrepancy measure, `WeakConvergence` and `TotalDivergence` as precise Prop definitions, proved: discrepancy nonzero at depth 0, semantic trajectory constant, the two conjectures are contradictory |

**The open question:** Does `WeakConvergence` or `TotalDivergence` hold?

- If convergence: the obstruction is a finite-depth phenomenon; `e` emerges as the convergence rate; the analytic model (obs = d/dx) is selected by self-reference
- If divergence: the obstruction is total at every resolution; self-knowledge is structurally impossible even approximately

### Totals

| Metric | Value |
|---|---|
| Files | 5 |
| Lines | 1229 |
| Definitions + theorems | 90 |
| `sorry` | 0 |

## The picture

```
SpectralArithmetic/Core/         Axiom tower: compose, oplus, obs, eigenvalues
        │                        Derives PA, ZF, forward model
        │
        ▼
SpectralArithmetic/Obstruction/  WHY self-encoding fails:
        │                        intension/extension gap (no fixed point)
        │                        ⊕ non-locality (carry propagation)
        │                        compilation ≠ execution (necessary separation)
        │                        there is no bottom (halting = no fixed point)
        │
        ▼
Convergence.lean                 OPEN: is there a non-divergent variant?
                                 WeakConvergence vs TotalDivergence

suisuss/Obstruction              The encoding trilemma, generalized:
                                 injectivity ∧ homomorphism ∧ non-trivial = ⊥
                                 proved for PA (eval collisions),
                                 ZF (set-theoretic identities),
                                 and all term algebras with Leibniz obs
```

All results are sorry-free.
