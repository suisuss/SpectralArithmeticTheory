# Plan: Forward Model for ZF Equiconsistency

## Context

The Spectral Arithmetic Theory has a pen-and-paper equiconsistency proof: Con(ZF) ↔ Con(A1-F3). The backward direction (Framework → ZF) is formalized in `ZFTest.lean`. The **forward direction** (ZF → Framework) — constructing a model of all 20 axioms inside ZF — is only on paper. This plan formalizes it in Lean by building an explicit `DynZF` instance on `AddMonoidAlgebra ℝ ℝ`.

## The Model

**State** = `AddMonoidAlgebra ℝ ℝ` (finitely-supported functions `ℝ → ℝ` with convolution multiplication)

| Framework primitive | Model definition |
|---|---|
| compose | Ring multiplication (`· * ·`) |
| oplus | Ring addition (`· + ·`) |
| obs | Eigenvalue-weighting: `c.sum fun α a => single α (α * a)` |
| f₀ | `1` (= `single 0 1`) |
| f₁ | `single 1 1` |
| z | `0` |
| oneg | `Neg.neg` |
| f₁_inv | `single (-1) 1` |
| root q | `single (1/q) 1` |
| qdiv n a | `Finsupp.mapRange ((↑n)⁻¹ * ·) _ a` |
| ratEigen r | `single r 1` |
| realEigen α | `single α 1` |
| rsmul α x | `Finsupp.mapRange (α * ·) _ x` |

## New File

**`SpectralArithmetic/Model.lean`** — one new file, ~300-400 lines.

## Implementation

### Phase 1: Helpers (~50 lines)

```
modelObs_zero   : modelObs 0 = 0                               — Finsupp.sum_zero_index
modelObs_single : modelObs (single α a) = single α (α * a)     — sum_single_index
modelObs_add    : modelObs (a + b) = modelObs a + modelObs b   — sum_add_index'
nfoldSum_eq_nsmul : nfoldSum (+) 0 n x = n • x                 — induction on n
cpow_single_one : cpow (single r 1) n = single (n * r) 1       — induction on n
```

### Phase 2: SpectralMonoid instance (~40 lines)

Most fields are 1-liners from ring axioms (`one_mul`, `mul_assoc`, `mul_comm`, `zero_mul`). Non-trivial:

- **obs_f₁**: `modelObs_single` + `one_mul`
- **f₁_cancel**: `mul_left_cancel₀` from `NoZeroDivisors` instance (Mathlib provides this via `UniqueSums ℝ`)
- **f₀_ne_f₁**: Evaluate at 0 via `Finsupp.single_apply`, get `1 ≠ 0`
- **f₁_ne_z**: `Finsupp.single_ne_zero one_ne_zero`

### Phase 3: DynSemiring instance (~80 lines)

Algebraic fields are 1-liners. Two hard proofs:

- **leibniz** (KEY PROOF, ~40 lines): Double `induction_linear`. Reduce to single-single case: `(α+β)*(r*s) = α*r*s + r*(β*s)`, closed by `ring`.
- **char_zero** (~15 lines): Show `nfoldSum (+) 0 n 1 = ↑n` via helper, then `Nat.cast_ne_zero` + `single_ne_zero`.

### Phase 4: DynIntDomain instance (~15 lines)

- **f₁_inv_spec**: `single_mul_single` + `add_neg_cancel` + `mul_one`
- **oneg_spec**: `add_neg_cancel`
- **no_zero_divisors**: From Mathlib's `NoZeroDivisors` instance

### Phase 5: DynRational instance (~30 lines)

- **root_spec**: Use `cpow_single_one` helper, then `div_mul_cancel`
- **qdiv_spec**: `nfoldSum_eq_nsmul` + scalar arithmetic `n • (n⁻¹ * a) = a`

### Phase 6: DynComplete instance (~80 lines)

- **ratEigen/realEigen fields**: Mostly direct from `single_mul_single` + `mul_one`
- **eigenvalue_real**: `modelObs_single` matches `rsmul` definition
- **rsmul plumbing** (rsmul_nat, rsmul_compose, etc.): Some may use `sorry` on first pass — these are definitional bookkeeping, not mathematical content

### Phase 7: DynZF (~0 lines)

Automatic from existing `instDynZF` instance in `ZFTest.lean`.

## Sorry Budget

Core mathematical content (NO sorry):
- obs_f₁, obs_f₀, leibniz, char_zero, no_zero_divisors, eigenvalue_real, f₁_cancel

Plumbing that may use sorry on first pass:
- rsmul_nat, rsmul_compose, rsmul_inv_nat (connecting framework's nfoldSum to Lean's nsmul to mapRange)

## Key Mathlib Lemmas

| Lemma | Signature | Use |
|---|---|---|
| `AddMonoidAlgebra.single_mul_single` | `single m₁ r₁ * single m₂ r₂ = single (m₁ + m₂) (r₁ * r₂)` | Compose on singles |
| `Finsupp.sum_single_index` | `(single a b).sum h = h a b` (when `h a 0 = 0`) | obs on single |
| `Finsupp.sum_add_index'` | `(f + g).sum h = f.sum h + g.sum h` | obs additivity |
| `Finsupp.induction_linear` | Induction: zero, add, single cases | Leibniz proof |
| `Finsupp.single_ne_zero` | `b ≠ 0 → single a b ≠ 0` | f₁_ne_z |
| `NoZeroDivisors (AddMonoidAlgebra ℝ ℝ)` | Instance via `UniqueSums ℝ` | no_zero_divisors |
| `Finsupp.mapRange` | Apply function pointwise to coefficients | qdiv, rsmul |

## Key Imports

```lean
import SpectralArithmetic.ZFTest
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
```

## Also Update

- `SpectralArithmetic.lean` (root module): add `import SpectralArithmetic.Model`
- `README.md`: add Model.lean to the file table

## Verification

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/suisuss/.programming/sandbox/SpectralArithmeticTheory
lake build
```

All 3111+ jobs should pass. Any `sorry` will produce warnings but not errors.
