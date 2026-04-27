# Plan: Lean Formalization of Complexity Asymmetry

## Context

The SpectralArithmeticTheory project has proved several algebraic results about encoding obstruction — no injective encoding commutes with Leibniz extensionalization, term size more than doubles per rewrite, the substitution chain has no fixed point. These results establish a structural asymmetry between verification (reading eigenvalues, O(1)) and construction (normalizing terms, exponential). The user wants to formalize this connection to P vs NP in Lean, making the structural analogy machine-checked while being honest about what is proved vs conjectured.

## What We're Building

A new file `SpectralArithmetic/Obstruction/Complexity.lean` that formalizes the verification/construction asymmetry, connecting existing proved results into a coherent statement of the P vs NP structural analogy.

## Implementation

### File: `SpectralArithmetic/Obstruction/Complexity.lean` (NEW)

Imports: `Encoding`, `Oplus`, `Convergence`, `Core.Semiring`
Namespace: `SpectralMonoid.Complexity`

#### Part 1: Position-Existence (fully provable)

- `obs_bit_values`: obs restricted to {f₀, f₁} gives {z, f₁} — Boolean values from eigenvalue arithmetic. Proof: case split on hypothesis, apply `obs_f₀` / `obs_f₁`.
- `eigenvalue_bit_connection`: connect `bitAt` (from Oplus.lean) to eigenvalue observation — the k-th bit of eigenvalue n IS the Boolean shadow of obs at position k. Proof: unfold `bitAt` definition.

#### Part 2: Normalization Depth (fully provable definitions)

- `isObsNormal : Term → Bool` — decidable check: no `obs(compose(_,_))` sub-terms remain. Returns `Bool`, computable.
- `normDepthBounded : ℕ → Term → ℕ` — count deepRewrite steps until obs-normal (with fuel bound). Fully computable, no sorry.
- Concrete depth computations for specific terms via `by decide`:
  - `normDepthBounded _ (.obs .f₁) = 0` (verification: zero steps)
  - `normDepthBounded _ (.obs t_f₂) = 1` (one Leibniz step)

#### Part 3: Nested Obs-Compose Family (provable size bounds)

- `nestedObsCompose : ℕ → Term` — depth-d terms: `d=0` is `compose f₁ f₁`, `d+1` wraps in `obs(compose(-, -))` with two copies.
- `nestedObsCompose_size`: termSize = 5*2^d - 2 (proof: induction + omega)
- `compounding_size_lower_bound`: termSize ≥ 2^d (proof: induction + omega)
- Concrete normDepth values for d=0,1,2 via `decide` (values TBD — Lean decides the correct answer)

#### Part 4: Verification vs Construction Asymmetry (fully provable)

- `verification_vs_construction_asymmetry`: conjunction of:
  1. Eigenvalue theorem: `obs(iterS n) = n * iterS n` for all n (is `eigenvalue n`)
  2. Term size doubling: `termSize(nestedObsCompose(d+1)) > 2 * termSize(nestedObsCompose d)` (proof: unfold + omega)

#### Part 5: Exponential Normalization Lower Bound (sorry)

- `normDepth_nestedObs_exponential`: normDepthBounded ≥ 2^d for nestedObsCompose d
- Marked `sorry` — requires characterizing the tree structure of `iterDeepRewrite k (nestedObsCompose d)` to show `obs(compose)` patterns persist. Genuine research.

#### Part 6: P vs NP Structural Analogy (fully provable)

- `PvsNP_StructuralAnalogy : Prop` — conjunction of three proved results:
  1. Verification is O(1): eigenvalue theorem
  2. Construction size is exponential: compounding_size_lower_bound
  3. No encoding bridges the gap: no_coalgebra_morphism
- `PvsNP_analogy_holds`: proof assembling the three components. No sorry.
- Doc comment clearly states this is a structural analogy, NOT an implication of P != NP.

#### Part 7: SAT Encoding Sketch (definitional only)

- `varTerm`, `andTerm`, `orTerm` — sketch definitions mapping SAT structure to Terms
- No theorems — this is a research direction marker, not a claim

### File: `SpectralArithmetic.lean` (MODIFY)

Add: `import SpectralArithmetic.Obstruction.Complexity` after the Convergence import.

## Sorry Budget

| Theorem | Status | Why |
|---|---|---|
| `normDepth_nestedObs_exponential` | `sorry` | Requires invariant characterization of iterDeepRewrite on nested terms |
| Everything else | Proved | Uses `decide`, `rfl`, `omega`, `eigenvalue`, or assembly of existing results |

## Risks

1. **`decide` timeouts**: `normDepthBounded` on `nestedObsCompose 2` may be too large for `decide`. Fallback: prove by `native_decide` or reduce the depth tested.
2. **Nat subtraction**: `5*2^d - 2` needs care. Will add `have : 5 * 2^d >= 2` guards.
3. **omega vs 2^d**: `omega` handles linear arithmetic but may struggle with exponentials. Fallback: `linarith` with `Nat.one_le_two_pow`.

## Verification

1. `lake build` — must compile without errors (sorry is allowed, compilation failure is not)
2. Check that all `sorry`-free theorems are genuinely machine-checked
3. Verify concrete `decide` proofs give correct normalization depth values

## Files Modified

- `SpectralArithmetic/Obstruction/Complexity.lean` (NEW) — ~200 lines
- `SpectralArithmetic.lean` — add 1 import line
