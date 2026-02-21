# Spectral Arithmetic: Peano Axioms & ZF from the Eigenvalue Structure of a Derivation

## What This Is

A coalgebraic axiom system — a commutative semiring with a derivation operator — from which Peano arithmetic emerges as theorems rather than axioms. The eigenvalue structure of the derivation (abstract d/dx) provides a natural arithmetic interpretation: the n-th iterate of the generator is an eigenvector with eigenvalue n, and the Peano axioms follow from the algebraic structure.

**Core result:** Given a commutative semiring (State, compose, ⊕) with a derivation obs satisfying the Leibniz rule and characteristic zero, the orbit of the identity under the generator has eigenvalue structure that reproduces all nine axioms of Peano Arithmetic. Several axioms that appear necessary at the base level (cancellation, infinite orbit) become theorems as the algebraic structure enriches.

**Lean 4 formalization:** The algebraic core is machine-checked. All proofs from ℕ through ℚ compile against Mathlib v4.28.0. See [Lean status](#lean-4-formalization) below.

## The Construction

Four primitives: **State** (an uninterpreted type), **compose** (binary operation), **obs** (observation operator — the abstract d/dx), **⊕** (addition).

The natural numbers emerge as follows:

1. **f₀** is the identity state: compose(f₀, s) = s
2. **f₁** is the generator, fixed by obs: obs(f₁) = f₁
3. **Successor** is multiplication by the generator: S(s) = compose(f₁, s)
4. **The eigenvalue theorem:** obs(fₙ) = n · fₙ — the observation operator reads off which number a state represents
5. **Peano axioms** follow: f₀ is not a successor (eigenvalue 0 ≠ eigenvalue n for n ≥ 1), successor is injective (cancellation), induction holds on the orbit

The eigenvalue theorem is proved by induction using the Leibniz rule. The infinite orbit property (A8) — which must be axiomatized in the base system — becomes a *theorem* in the semiring: if the orbit cycled, eigenvalue scaling would force n · f₀ = z, contradicting characteristic zero.

## What's Proved vs. What's Conjectured

### Machine-checked (Lean 4)

| Result | File |
|---|---|
| Peano axioms P1-P5 from A1-A7 + InfiniteOrbit | Core/Basic.lean |
| Eigenvalue theorem: obs(fₙ) = n · fₙ | Core/Semiring.lean |
| A8 (infinite orbit) as theorem from char zero | Core/Semiring.lean |
| All nine PA axioms (PA1-PA9) | Verification/PeanoTest.lean |
| A7 (cancellation) as theorem from integral domain | Core/IntegralDomain.lean |
| Power rule: obs(gⁿ⁺¹) = (n+1) · gⁿ · obs(g) | Core/IntegralDomain.lean |
| Eigenvalue theorem for ℤ (negative eigenvalues) | Core/IntegralDomain.lean |
| Eigenvalue 1/q for q-th roots | Core/Rational.lean |
| Torsion-freeness and generalized cancellation | Core/Rational.lean |
| Boolean algebra on {z, f₀} via compose/oplus/oneg | Verification/ZFTest.lean |
| F1-F3 axiom class (set-theoretic closure) | Verification/ZFTest.lean |
| ZF axioms verified (sets as predicates, dependency-tracked) | Verification/ZFTest.lean |
| Complex extension: j⁴ = f₀, quarter-turn periodicity | Core/Complex.lean |
| ℝ eigenvalue theorem (axiomatized, not derived) | Core/Complete.lean |
| ℂ eigenvalue theorem (axiomatized, not derived) | Core/Complex.lean |
| Forward model: AddMonoidAlgebra ℝ ℝ satisfies all 20 axioms (A1–F3) | Verification/Model.lean |

### Pen-and-paper (theory documents, not formalized)

| Claim | Document | Status |
|---|---|---|
| PA equiconsistency: Con(A1-A8) ↔ Con(PA) | [pa-equiconsistency](docs/theory/pa-equiconsistency.md) | Rigorous argument with countermodels |
| ZF equiconsistency: Con(A1-F3) ↔ Con(ZF) | [zf-equiconsistency](docs/theory/zf-equiconsistency.md) | Relies on Jech-Sochor theorem |
| Self-representation and Gödel encoding | [self-representation](docs/theory/computation/self-representation.md) | Standard PA-strength argument |
| Confluence and canonical normal forms | [confluence](docs/theory/computation/confluence.md) | Term rewriting analysis |
| e derived as f(1) = Σ 1/n! | [spectral-arithmetic-complete](docs/theory/spectral-arithmetic-complete.md) | Requires analytic model (not in Lean) |
| Taylor series as theorem | [real-extension](docs/theory/real-extension.md) | Requires analytic model |

### Open conjectures

| Conjecture | Description |
|---|---|
| **Syntax-semantics bisimulation** | Does the Gödel encoding create a behavioral equivalence between the syntactic coalgebra (term rewriting) and the semantic coalgebra (eigenvalue observation)? Precisely: is there a bisimulation between (State, obs_semantic) and (State, obs_code)? |
| **Analytic model connection** | Building State = smooth functions, compose = multiplication, obs = d/dx in Lean and verifying all axioms — connecting the abstract algebra to actual eigenfunctions of differentiation. |

## Origin

This construction emerged from studying finite differences (the discrete analogue of differentiation):

1. The forward difference operator Δ reduces polynomial degree by 1
2. Exponentials survive Δ indefinitely — they are eigenfunctions
3. The discrete-to-continuous bridge (Δ → d/dx as step size → 0) yields e
4. Reframing 1 as "the eigenfunction with eigenvalue 1" rather than "the constant that differentiation kills"
5. Building the naturals via successor, then extending to ℤ, ℚ, ℝ as concentric circles of reachability

## Progressive Axiom Layering

A distinctive feature: axioms that appear necessary at one level become theorems at the next.

| Level | Structure | Axioms added | Axioms that become theorems |
|---|---|---|---|
| **A (Base)** | Commutative monoid + obs + generator | A1-A7, A8 | — |
| **B (Semiring)** | + ⊕, Leibniz rule, char zero | B1-B5 | **A8** (infinite orbit) |
| **C (Integral domain)** | + inverses, no zero divisors | C1-C3 | **A7** (cancellation) |
| **D (ℚ-algebra)** | + q-th roots, unique divisibility | D1-D2 | — |
| **E (ℝ-algebra)** | + Cauchy completeness | E1 | — |
| **F (Predicates)** | + completed orbit, comprehension, replacement | F1-F3 | — |
| **G (ℂ-algebra)** | + imaginary unit j | G1 | — |

Total: 21 axioms, 4 primitives. The number tower ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ in a single eigenvalue space.

## Lean 4 Formalization

```
SpectralArithmetic/
├── Core/
│   ├── Basic.lean           ← A1-A7, Peano axioms P1-P5, iterS arithmetic
│   ├── Semiring.lean        ← B1-B5, eigenvalue theorem, A8 as theorem
│   ├── IntegralDomain.lean  ← C1-C3, A7 as theorem, power rule, ℤ eigenvalues
│   ├── Rational.lean        ← D1-D2, eigenvalue 1/q, torsion-freeness
│   ├── Complete.lean        ← E1 (axiomatized), ℝ eigenvalue theorem (axiomatized)
│   └── Complex.lean         ← G1, j⁴ = f₀, ℂ eigenvalue theorem (axiomatized)
├── Verification/
│   ├── PeanoTest.lean       ← PA1-PA9 verification, recursion theorem
│   ├── ZFTest.lean          ← ZF1-ZF9 verification (sets as predicates)
│   └── Model.lean           ← Forward model: AddMonoidAlgebra ℝ ℝ satisfies A1–F3
└── Obstruction/             ← Encoding obstruction (see suisuss/Obstruction for general version)
    ├── Encoding.lean        ← Term algebra, obsRewrite, trajectory divergence
    ├── Main.lean            ← no_coalgebra_morphism, compilation ≠ execution
    ├── Oplus.lean           ← Bitwise ⊕ impossibility
    ├── Pairing.lean         ← Pairing unboundedness, carry propagation
    └── Convergence.lean     ← WeakConvergence vs TotalDivergence (open)
```

Build: `lake build` (requires Lean 4 v4.28.0 + Mathlib v4.28.0)

**What the Lean code proves:** If you have a commutative semiring with a derivation satisfying the Leibniz rule and characteristic zero, the eigenvalue theorem holds, the Peano axioms are consequences, and axioms progressively become theorems as algebraic structure enriches.

**What the Lean code does not prove:** The connection to actual eigenfunctions of d/dx, the derivation of e, the Taylor series, the PA/ZF equiconsistency results, or the self-representation/computation material. These remain pen-and-paper arguments in the theory documents.

## The Encoding Obstruction

The framework proves its own limitation: no injective encoding of its terms can faithfully preserve the semantics. This is the **encoding trilemma** — three properties, any two compatible, all three impossible:

1. **Injectivity** — distinct terms get distinct codes
2. **Homomorphism** — the encoding respects operations
3. **Non-trivial semantics** — distinct terms can denote the same value

The spectral framework makes this concrete. The eigenvalue theorem says `obs(f_n) = n · f_n` — observation reads off the number. But encoding this process and reproducing it internally produces a different answer than performing the observation directly (`encoding_obstruction_term`). The system can observe its eigenstates but cannot faithfully encode the act of observation.

This obstruction is not specific to the spectral framework. It holds for any system with enough structure to be interesting:

| System | Source of non-trivial semantics | Where the trilemma bites |
|---|---|---|
| **This framework** | Leibniz rule rewrites `obs(compose(a,b))` to a structurally different term | `Obstruction/Main.lean` |
| **Peano arithmetic** | `S(S(0))` and `S(0)+S(0)` are different terms for 2 | [Obstruction repo: Peano.lean](https://github.com/suisuss/Obstruction) |
| **ZF set theory** | `⋃∅` and `∅` are different terms for the empty set | [Obstruction repo: ZF.lean](https://github.com/suisuss/Obstruction) |

The encoding-specific results live in [`SpectralArithmetic/Obstruction/`](SpectralArithmetic/Obstruction/). The general results — independent of the spectral framework, proved for PA, ZF, and all term algebras with Leibniz observation — are in the standalone [Obstruction](https://github.com/suisuss/Obstruction) repository.

This is the structural barrier to completeness. To escape incompleteness while retaining self-reference, a system would need an encoding that is both injective and homomorphic. The trilemma proves that's impossible. Gödel proved *that* you can't escape. The encoding obstruction characterizes *what you'd need to overcome* — and proves it can't be overcome.

## Connections to Existing Work

This is a synthesis of ideas from several fields:

| Field | What it contributes | What's new here |
|---|---|---|
| **Differential algebra** (Ritt, Kolchin) | Commutative rings with derivations, Leibniz rule | Interpreting eigenvalue structure as arithmetic |
| **Universal coalgebra** (Rutten, Jacobs) | Bisimulation, coinduction, final coalgebras | Combining coalgebraic primitives with derivation structure |
| **Bialgebraic semantics** (Turi, Plotkin) | Algebra (syntax) + coalgebra (semantics) unified | Asking whether Gödel encoding is a coalgebra morphism |
| **Recursion theory** (Kleene) | Self-referencing programs, fixed points | Strengthening to coalgebraic bisimulation (not just syntactic fixed points) |

## Theory Documents

| File | Contents |
|---|---|
| [spectral-arithmetic-complete](docs/theory/spectral-arithmetic-complete.md) | Complete unified theory (Parts 1-9) |
| [axioms](docs/theory/axioms.md) | Formal axiom set (A1-A8) |
| [pa-equiconsistency](docs/theory/pa-equiconsistency.md) | PA equiconsistency proof with countermodels |
| [path-b-obs-structure](docs/theory/path-b-obs-structure.md) | Semiring structure, eigenvalue theorem, A8 as theorem |
| [integer-extension](docs/theory/integer-extension.md) | ℤ extension, A7 as theorem, power rule |
| [rational-extension](docs/theory/rational-extension.md) | ℚ extension, eigenvalue 1/q |
| [real-extension](docs/theory/real-extension.md) | ℝ extension, Cauchy completion |
| [complex-extension](docs/theory/complex-extension.md) | ℂ extension, imaginary unit |
| [zf-test-suite](docs/theory/zf-test-suite.md) | ZF axioms verified against framework |
| [zf-equiconsistency](docs/theory/zf-equiconsistency.md) | ZF equiconsistency proof |
| [transfinite-ordinals](docs/theory/transfinite-ordinals.md) | Transfinite ordinals in predicate hierarchy |
| [role-of-x](docs/theory/role-of-x.md) | Observation parameter, x-free framework |
| [self-representation](docs/theory/computation/self-representation.md) | Gödel encoding, self-representation, incompleteness |
| [confluence](docs/theory/computation/confluence.md) | Confluence, termination, canonical normal forms |

### Background documents

| File | Contents |
|---|---|
| [eulers-number-and-differentials](docs/theory/eulers-number-and-differentials.md) | Background: eigenfunctions of d/dx, discrete-continuous bridge |
| [spectral-arithmetic](docs/theory/spectral-arithmetic.md) | Original construction: numbers as eigenfunctions |
| [set-constructor-and-deriving-e](docs/theory/set-constructor-and-deriving-e.md) | Set constructor, deriving e |
| [extending-the-number-systems](docs/theory/extending-the-number-systems.md) | Extension to ℤ, ℚ, ℝ |

## Reading Order

For the core results: **Core/Semiring.lean** (eigenvalue theorem) → **Verification/PeanoTest.lean** (PA verification) → **pa-equiconsistency** (why these axioms and not others).

For the full theory: **spectral-arithmetic-complete** gives everything in one document.

For the encoding obstruction: [**Obstruction repo**](https://github.com/suisuss/Obstruction) (the encoding trilemma for PA, ZF, and all term algebras) → [**Obstruction/**](SpectralArithmetic/Obstruction/) (the same obstruction applied to this framework's eigenvalue structure).

For the most original open question: **self-representation** (the syntax-semantics bisimulation conjecture).
