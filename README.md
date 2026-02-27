# Spectral Arithmetic

## Two Results

This project contains two independent but related results, both machine-checked in Lean 4.

**Part 1 — Eigenvalue Arithmetic.** A commutative semiring with a derivation operator (abstract d/dx) produces the natural numbers as eigenvalues. The Peano axioms are theorems, not assumptions. The number tower ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ emerges as concentric eigenvalue spectra within a single algebraic structure, and axioms assumed at lower levels become theorems at higher ones.

**Part 2 — The Encoding Obstruction.** The framework proves its own structural limitation: no injective encoding of terms can faithfully preserve semantics. This is the *encoding trilemma* — injectivity, homomorphism, and non-trivial semantics are pairwise compatible but jointly impossible. This characterizes *what you would need* to escape incompleteness, and proves it can't be obtained. The result is not specific to this framework — it holds for PA, ZF, and any term algebra with non-trivial semantics.

---

## Part 1: Eigenvalue Arithmetic

### The Construction

Four primitives: **State** (an uninterpreted type), **compose** (binary operation), **obs** (observation operator), **oplus** (addition).

The natural numbers emerge from the eigenvalue structure of obs:

1. **f₀** is the identity: compose(f₀, s) = s
2. **f₁** is the generator, fixed by obs: obs(f₁) = f₁
3. **Successor** is multiplication by the generator: S(s) = compose(f₁, s)
4. **The eigenvalue theorem:** obs(f_n) = n . f_n — obs reads off which number a state represents
5. **Peano axioms** follow: f₀ is not a successor (eigenvalue 0 vs n >= 1), successor is injective, induction holds on the orbit

The eigenvalue theorem is proved by induction using the Leibniz rule. The key mechanism: obs acts like d/dx, and the orbit elements behave like e^(nx) — eigenfunctions whose eigenvalue *is* their index.

### Progressive Axiom Elimination

Axioms assumed at one level become theorems at the next:

| Level | Structure | Axioms | What becomes a theorem |
|---|---|---|---|
| **A** | Commutative monoid + obs | A1-A7, A8 | — |
| **B** | + oplus, Leibniz rule, char zero | B1-B5 | **A8** (infinite orbit) |
| **C** | + inverses, no zero divisors | C1-C3 | **A7** (cancellation) |
| **D** | + q-th roots, unique divisibility | D1-D2 | — |
| **E** | + Cauchy completeness | E1 | — |
| **F** | + abstract set universe Ens | F1-F5 | — |
| **G** | + imaginary unit j | G1 | — |

A8 (the orbit doesn't cycle) must be assumed at Level A. At Level B, it becomes a *theorem*: if the orbit cycled, the eigenvalue theorem would force n . f₀ = z, contradicting characteristic zero. Similarly, A7 (cancellation) is an axiom at Level A but follows from integral domain structure at Level C.

### Set-Theoretic Verification (Level F)

The F-axioms lift the framework from PA-strength to ZF-strength by introducing an abstract type Ens (the set universe) with a membership relation. Unlike a naive sets-as-predicates approach (where everything is trivially satisfied by type theory), Ens is abstract — the F-axioms carry genuine content, demonstrated by machine-checked countermodels that falsify each axiom independently.

The F-axioms come in two tiers:

**Level 1 (sets of states):** F1 (orbit ensemble / Infinity), F2 (separation), F3 (replacement)

**Level 2 (sets of sets):** F4 (power ensemble / Power Set), F5 (family union / Union)

8 of 9 ZF axioms are proved at the Ens level. Foundation holds by type stratification. Choice is independent (same status as in ZF).

### What the Lean Code Proves

| Result | File |
|---|---|
| Eigenvalue theorem: obs(f_n) = n . f_n | Core/Semiring.lean |
| A8 (infinite orbit) as theorem from char zero | Core/Semiring.lean |
| A7 (cancellation) as theorem from integral domain | Core/IntegralDomain.lean |
| All nine PA axioms (PA1-PA9) | Verification/PeanoTest.lean |
| Power rule: obs(g^(n+1)) = (n+1) . g^n . obs(g) | Core/IntegralDomain.lean |
| Eigenvalue theorem for Z (negative eigenvalues) | Core/IntegralDomain.lean |
| Eigenvalue 1/q for q-th roots | Core/Rational.lean |
| ZF1-ZF8 from abstract Ens; countermodels for F1-F3 | Verification/ZFTest.lean, Countermodels.lean |
| Forward model: AddMonoidAlgebra R R satisfies all axioms | Verification/Model.lean |

### What Remains Pen-and-Paper

| Claim | Document | Status |
|---|---|---|
| PA equiconsistency: Con(A1-A8) <-> Con(PA) | [pa-equiconsistency](docs/theory/pa-equiconsistency.md) | Rigorous argument with countermodels |
| ZF equiconsistency: Con(A1-F5) <-> Con(ZF) | [zf-equiconsistency](docs/theory/zf-equiconsistency.md) | Relies on Jech-Sochor theorem |
| e derived as f(1) = sum 1/n! | [spectral-arithmetic-complete](docs/theory/spectral-arithmetic-complete.md) | Requires analytic model |
| Taylor series as theorem | [real-extension](docs/theory/real-extension.md) | Requires analytic model |

---

## Part 2: The Encoding Obstruction

Any system with enough structure to be interesting faces the encoding trilemma. Three properties — any two compatible, all three impossible:

1. **Injectivity** — distinct terms get distinct codes
2. **Homomorphism** — the encoding respects operations
3. **Non-trivial semantics** — distinct terms can denote the same value

The spectral framework makes this concrete. The eigenvalue theorem says obs(f_n) = n . f_n — observation reads off the number. But encoding this process and reproducing it internally produces a different answer than performing the observation directly. The system can observe its eigenstates but cannot faithfully encode the act of observation.

This is not a quirk of the spectral framework. It holds whenever a system has non-trivial semantics:

| System | Source of non-trivial semantics | File |
|---|---|---|
| **This framework** | Leibniz rule rewrites obs(compose(a,b)) to a structurally different term | Obstruction/Main.lean |
| **Peano arithmetic** | S(S(0)) and S(0)+S(0) are different terms for 2 | [Obstruction repo](https://github.com/suisuss/Obstruction) |
| **ZF set theory** | union(empty) and empty are different terms for the empty set | [Obstruction repo](https://github.com/suisuss/Obstruction) |

The connection to Part 1: the eigenvalue theorem gives the framework genuine semantic content (obs collapses distinct algebraic expressions to the same eigenvalue). The encoding obstruction proves that this semantic richness is exactly what prevents faithful self-encoding. Completeness would require an encoding that is both injective and homomorphic — the trilemma proves that's impossible.

Godel proved *that* you can't escape incompleteness. The encoding obstruction characterizes *what you would need* — and proves it can't be obtained.

---

## Origin

This construction emerged from studying finite differences (the discrete analogue of differentiation):

1. The forward difference operator reduces polynomial degree by 1
2. Exponentials survive indefinitely — they are eigenfunctions
3. The discrete-to-continuous bridge (step size -> 0) yields e
4. Reframing 1 as "the eigenfunction with eigenvalue 1" rather than "the constant that differentiation kills"
5. Building the naturals via successor, then extending to Z, Q, R as concentric eigenvalue spectra

## Lean 4 Formalization

```
SpectralArithmetic/
├── Core/                   ← The axiom tower (Part 1)
│   ├── Basic.lean           ← A1-A7, Peano axioms P1-P5
│   ├── Semiring.lean        ← B1-B5, eigenvalue theorem, A8 as theorem
│   ├── IntegralDomain.lean  ← C1-C3, A7 as theorem, power rule
│   ├── Rational.lean        ← D1-D2, eigenvalue 1/q
│   ├── Complete.lean        ← E1 (axiomatized)
│   └── Complex.lean         ← G1, j^4 = f₀
├── Verification/            ← ZF verification and model (Part 1)
│   ├── PeanoTest.lean       ← PA1-PA9 verification
│   ├── ZFTest.lean          ← ZF axioms from abstract Ens (F1-F5)
│   ├── Model.lean           ← Forward model: AddMonoidAlgebra R R
│   └── Countermodels.lean   ← F1/F2/F3 separation results
└── Obstruction/             ← Encoding obstruction (Part 2)
    ├── Encoding.lean        ← Term algebra, obsRewrite, trajectory divergence
    ├── Main.lean            ← no_coalgebra_morphism, encoding trilemma
    ├── Oplus.lean           ← Bitwise oplus impossibility
    ├── Pairing.lean         ← Pairing unboundedness
    └── Convergence.lean     ← WeakConvergence vs TotalDivergence (open)
```

Build: `lake build` (requires Lean 4 v4.28.0 + Mathlib v4.28.0)

## Open Questions

| Question | Description |
|---|---|
| **Syntax-semantics bisimulation** | Is the Godel encoding a coalgebra morphism between the syntactic coalgebra (term rewriting) and the semantic coalgebra (eigenvalue observation)? The encoding obstruction says no for injective encodings — but what about weaker notions? |
| **Analytic model** | Connecting the abstract algebra to State = smooth functions, compose = multiplication, obs = d/dx — verifying all axioms against actual eigenfunctions of differentiation. |

## Connections

| Field | What it contributes | What's new here |
|---|---|---|
| **Differential algebra** (Ritt, Kolchin) | Commutative rings with derivations, Leibniz rule | Interpreting eigenvalue structure as arithmetic |
| **Universal coalgebra** (Rutten, Jacobs) | Bisimulation, coinduction, final coalgebras | Combining coalgebraic primitives with derivation structure |
| **Bialgebraic semantics** (Turi, Plotkin) | Algebra (syntax) + coalgebra (semantics) unified | Asking whether Godel encoding is a coalgebra morphism |
| **Recursion theory** (Kleene) | Self-referencing programs, fixed points | The encoding trilemma as a structural characterization of incompleteness |

## Theory Documents

| File | Contents |
|---|---|
| [spectral-arithmetic-complete](docs/theory/spectral-arithmetic-complete.md) | Complete unified theory (Parts 1-9) |
| [axioms](docs/theory/axioms.md) | Formal axiom set (A1-A8) |
| [pa-equiconsistency](docs/theory/pa-equiconsistency.md) | PA equiconsistency proof with countermodels |
| [zf-test-suite](docs/theory/zf-test-suite.md) | ZF axioms verified against framework |
| [zf-equiconsistency](docs/theory/zf-equiconsistency.md) | ZF equiconsistency proof |
| [layers](docs/theory/layers.md) | The seven levels of spectral arithmetic |

### Background

| File | Contents |
|---|---|
| [eulers-number-and-differentials](docs/theory/eulers-number-and-differentials.md) | Eigenfunctions of d/dx, discrete-continuous bridge |
| [spectral-arithmetic](docs/theory/spectral-arithmetic.md) | Original construction: numbers as eigenfunctions |

## Reading Order

**For the core result:** Core/Semiring.lean (eigenvalue theorem) -> Verification/PeanoTest.lean (PA verification) -> [pa-equiconsistency](docs/theory/pa-equiconsistency.md) (why these axioms)

**For the encoding obstruction:** [Obstruction repo](https://github.com/suisuss/Obstruction) (the general trilemma) -> Obstruction/Main.lean (applied to this framework)

**For everything:** [spectral-arithmetic-complete](docs/theory/spectral-arithmetic-complete.md)
