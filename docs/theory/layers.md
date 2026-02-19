# The Seven Layers of Spectral Arithmetic

Spectral Arithmetic builds numbers from scratch. It starts with four undefined
operations and, through seven layers of axioms, arrives at a structure where
every complex number appears as an eigenvalue of an abstract observation
operator. Each layer extends the previous one, and axioms assumed at lower
layers sometimes become theorems at higher ones.

---

## Primitives

Everything is built from four undefined terms and three distinguished states.

### The Four Operations

| Primitive | Type | Meaning |
|-----------|------|---------|
| `State` | Type | An uninterpreted type — the raw material |
| `compose` | State → State → State | Combining processes (abstract multiplication) |
| `obs` | State → State | The observation operator (abstract d/dx) |
| `oplus` | State → State → State | Additive combination (introduced at Level B) |

### The Three Distinguished States

| State | Name | Role |
|-------|------|------|
| `f₀` | Identity | The "one" — `compose(f₀, s) = s` |
| `f₁` | Generator | The self-reproducing process — `obs(f₁) = f₁` |
| `z` | Annihilator | The "zero" — `compose(z, s) = z` |

---

## Level A — Monoid (`SpectralMonoid`)

**What it provides:** The natural numbers as an orbit.

**Axioms:**
- A1: `obs(f₁) = f₁` — the generator reproduces under observation
- A2: `compose(f₀, s) = s` — identity law
- A5a/b: `compose` is associative and commutative
- A6: `compose(z, s) = z` — annihilation
- A7: `compose(f₁, a) = compose(f₁, b) → a = b` — cancellation
- A8: `iterS n ≠ f₀` for `n ≥ 1` — the orbit is infinite

**Key definitions:**
- Successor: `S(s) = compose(f₁, s)`
- Natural numbers: the orbit `f₀, S(f₀), S(S(f₀)), ...`

**Key results:** All five Peano axioms are derived as theorems.

**Eigenvalue spectrum:** `{0, 1, 2, 3, ...}` (infinite by assumption)

---

## Level B — Semiring (`DynSemiring`)

**What it provides:** Addition, the eigenvalue theorem, and a proof that
the orbit is infinite.

**New primitive:** `oplus` (additive combination, with identity `z`).

**New axioms:**
- B1: `oplus` is an associative, commutative monoid with identity `z`
- B2: `compose` distributes over `oplus`
- B3: `obs(f₀) = z` — "the derivative of 1 is 0"
- B4: `obs(compose(a, b)) = oplus(compose(obs(a), b), compose(a, obs(b)))` — **Leibniz rule** (product rule)
- B5: `n · f₀ ≠ z` for `n ≥ 1` — **characteristic zero**

**Key result — the eigenvalue theorem:**

> `obs(iterS n) = n · iterS n`

The observation operator reads off which number a state represents. Numbers
appear as eigenvalues of `obs`, just as `n` is the eigenvalue of `d/dx`
acting on `e^(nx)`.

**Axiom eliminated:** A8 (infinite orbit) is now a **theorem**. Proof: if
`iterS n = f₀`, the eigenvalue theorem gives `obs(f₀) = n · f₀`, so
`z = n · f₀`, contradicting characteristic zero.

**Eigenvalue spectrum:** `{0, 1, 2, 3, ...}` (proved infinite)

---

## Level C — Integral Domain (`DynIntDomain`)

**What it provides:** Negative numbers, additive inverses, and the power rule.

**New axioms:**
- C1: `f₁` has a compose-inverse `f₁⁻¹` with `compose(f₁, f₁⁻¹) = f₀`
- C2: Every state has an additive inverse: `oplus(s, oneg(s)) = z`
- C3: No zero divisors: `compose(a, b) = z → a = z ∨ b = z`

**Key definitions:**
- Predecessor: `pred(s) = compose(f₁⁻¹, s)`
- Negative orbit: `iterS_neg n = pred^n(f₀)` — the states `f₋₁, f₋₂, ...`
- Compose-power: `cpow g n = compose(g, g, ..., g)` (n times)

**Key results:**
- `obs(f₁⁻¹) = oneg(f₁⁻¹)` — eigenvalue `-1`
- `obs(iterS_neg n) = oneg(n · iterS_neg n)` — eigenvalue `-n`
- **Power rule:** `obs(g^(n+1)) = (n+1) · g^n · obs(g)` — works for any state, not just orbit elements

**Axiom eliminated:** A7 (cancellation) is now a **theorem**. Proof: if
`compose(f₁, a) = compose(f₁, b)`, subtract and factor to get
`compose(f₁, oplus(a, oneg(b))) = z`. Since `f₁ ≠ z`, no-zero-divisors
forces `oplus(a, oneg(b)) = z`, so `a = b`.

**Eigenvalue spectrum:** `ℤ`

---

## Level D — Rational Extension (`DynRational`)

**What it provides:** Fractional eigenvalues.

**New axioms:**
- D1: q-th roots of `f₁` exist: `cpow(root(q), q) = f₁` for `q ≥ 1`
- D2: Additive division exists: `n · qdiv(n, a) = a` for `n ≥ 1`

D1 handles the multiplicative side (root-taking) and D2 handles the
additive side (dividing a state into n equal parts).

**Key results:**
- Torsion-freeness: `n · x = z → x = z` for `n ≥ 1`
- `qdiv` is unique (from torsion-freeness)
- **Eigenvalue 1/q:** `obs(root(q)) = qdiv(q, root(q))`

The proof of eigenvalue 1/q uses the power rule from Level C: apply it to
`root(q)^q = f₁`, get `obs(f₁) = f₁ = q · root(q)^(q-1) · obs(root(q))`,
cancel `root(q)^(q-1)` (nonzero by no-zero-divisors), and conclude
`root(q) = q · obs(root(q))`.

**Eigenvalue spectrum:** `ℚ`

---

## Level E — Real Extension (`DynComplete`)

**What it provides:** Real eigenvalues via Cauchy completion.

This level is fundamentally different from A–D. Those were algebraic
(finitary operations and equations). Level E is topological — it asserts
that limits exist, filling the gaps between rationals.

**New structure:**
- `ratEigen : ℚ → State` — packages the Level D construction into a coherent map
- `realEigen : ℝ → State` — extends `ratEigen` to all reals
- `rsmul : ℝ → State → State` — real scalar multiplication
- **Eigenvalue theorem for ℝ:** `obs(realEigen α) = rsmul α (realEigen α)`

**Properties preserved under extension:**
- Functional equation: `compose(f_α, f_β) = f_{α+β}`
- Injectivity: distinct reals give distinct states
- Compatibility: `realEigen` agrees with `ratEigen` on rationals

**Note:** Unlike Levels A–D where theorems are proved from axioms, Level E
axiomatizes the *consequences* of completion. Deriving them would require
building a full metric space and proving continuity of `obs`, which is a
separate project.

**Eigenvalue spectrum:** `ℝ`

---

## Level F — ZF Set Theory (`DynZF`)

**What it provides:** Verification that the framework supports ZF set theory.

This level is architectural rather than mathematical. It asks: can the
framework's state space support set theory? Sets are represented as
predicates `State → Prop` (membership is function application).

**New axioms:**
- F1: The natural orbit exists as a completed predicate (Axiom of Infinity)
- F2: Power sets of predicates exist (Power Set)
- F3: Images of sets under functions exist (Replacement)

**The honest picture:** In Lean's type theory, F1–F3 are trivially
satisfied — every proof is `Iff.rfl`. The axioms carry real content only
in a weaker (first-order) metatheory. The value of Level F is the
**dependency analysis**:

| ZF Axiom | Source |
|----------|--------|
| Extensionality | Metatheory |
| Empty Set | Metatheory |
| Pairing | Metatheory |
| Union | Metatheory + F2 |
| Power Set | F2 |
| **Infinity** | **F1 + eigenvalue theorem (A1–B5)** |
| Separation | Metatheory |
| Replacement | F3 |
| Foundation | Metatheory (type stratification) |

Only the Axiom of Infinity uses the framework's algebra. The eigenvalue
theorem from Level B is what makes the orbit provably infinite.

**Bonus:** The framework implements boolean logic algebraically on `{z, f₀}`:
AND = `compose`, NOT = `oplus(f₀, oneg(·))`, OR via De Morgan. The algebra
can express logic, not just use it.

---

## Level G — Complex Extension (`DynComplex`)

**What it provides:** Complex eigenvalues and the imaginary unit.

This level is algebraic again (like A–D), adjoining a solution to `x² + 1 = 0`.

**New axiom (G1):**
- `j : State` with `compose(j, j) = oneg(f₀)` — i.e., `j² = -1`
- `j` commutes with all states
- `j ≠ z`, `j ≠ f₀`

**New structure:**
- `csmul : ℂ → State → State` — complex scalar multiplication (extends `rsmul`)
- `complexEigen : ℂ → State` — complex eigenstates (extends `realEigen`)
- **Eigenvalue theorem for ℂ:** `obs(complexEigen w) = csmul w (complexEigen w)`

**Quarter-turn periodicity:**

| Power | Value | Angle |
|-------|-------|-------|
| j⁰ | f₀ | 0° |
| j¹ | j | 90° |
| j² | ⊖f₀ | 180° |
| j³ | ⊖j | 270° |
| j⁴ | f₀ | 360° |

**Distinctness results:**
- `j ≠ f₁`: if they were equal, `j⁴ = iterS 4 = f₀` would violate infinite orbit
- `⊖f₀ ≠ f₀`: otherwise `2 · f₀ = z`, violating characteristic zero
- `j ≠ ⊖f₀`: the quarter turn is not the half turn

**Eigenvalue spectrum:** `ℂ`

---

## Summary

| Level | Structure | Spectrum | Axioms eliminated |
|-------|-----------|----------|-------------------|
| A | Monoid | `{0,1,2,...}` | — |
| B | Semiring | `{0,1,2,...}` | A8 (infinite orbit) |
| C | Integral domain | `ℤ` | A7 (cancellation) |
| D | Rational extension | `ℚ` | — |
| E | Real extension | `ℝ` | — |
| F | ZF set theory | — | — |
| G | Complex extension | `ℂ` | — |

The theory starts with four primitives (`State`, `compose`, `obs`, `oplus`)
and three special states (`f₀`, `f₁`, `z`). Through progressive axiom
layering, it builds all of arithmetic. The central mechanism is the
**eigenvalue theorem** — `obs` reads off numerical identity as eigenvalues,
just as `d/dx` reads eigenvalues from `e^(λx)`. Numbers are not assumed.
They emerge from the algebra.
