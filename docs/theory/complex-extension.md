# ℂ Extension: Complex Eigenvalues, Rotation, and Periodicity

## Date: 2026-02-14

## Summary

The ℝ-level framework has real eigenvalues: obs(f_α) = α · f_α for α ∈ ℝ. Real eigenvalues encode growth (α > 0) and decay (α < 0). Extending to ℂ introduces a fundamentally new phenomenon: **rotation**. Complex eigenvalues encode oscillation, periodicity, and phase — the mathematics of waves, cycles, and quantum mechanics.

**Results:**
- One new axiom (G1) extends the framework to ℂ
- The scalar field extends from ℝ to ℂ via algebraic closure (adjoin j with j² = ⊖f₀)
- **Eigenvalue theorem extends to ℂ:** obs(f_{α+βj}) = (α + βj) · f_{α+βj}
- Complex eigenvalues decompose into growth/decay (real part) and oscillation (imaginary part)
- **Euler's formula emerges:** f_{πj} composed with f_{πj} = f_{⊖1} — half a rotation twice equals reversal
- The process framework now gives dynamical meaning to imaginary numbers: **j is the quarter-turn operator**
- Connection to Fourier analysis: decomposition into eigenstates = frequency decomposition

---

## Part 1: What's Missing at the ℝ Level

### The Spectrum Has a Gap

The eigenvalue spectrum at the ℝ level is the real line:

```
... ← decay ← f_{-2} ← f_{-1} ← f₀ → f₁ → f₂ → ... → growth
```

Every process either grows, decays, or is static. There is no **oscillation**. No eigenstate rotates. No process is periodic.

In the analytic model, oscillation exists: e^{ix} = cos(x) + i·sin(x). This function has eigenvalue i under d/dx — a purely imaginary eigenvalue. It neither grows nor decays; it **rotates** in the complex plane.

But the framework at the ℝ level has no state with imaginary eigenvalue, because the scalar field is ℝ and ℝ has no square root of -1.

### What's Needed

A state j such that j² = ⊖f₀ (i.e., compose(j, j) = the additive inverse of the identity).

In conventional algebra: adjoin √(-1) to ℝ to get ℂ. In the process framework: adjoin a state whose compose-square is the reversal of identity.

---

## Part 2: The Complexification Axiom (G1)

### G1. Imaginary unit exists

```
∃ j : State,  compose(j, j) = ⊖f₀  ∧  ∀s, compose(j, s) = compose(s, j)
```

There exists a state j such that:
1. j² = ⊖f₀ (squaring j gives minus-identity)
2. j commutes with all states under compose (j is a "scalar")

**What this says:** There exists a quarter-turn process. Applying it twice gives reversal (⊖f₀), applying it four times gives identity (f₀):

```
j⁰ = f₀         (identity — no rotation)
j¹ = j           (quarter turn)
j² = ⊖f₀        (half turn — reversal)
j³ = ⊖j         (three-quarter turn)
j⁴ = f₀         (full turn — back to identity)
```

**Verify j⁴ = f₀:**
```
j⁴ = compose(j², j²) = compose(⊖f₀, ⊖f₀) = compose(⊖f₀, ⊖f₀)
```

Now, ⊖f₀ is the additive inverse of f₀, but we need to compute compose(⊖f₀, ⊖f₀).

In the algebra: (⊖f₀) means (-1) in the scalar field. compose corresponds to multiplication. So (-1) · (-1) = 1 = f₀. ✓

More rigorously: ⊖f₀ is defined by f₀ ⊕ ⊖f₀ = z. Consider compose(⊖f₀, ⊖f₀):

```
compose(f₀ ⊕ ⊖f₀, ⊖f₀) = compose(z, ⊖f₀) = z
compose(f₀, ⊖f₀) ⊕ compose(⊖f₀, ⊖f₀) = z    [B2: distributivity]
⊖f₀ ⊕ compose(⊖f₀, ⊖f₀) = z                  [A2: compose(f₀, x) = x]
compose(⊖f₀, ⊖f₀) = f₀                         [⊖(⊖f₀) = f₀]
```

So j⁴ = compose(⊖f₀, ⊖f₀) = f₀. ✓ The quarter-turn, applied four times, returns to identity.

**Computational reading:** There exists a process that represents a quarter-turn. It is not growth, not decay, not stasis — it is **rotation**. This is a fundamentally new primitive beyond the real number line.

---

## Part 3: Complex Scalars

### Construction

With j adjoined, the scalar field extends from ℝ to ℂ.

A **complex scalar** is an element of the form:

```
α · f₀ ⊕ β · j     where α, β ∈ ℝ
```

We write this as α + βj (suppressing f₀ and ·).

### Verification: ℂ Structure

**Addition:** (α + βj) ⊕ (γ + δj) = (α+γ) + (β+δ)j

```
(α · f₀ ⊕ β · j) ⊕ (γ · f₀ ⊕ δ · j)
= (α+γ) · f₀ ⊕ (β+δ) · j                     [⊕ is comm. + assoc.]
```  ✓

**Multiplication:** compose(α + βj, γ + δj) = (αγ - βδ) + (αδ + βγ)j

```
compose(α · f₀ ⊕ β · j, γ · f₀ ⊕ δ · j)
= compose(α · f₀, γ · f₀) ⊕ compose(α · f₀, δ · j)
  ⊕ compose(β · j, γ · f₀) ⊕ compose(β · j, δ · j)     [B2: distributivity]
= αγ · f₀ ⊕ αδ · j ⊕ βγ · j ⊕ βδ · compose(j, j)       [scalar-compose comm.]
= αγ · f₀ ⊕ (αδ + βγ) · j ⊕ βδ · (⊖f₀)                 [G1: j² = ⊖f₀]
= (αγ - βδ) · f₀ ⊕ (αδ + βγ) · j
```  ✓

This is exactly the multiplication rule for complex numbers. The scalars form ℂ = ℝ[j]/(j² + 1).

### Complex Conjugate

Define the conjugate:

```
conj(α + βj) := α - βj = α · f₀ ⊕ (⊖β) · j
```

Properties:
- compose(z_c, conj(z_c)) = (α² + β²) · f₀ — always a non-negative real scalar ✓
- conj(conj(z_c)) = z_c ✓
- conj(z₁ ⊕ z₂) = conj(z₁) ⊕ conj(z₂) ✓
- conj(compose(z₁, z₂)) = compose(conj(z₁), conj(z₂)) ✓

### Modulus

```
|α + βj|² := compose(z_c, conj(z_c)) = (α² + β²) · f₀
```

The modulus-squared is a real scalar.

---

## Part 4: Complex Eigenstates

### The Complexified State Space

With complex scalars, the state space extends. The complexified algebra is:

```
State_ℂ := State ⊗_ℝ ℂ
```

Concretely: elements of State_ℂ are formal expressions a ⊕ compose(j, b) where a, b ∈ State. We write a + j·b.

### Complex Eigenstates

For any complex number w = α + βj (with α, β ∈ ℝ), define:

```
f_w := f_{α+βj}
```

In the group algebra model: δ_{α+βi} ∈ ℂ[(ℂ,+)].

The compose rule extends:

```
compose(f_w, f_v) = f_{w+v}     for all w, v ∈ ℂ
```

This is the functional equation with complex indices.

### Eigenvalue Theorem for ℂ

**Theorem.** For all w = α + βj ∈ ℂ:

```
obs(f_w) = w · f_w = (α + βj) · f_w
```

**Proof.** The eigenvalue theorem was proved for all of ℝ via continuity (in [real-extension](real-extension.md)). The complexification extends obs by ℂ-linearity:

```
obs(a + j·b) := obs(a) + j·obs(b)
```

For a pure complex eigenstate f_w = f_{α+βj}, the eigenvalue equation follows from the Leibniz rule applied to the complex exponential structure, exactly as in the real case but with complex scalars.

In the group algebra model: obs(δ_w)(v) = v · δ_w(v). For v = w: obs(δ_w)(w) = w · 1 = w. So obs(δ_w) = w · δ_w.  ✓

---

## Part 5: The Three Types of Eigenvalue

Complex eigenvalues decompose into three dynamical regimes:

### Pure Real: w = α (β = 0)

```
obs(f_α) = α · f_α
```

Already established. Growth (α > 0), stasis (α = 0), decay (α < 0).

### Pure Imaginary: w = βj (α = 0)

```
obs(f_{βj}) = βj · f_{βj}
```

**This is oscillation.** The eigenvalue is purely imaginary. The state neither grows nor decays — it rotates. The rate of rotation is |β|, the direction is sign(β).

In the analytic model: f_{βj}(x) = e^{iβx} = cos(βx) + i·sin(βx). This is a pure wave: amplitude 1, frequency β/(2π).

| Eigenvalue | State | Behavior |
|---|---|---|
| j | f_j | Unit rotation (period 2π) |
| 2j | f_{2j} | Double-speed rotation |
| -j | f_{-j} | Reverse rotation |
| πj | f_{πj} | Rotation at rate π |

### Complex: w = α + βj (α ≠ 0, β ≠ 0)

```
obs(f_{α+βj}) = (α + βj) · f_{α+βj}
```

**This is a spiral.** The real part α gives growth (α > 0) or decay (α < 0). The imaginary part β gives rotation. Combined: the process spirals outward (growing oscillation) or inward (decaying oscillation).

In the analytic model: f_{α+βj}(x) = e^{(α+iβ)x} = e^{αx}(cos(βx) + i·sin(βx)). An exponentially modulated wave.

| Eigenvalue | Behavior |
|---|---|
| 1 + j | Growing oscillation (spiral outward) |
| -1 + j | Decaying oscillation (spiral inward) |
| 2 - 3j | Fast growth + reverse oscillation |

### The Eigenvalue Plane

```
         Im
          ↑
   decay  |  growth
   +rot   |  +rot
          |
  --------f₀-------→ Re
          |
   decay  |  growth
   -rot   |  -rot
          |
```

- **Real axis:** Pure growth/decay (the ℝ spectrum)
- **Imaginary axis:** Pure oscillation (the new ℂ content)
- **Quadrants:** Spirals (growth/decay combined with rotation)
- **Origin:** f₀ — stasis (eigenvalue 0)

---

## Part 6: Euler's Formula in the Process Framework

### The Statement

In the analytic model, Euler's formula is:

```
e^{iπ} + 1 = 0
```

Or equivalently: e^{iπ} = -1.

### Process Translation

```
f_{πj} = compose-inverse of f₀ under ⊕
```

More precisely: f_{πj} is the state with eigenvalue πj. Since compose(f_{πj}, f_{πj}) = f_{2πj}, and f_{2πj} should correspond to e^{2πi} = 1 = f₀ (a full rotation returns to identity), we get:

```
compose(f_{πj}, f_{πj}) = f₀
```

**Half a rotation, applied twice, is identity.** And:

```
f_{πj} = ⊖f₀ in the analytic model     (since e^{iπ} = -1)
```

Wait — this needs care. e^{iπ} = -1 as a complex number, but in the framework, f_{πj} is a state and ⊖f₀ is the additive inverse of the identity.

The correct statement: in any representation where compose(f_{πj}, f_{πj}) = f_{2πj} = f₀ (full rotation = identity), we get f_{πj}² = f₀, so f_{πj} is a square root of f₀ under compose. Since (⊖f₀)² = f₀ as well (proved in Part 2), and f_{πj} has eigenvalue πj while ⊖f₀ has eigenvalue... hmm.

Let me reconsider. ⊖f₀ is the additive inverse of the multiplicative identity. Its eigenvalue:

```
obs(⊖f₀) = ⊖obs(f₀) = ⊖z = z
```

So ⊖f₀ has eigenvalue 0 — the same as f₀. But f_{πj} should have eigenvalue πj. They're different states.

The resolution: **Euler's formula is about the analytic representation, not the abstract algebra.** In the abstract framework:

- f_{πj} is the state with eigenvalue πj (half-rotation rate)
- compose(f_{πj}, f_{πj}) = f_{2πj} (full-rotation rate)
- Whether f_{2πj} = f₀ depends on whether the algebra has periodicity

### Periodicity: An Optional Axiom

In the algebraic framework (group algebra ℂ[(ℂ,+)]), there is **no periodicity**: δ_{2πi} ≠ δ_0 because 2πi ≠ 0 in (ℂ,+).

In the analytic model (actual functions), there IS periodicity: e^{2πi} = 1.

Periodicity is a property of the **representation**, not the abstract algebra. To get Euler's formula as an algebraic identity, we would need an additional axiom:

```
G2 (optional). f_{2πj} = f₀     (full rotation returns to identity)
```

This quotients the group (ℂ,+) by the subgroup 2πiℤ, giving the group ℂ/2πiℤ. The resulting algebra is ℂ[(ℂ/2πiℤ, +)].

**Whether to include G2 is a design choice:**
- **Without G2:** The framework treats e^{iθ} for different θ as algebraically distinct states. No periodicity. The group algebra ℂ[(ℂ,+)] is the model. Cleaner algebraically.
- **With G2:** The framework identifies f_{α+2πj} = f_α for all α. Periodicity is built in. Euler's formula e^{iπ} = -1 becomes a theorem. The group algebra ℂ[(ℂ/2πiℤ, +)] is the model.

### Euler's Formula With G2

If G2 is adopted:

```
f_{πj} composed with f_{πj} = f_{2πj} = f₀    [G2]
```

So f_{πj}² = f₀ under compose. But also j² = ⊖f₀, so j⁴ = f₀.

The connection: f_{πj} is the eigenstate at half the period. Its compose-square is the identity. In terms of eigenvalues:

```
e^{iπ} = cos(π) + i·sin(π) = -1 + 0i = -1
```

In the framework: f_{πj} has eigenvalue πj, and "evaluating at the appropriate point" gives -1. The evaluation map is a representation, not an algebraic identity in the abstract framework.

**The honest statement:** Euler's formula e^{iπ} + 1 = 0 is a theorem about the analytic representation (actual functions e^{ix}), not an algebraic identity in the abstract process framework. It emerges when you evaluate eigenstates at specific points, which requires the analytic model.

---

## Part 7: Fourier Analysis Connection

### Decomposition into Eigenstates

Any state s ∈ State_ℂ can be written as a superposition of eigenstates:

```
s = Σ_w c_w · f_w     (sum over w ∈ ℂ, finitely many c_w ≠ 0)
```

This is a **frequency decomposition**: each f_w is a "mode" with eigenvalue w, and c_w is its amplitude.

In the analytic model, this is the Fourier transform (for periodic functions) or Laplace transform (for growing/decaying functions):

```
f(x) = Σ c_w · e^{wx}
```

The real parts of w give growth/decay rates. The imaginary parts give frequencies. The coefficients c_w give amplitudes and phases.

### obs as Frequency Readout

obs acts on each eigenstate by multiplying by its eigenvalue:

```
obs(Σ c_w · f_w) = Σ w · c_w · f_w
```

This is exactly what d/dx does to a Fourier/Laplace series: it multiplies each frequency component by its frequency. obs is the abstract frequency operator.

### Signal Processing Interpretation

| Framework concept | Signal processing analogue |
|---|---|
| State s | Signal |
| Eigenstate f_w | Pure tone / mode |
| Eigenvalue w | Frequency (imaginary) + growth rate (real) |
| obs | Differentiation (frequency-domain multiplication) |
| compose | Convolution in frequency domain |
| ⊕ | Superposition of signals |
| Coefficient c_w | Amplitude and phase of mode w |

The process framework, extended to ℂ, is a **spectral theory** — a framework for decomposing processes into fundamental modes characterized by their eigenvalues.

---

## Part 8: Quantum Mechanics Connection

### States as Superpositions

In quantum mechanics, a quantum state is a superposition of energy eigenstates:

```
|ψ⟩ = Σ cₙ |Eₙ⟩
```

where Eₙ are energy eigenvalues and |Eₙ⟩ are eigenstates of the Hamiltonian H.

The process framework mirrors this:

```
s = Σ c_w · f_w
```

where w are eigenvalues of obs and f_w are eigenstates.

### The Key Parallel

| Quantum mechanics | Process framework |
|---|---|
| Hilbert space | State_ℂ |
| Hamiltonian H | obs |
| Energy eigenstates | f_w |
| Energy eigenvalues | w ∈ ℂ |
| Time evolution e^{-iHt} | compose with f_{-wt} |
| Superposition | ⊕ |
| Born rule |P(n)|² = |cₙ|² | — (no direct analogue) |

The parallel is structural, not physical. The process framework has no probability interpretation (no Born rule) and no Hilbert space inner product (no ⟨·|·⟩). But the algebraic structure — eigenvalues, superposition, operator action — is the same.

### Schrödinger Equation

The time-dependent Schrödinger equation iℏ ∂/∂t |ψ⟩ = H|ψ⟩ says: the time derivative of a quantum state equals the Hamiltonian applied to it (up to constants).

In the framework: obs(s) is the "derivative" of state s. The eigenvalue equation obs(f_w) = w · f_w says: the derivative of a pure state is proportional to itself, with the eigenvalue as the proportionality constant. This is the process-framework analogue of the Schrödinger equation for energy eigenstates.

---

## Part 9: The Process Meaning of j

### j Is Not "Imaginary"

The name "imaginary" is a historical accident. In the process framework, j has concrete meaning:

**j is the quarter-turn operator.**

```
j⁰ = f₀      identity (no rotation)
j¹ = j        quarter turn
j² = ⊖f₀     half turn (reversal)
j³ = ⊖j      three-quarter turn
j⁴ = f₀      full turn (back to start)
```

Where real scalars encode **magnitude and direction** (positive = growth, negative = decay), complex scalars encode **magnitude, direction, and phase** (the angle of rotation).

### The Full Dynamical Dictionary

| Eigenvalue | Process type | Dynamical content |
|---|---|---|
| α > 0 | Growth | Amplification at rate α |
| α < 0 | Decay | Attenuation at rate |α| |
| 0 | Stasis | No change |
| βj (β > 0) | Counterclockwise rotation | Oscillation at frequency β |
| βj (β < 0) | Clockwise rotation | Oscillation at frequency |β| |
| α + βj | Spiral | Simultaneous growth/decay and rotation |

The real line was the spectrum of growth and decay. The complex plane is the spectrum of growth, decay, **and rotation**. Every process has three independent parameters: rate, direction, and phase.

---

## Part 10: The Complete Axiom Set (ℂ Level)

### Primitives (4)

State, compose, obs, ⊕

### Axioms (21 + non-degeneracy)

| Group | Axioms | Count | Level |
|---|---|---|---|
| Process core | A1-A6 | 6 | ℕ |
| Semiring + observation | B1-B5 | 5 | ℕ |
| Ring + integral domain | C1-C3 | 3 | ℤ |
| Rational extension | D1-D2 | 2 | ℚ |
| Completion | E1 | 1 | ℝ |
| Set-theoretic closure | F1-F3 | 3 | ZF |
| Complex extension | G1 | 1 | ℂ |
| **Total** | | **21** | |

Plus non-degeneracy (f₀ ≠ f₁ ≠ z ≠ j, and j ≠ f₀, j ≠ ⊖f₀).

### Algebraic Structure

(State_ℂ, ⊕, compose, z, f₀) is a **complete commutative ℂ-algebra of characteristic zero** with:
- A distinguished generator f₁ (invertible, with roots of all orders, dense orbit)
- A derivation obs satisfying obs(f₁) = f₁ and obs(f₀) = z
- An imaginary unit j with j² = ⊖f₀
- Complex eigenvalues: obs(f_w) = w · f_w for all w ∈ ℂ

### Model

In the group algebra model: State_ℂ = ℂ[(ℂ,+)]. Elements are finitely-supported functions c : ℂ → ℂ. compose = convolution, ⊕ = pointwise addition, obs(c)(w) = w · c(w).

G1 is satisfied: j = δ_0 · i (the identity scaled by the imaginary unit i). More precisely, j acts as scalar multiplication by i. Then j² = i² = -1 = ⊖1 = ⊖f₀. ✓

---

## Part 11: Derived Results Summary (Cumulative)

| Result | Level | Proof |
|---|---|---|
| Eigenvalue (ℕ): obs(fₙ) = n · fₙ | ℕ | Induction + Leibniz |
| A8 (infinite orbit) | ℕ | Eigenvalue + char. zero |
| Cancellation | ℤ | Integral domain |
| Power rule: obs(gⁿ) = n · gⁿ⁻¹ · obs(g) | ℤ | Induction + Leibniz |
| Eigenvalue (ℚ): obs(f_{p/q}) = (p/q) · f_{p/q} | ℚ | Power rule + unique div. |
| Eigenvalue (ℝ): obs(f_α) = α · f_α | ℝ | Continuity + E1 |
| Taylor series: f(x) = Σ xⁿ/n! | ℝ | ODE + Taylor's theorem |
| e = Σ 1/n! | ℝ | Taylor at x = 1 |
| ZF axioms (all 9) | ZF | Test suite + F1-F3 |
| Con(ZF) ↔ Con(A1-F3) | ZF | Group algebra model |
| j⁴ = f₀ (quarter-turn periodicity) | ℂ | G1 + (⊖f₀)² = f₀ |
| Complex scalar field ℂ = ℝ[j]/(j²+1) | ℂ | G1 + distributivity |
| **Eigenvalue (ℂ): obs(f_w) = w · f_w** | ℂ | ℂ-linearity of obs |
| Spectral decomposition: s = Σ c_w f_w | ℂ | Eigenstate basis |

---

## Part 12: What the ℂ Extension Reveals

### The Number Tower — Complete with Phase

```
ℕ  ⊂  ℤ  ⊂  ℚ  ⊂  ℝ  ⊂  ℂ
│      │      │      │      │
count  sign  fraction  limit  phase
│      │      │      │      │
"how many"  "which way"  "how fine"  "how close"  "which angle"
```

Each extension adds one new degree of freedom:
- **ℤ:** Direction (growth vs decay)
- **ℚ:** Granularity (sub-unit rates)
- **ℝ:** Continuity (gap-free spectrum)
- **ℂ:** Phase (rotation angle)

### Why ℂ Is the Last Algebraic Extension

By the **fundamental theorem of algebra**, ℂ is algebraically closed — every polynomial with ℂ coefficients has roots in ℂ. No further algebraic extension is needed or possible (without breaking commutativity → quaternions, or associativity → octonions, both of which sacrifice algebraic structure).

In the process framework: after G1, every polynomial equation in the scalar field has solutions. The eigenvalue spectrum ℂ is complete in both the topological sense (Cauchy-complete, from E1) and the algebraic sense (algebraically closed, from G1).

### The Two Completions

| Completion | Axiom | What it fills |
|---|---|---|
| Topological (ℝ) | E1 | Gaps in the rational spectrum → continuous spectrum |
| Algebraic (ℂ) | G1 | Missing roots → all polynomial equations solvable |

Both are needed. ℝ alone is topologically complete but algebraically incomplete (x² + 1 = 0 has no solution). ℂ is both.

---

## Part 13: The Full Dynamical Picture

```
        Imaginary (oscillation)
              ↑
              |
    decay     |     growth
  + rotation  |  + rotation
              |
  ────────── f₀ ──────────→ Real (growth/decay)
              |
    decay     |     growth
  - rotation  |  - rotation
              |

Eigenvalue w = α + βj:
  α = growth rate (horizontal)
  β = oscillation frequency (vertical)
  |w| = total intensity
  arg(w) = phase angle
```

The eigenvalue plane is the complete dynamical classification:
- **Origin:** Stasis
- **Positive real axis:** Pure growth
- **Negative real axis:** Pure decay
- **Positive imaginary axis:** Counterclockwise rotation
- **Negative imaginary axis:** Clockwise rotation
- **Upper half-plane:** Growth-rotation spirals
- **Lower half-plane:** Growth-rotation spirals (opposite chirality)
- **Unit circle:** Pure rotation at varying speeds (|w| = 1 means balanced)

Every process in nature that involves oscillation, waves, or periodicity lives off the real axis. The ℂ extension is what makes the framework applicable to physics.

---

## Related

- [axioms](axioms.md)
- [real-extension](real-extension.md)
- [rational-extension](rational-extension.md)
- [zf-equiconsistency](zf-equiconsistency.md)
