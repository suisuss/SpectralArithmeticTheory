# The Encoding Obstruction: Intension, Extension, and the Limits of Executable Self-Representation

## Date: 2026-02-19 (revised 2026-02-21)

## Summary

The bisimulation conjecture (self-representation.md, Part 10) asks whether the Gödel encoding creates a behavioral equivalence between syntactic rewriting and semantic observation. This document argues that the obstruction is **not** an artifact of growth rates or any particular encoding, but a structural consequence of the **intension/extension duality** in any system powerful enough for self-representation.

The fundamental insight: **mathematics is substitution.** Substitution moves between two irreducible modes — the **intensional** (a form named, treated as a unit: `obs(compose(f₁, f₁))`) and the **extensional** (the same form unfolded, all parts visible: `oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁)))`). A final substitution cannot be proven, because any completed extensional form can be given a new symbol — re-intensionalized — and the process begins again. The encoding of execution cannot equal the execution of encoding, because encoding is intensional (naming) while execution is extensional (substituting), and these never reach a fixed point.

This gap has different consequences depending on what the encoding is for:

- **Passive encoding** (Gödel numbering as inert labels): the gap gives Gödel incompleteness. The system can name but not resolve self-referential propositions. This is standard and well-understood.

- **Executable encoding** (the encoding runs itself — self-executing representation): the gap forces **external state**. To actually perform the intension/extension switching, the system must manipulate positions (bits, eigenvalues). Positional manipulation requires carry propagation. Carry propagation is non-local. Non-locality requires a register external to the encoding. This is the new content.

The **trilemma** maps cleanly onto this:

| Property | What it really is |
|---|---|
| **Eigenvalue arithmetic** | Positions exist — obs reads off eigenvalues, giving ℕ |
| **Self-encoding** | The encoding is executable — not just naming, but running |
| **Coalgebra morphism** | Intension/extension switching commutes with execution |

The third fails because executable encoding requires positional manipulation, positional manipulation requires carry, and carry requires external state that breaks self-containment. The system can name itself (passive encoding works) but cannot execute its own encoding faithfully (the morphism fails at the point where addition enters through the Leibniz rule).

**Key result (proved, sorry-free in Lean):** For any injective `ε : Term → ℕ`, the Leibniz rewrite extensionalizes `obs(compose(f₁, f₁))` into a structurally different term. By injectivity, the codes differ. The eval-quote diagram does not commute. See [obstruction/README.md](obstruction/README.md) for the formalization.

---

## Part 1: The Fundamental Obstruction — Substitution Never Terminates

### Intension and extension

Every formal expression has two faces:

- **Intensional**: the expression as a named unit, opaque, treated as a single thing. `obs(compose(f₁, f₁))` — you see the name, not the internals.
- **Extensional**: the expression unfolded by substitution, all parts visible. `oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁)))` — the Leibniz rule has been applied, every sub-operation is explicit.

The `obsRewrite` operation moves from intensional to extensional: it substitutes the Leibniz rule into the expression, making the implicit structure explicit. But then you can **re-intensionalize** — give the entire unfolded form a new name, a new symbol — and the process begins again.

This is not a quirk of this framework. It is what mathematics IS. Mathematics operates by substitution. Every definition is an intensional compression of an extensional form. Every proof step is an extensional unfolding. And every completed unfolding can be re-named, because **any form can be given a symbol.**

A coalgebra morphism between syntax and semantics would require a fixed point: a point where the extensional (unfolded, syntactic) and intensional (folded, semantic) representations agree through the encoding. No such fixed point exists, because naming is always one step behind substitution.

### The distinction: passive vs. executable encoding

This matters differently depending on what the encoding does:

**Passive encoding** (standard Gödel numbering): the encoding assigns inert labels to terms. The label `⌜obs(compose(f₁, f₁))⌝` is just a number — it doesn't *do* anything. The intension/extension gap produces Gödel incompleteness: the system can name self-referential propositions but cannot resolve them. This is Gödel 1931.

**Executable encoding** (self-executing representation): the encoding is not just a label — it is meant to be *run*. The system operates on its own codes using its own operations. Now the intension/extension switching must actually be *performed*, not just described. Performing it requires manipulating positional representations (eigenvalues, bits), which requires addition (carry propagation), which requires external state (a register). The morphism fails not just abstractly (naming can't catch substitution) but concretely (the execution machinery introduces state that breaks self-containment).

The encoding obstruction is about the second case: why no self-executing encoding can faithfully represent its own execution.

### The technical framing

The bisimulation conjecture defines two coalgebra structures on the same carrier:

- **Semantic coalgebra** (State, obs_semantic): eigenvalue scaling, obs(f_n) = n · f_n
- **Syntactic coalgebra** (State, obs_code): parse a Gödel number, apply obs as a rewrite rule, re-encode the result

The eval-quote diagram asks whether these produce bisimilar behavior:

```
        eval
Terms --------→ State
  |                |
  | ⌜·⌝            | obs_semantic
  |                |
  ↓                ↓
State --------→ State
     obs_code
```

The first-pass analysis identifies a mismatch between prime factorization and eigenvalue arithmetic:

- **Eigenvalue arithmetic is additive:** compose(f_m, f_n) = f_{m+n}, obs(f_n) = n · f_n
- **Prime factorization is multiplicative:** ⌜compose(a, b)⌝ = 2^1 · 3^17 · 5^{⌜a⌝} · 7^19 · 11^{⌜b⌝} · 13^18

These operate in completely different arithmetic regimes. The natural question is: **is this an accident of Gödel's particular encoding choice, or is it fundamental?**

### Why the standard framing is insufficient

Stopping at "prime factorization doesn't match eigenvalue addition" leaves open two escape routes:

1. **A different encoding might work.** Perhaps Cantor pairing, binary interleaving, or some other injection aligns with eigenvalue structure.
2. **A different observation operator might work.** Perhaps replacing the Leibniz rule with a rule that produces non-linear eigenvalues could match the encoding's growth rate.

Both escape routes fail, but for different and instructive reasons. Their failure reveals a trilemma that is the actual obstruction.

---

## Part 2: Why No Encoding Works (Closing Escape Route 1)

### The pairing requirement

Any injective encoding of structured terms into ℕ must solve the **pairing problem**: given a term with multiple components (e.g., `compose(a, b)` with sub-terms `a` and `b`), the encoding must map the pair (⌜a⌝, ⌜b⌝) to a single number ⌜compose(a, b)⌝ in a way that is:

1. **Injective:** Different pairs give different codes
2. **Decodable:** Given the code, recover both components

This is the requirement for a **pairing function** — an injection ℕ × ℕ → ℕ with computable projections.

### No pairing function is additive

**Claim:** No injective, decodable function π: ℕ × ℕ → ℕ satisfies π(m, n) = m + n.

**Proof:** Addition is not injective on pairs. π(3, 5) = π(4, 4) = 8. Given 8, you cannot recover the pair. ∎

This is trivial but the consequences are not. It means:

> Any encoding of a binary operation's arguments into ℕ must use **non-additive** structure — at minimum quadratic (Cantor pairing), typically exponential (prime factorization).

### The available pairing functions

| Encoding | Formula | Growth | Structure |
|---|---|---|---|
| Prime factorization | π(m, n) = 2^m · 3^n | Exponential | Multiplicative |
| Cantor pairing | π(m, n) = (m+n)(m+n+1)/2 + n | Quadratic | Polynomial |
| Binary interleaving | Interleave binary digits of m and n | Linear in max(m,n) | Bitwise |
| Rosenberg-Strong | max(m,n)² + max(m,n) + m − n | Quadratic | Polynomial |

Every one of these is super-linear in at least one argument. The eigenvalue coalgebra's observation obs(f_k) = k · f_k is linear in the index k. The mismatch is unavoidable regardless of encoding choice.

### The trajectory divergence argument

Consider a term t and its observation trajectory under both coalgebras.

**Semantic trajectory:**
```
f_{ε(t)},  ε(t) · f_{ε(t)},  ε(t)² · f_{ε(t)},  ...
```
Each step multiplies by ε(t). The eigenvalue at step k is ε(t)^k — geometric in k.

**Syntactic trajectory:**
```
ε(t),  ε(obs(t)),  ε(obs²(t)),  ...
```
Each step applies the rewriting system to reduce the term, then re-encodes. The Leibniz rule (R7) transforms obs of a compound term into a **sum** of terms. Encoding a sum requires pairing both summands, invoking the super-linear pairing function.

At each step:
- Semantic obs multiplies the eigenvalue by a scalar (linear operation on the index)
- Syntactic obs decomposes, rewrites, and re-encodes (involving pairing, which is super-linear)

After k steps, the growth rates are governed by fundamentally different arithmetic. These sequences cannot be bisimilar because bisimulation requires trajectory agreement at all observation depths.

**Conclusion:** The obstruction holds for **all** injective encodings, not just prime factorization. Escape route 1 is closed.

---

## Part 3: Why No Observation Operator Works (Closing Escape Route 2)

### The question

If the problem is "linear obs vs. super-linear encoding," the natural response is: make obs non-linear too. Can the observation operator read off an index whose growth rate matches the encoding?

### Why eigenvalues are linear

The eigenvalue theorem gives obs(f_n) = n · f_n. The linearity of n (not n², not 2^n) comes from the **Leibniz rule**:

```
obs(compose(a, b)) = compose(obs(a), b) ⊕ compose(a, obs(b))
```

This is the product rule for differentiation. It forces eigenvalues to be **additive** under composition. If compose(f_m, f_n) = f_{m+n}, then the eigenvalue of the composite is the sum of the eigenvalues. By induction: obs(f_n) = n · f_n. Linear.

The Leibniz rule is what makes obs a **derivation**. Derivations on commutative semirings have linear eigenvalue growth. This is a theorem about the algebraic structure, not a design choice.

### What happens with a multiplicative observation operator

Replace the Leibniz rule with a **homomorphism rule**:

```
obs(compose(a, b)) = compose(obs(a), obs(b))
```

Now obs is a ring endomorphism instead of a derivation. Eigenvalues become **multiplicative**: if obs(f_1) = λ · f_1, then obs(f_n) = λ^n · f_n.

With λ = 2, eigenvalues are {1, 2, 4, 8, 16, ...} — exponential growth, matching prime factorization's growth rate. The growth rates align.

**But the eigenvalues don't form ℕ.** The set {2^n : n ∈ ℕ} is not closed under addition: 2 + 4 = 6, and 6 is not a power of 2. Without closure under addition, you don't have a semiring. Without a semiring, you don't have PA. Without PA, you don't have arithmetic.

### What happens with a quadratic observation operator

Suppose some algebraic rule gives obs(f_n) = n² · f_n. The eigenvalues would be {0, 1, 4, 9, 25, ...} — perfect squares, matching Cantor pairing's quadratic growth.

Again, **not closed under addition**: 1 + 4 = 5, and 5 is not a perfect square. No semiring. No PA.

### What happens with any non-linear observation operator

For eigenvalues to form ℕ (with its semiring structure under + and ×), the eigenvalue sequence must be exactly {0, 1, 2, 3, 4, ...}. This is the only sequence that is:

1. Closed under addition (m + n ∈ ℕ for all m, n)
2. Closed under multiplication (m × n ∈ ℕ for all m, n)
3. Has additive identity (0) and multiplicative identity (1)
4. Satisfies induction

Any non-linear eigenvalue sequence (squares, exponentials, Fibonacci numbers, etc.) fails closure under addition. The natural numbers are distinguished precisely by being the unique semiring generated by {0, 1, successor}.

**The algebraic constraint:** To get arithmetic, eigenvalues must be {0, 1, 2, 3, ...}. To get {0, 1, 2, 3, ...} from an eigenvalue theorem, the observation operator must be a derivation (Leibniz rule), which forces linearity.

### The self-encoding dependency

Even if you could somehow produce arithmetic from non-linear eigenvalues, self-encoding requires the very features that linear eigenvalues provide:

1. **Gödel encoding requires prime factorization.** The fundamental theorem of arithmetic (unique factorization) is a theorem of PA. Without PA, prime factorization isn't available.

2. **Primitive recursive predicates require induction over ℕ.** The syntactic predicates (WellFormed, IsAxiom, ValidStep, Computes) are defined by primitive recursion on the eigenstate orbit. This requires ℕ with its induction principle.

3. **Quantification over codes requires ℕ.** The Computes predicate (∃ sequence of valid steps from input to output) quantifies over natural numbers encoding derivation sequences.

Without linear eigenvalues → without ℕ → without PA → without self-encoding. The system can't represent itself without the arithmetic that only linear eigenvalues provide.

**Conclusion:** Making obs non-linear to match encoding growth rates destroys the arithmetic needed for self-encoding. Escape route 2 is closed — and it's closed by a circularity.

---

## Part 4: The Trilemma

### Statement

Any system combining eigenvalue observation with self-representation faces a three-way impossibility:

| Property | What it requires | What it really is |
|---|---|---|
| **Eigenvalue arithmetic** | Linear eigenvalues (Leibniz rule / derivation) | **Positions exist** — obs reads off eigenvalues, giving ℕ with PA |
| **Self-encoding** | Injective pairing function (super-linear) | **The encoding is executable** — not just passive naming, but self-running code |
| **Coalgebra morphism** | Encoding preserves obs trajectories | **Intension/extension switching commutes with execution** — naming and unfolding are consistent through the encoding |

The obstruction, stated in terms of intension and extension: **executable self-encoding requires that the intensional view (the code) and the extensional view (the execution) agree at every step. They cannot, because execution is substitution (extensionalizing), and any extensional result can be re-intensionalized (given a new name), and the encoding of the new name has no fixed relationship to the encoding of the unfolded form.**

In the growth-rate language: eigenvalue observation is linear (intensional — reads off a single number), encoding is super-linear (extensional — must represent structure), and no map between these regimes commutes with both. But the growth-rate mismatch is the *symptom*. The intension/extension gap is the *cause*.

**You can have any two, but not all three:**

---

**Case 1: Eigenvalue arithmetic + Self-encoding, without Coalgebra morphism**

This is the framework as it stands. Linear eigenvalues (from the Leibniz rule) give ℕ, which gives PA, which gives Gödel encoding. But the encoding is super-linear while obs is linear — the growth rates don't match, so the encoding isn't a coalgebra morphism.

*Result:* The system can represent itself but can't observe itself faithfully through the encoding. The syntax-semantics gap.

---

**Case 2: Self-encoding + Coalgebra morphism, without Eigenvalue arithmetic**

Match the encoding growth rate to obs (e.g., both exponential via a homomorphism rule). The growth rates align, so the encoding could be a coalgebra morphism. But exponential eigenvalues don't give ℕ (not closed under addition), so there's no PA. Without PA:
- No prime factorization (it's a theorem of PA)
- No primitive recursive predicates (they require induction over ℕ)
- No Gödel encoding (it requires both of the above)

The self-encoding that was supposed to benefit from the matched growth rates **cannot be constructed** without the arithmetic that was sacrificed to match the growth rates.

*Result:* Circular. You need arithmetic to self-encode, but you gave up arithmetic to match growth rates.

---

**Case 3: Eigenvalue arithmetic + Coalgebra morphism, without Self-encoding**

Keep linear eigenvalues (getting ℕ and PA) and require the encoding to also be linear (to match obs). But a linear function ε(a, b) = a + b is not injective on pairs — you can't recover the components. No injective linear encoding of structured terms exists.

*Result:* Clean eigenvalue arithmetic that can't talk about itself. Observation is faithful but self-representation is impossible.

---

### The dependency structure

The trilemma has an asymmetric dependency that makes it particularly tight:

```
Self-encoding REQUIRES eigenvalue arithmetic:
    Self-encoding requires PA
        PA requires ℕ
            ℕ requires linear eigenvalues (Leibniz rule)

Coalgebra morphism REQUIRES matching growth rates:
    Matching requires encoding to be linear (to match linear obs)
        Linear encoding is not injective
            No self-encoding with linear encoding

Therefore:
    Self-encoding requires linear eigenvalues
    Coalgebra morphism requires linear encoding
    Linear eigenvalues + linear encoding → encoding is not injective
    → Self-encoding and coalgebra morphism cannot coexist
```

The obstruction is **self-referential**: the system's ability to encode itself (which comes from having linear/additive arithmetic) is precisely what prevents the encoding from preserving observational behavior (which would require the encoding to also be linear/additive, but injective linear encodings of structured data don't exist).

### Comparison to Gödel's incompleteness

Both Gödel's theorem and the encoding obstruction are consequences of the intension/extension gap in self-naming systems:

| | Gödel's incompleteness | Encoding obstruction |
|---|---|---|
| **The system's power** | PA-strength arithmetic enables self-reference | Linear eigenvalues produce ℕ, enabling Gödel encoding |
| **What self-reference creates** | The Gödel sentence G ("I am not provable") | The eval-quote diagram (encoding as candidate coalgebra morphism) |
| **The intension/extension gap** | G names (intensionalizes) its own unprovability; unfolding (extensionalizing) the name never resolves it | The encoding names (intensionalizes) terms; the Leibniz rule unfolds (extensionalizes) them into structurally different forms |
| **Why it can't close** | The resolved form can be re-named, producing a new unresolvable sentence | The unfolded form can be re-named (re-encoded), but the new code has no fixed relationship to the old |
| **Passive consequence** | Incompleteness — true but unprovable sentences exist | The encoding exists but distorts dynamics |
| **Executable consequence** | The halting problem — self-executing code can't decide its own termination | The register — self-executing encoding requires external state for addition's carry propagation |

Gödel's theorem is about **passive** self-reference: the system names a proposition about itself but cannot resolve it. The encoding obstruction extends this to **executable** self-reference: the system not only names itself but tries to run its own encoding, and the execution step (which requires addition, which requires carry) introduces machinery the encoding cannot absorb.

In both cases: substitution is open-ended, naming is always one step behind unfolding, and no fixed point exists.

---

## Part 5: Proof Strategy for the Impossibility Theorem

> **Status update (2026-06-10).** The compositional version of this
> conjecture is now a machine-checked theorem
> (`SpectralArithmetic/Obstruction/QuotationCost.lean`,
> `quotation_overhead_superpolynomial`), with the qualitative
> bisimulation boundary in `Obstruction/Bisimulation.lean`. One
> correction: Step 3 below has a gap as stated — injectivity alone
> does NOT force code growth along a fixed computable trajectory,
> since a non-compositional primitive recursive injection can
> compress a sparse trajectory (j-th iterate to j, everything else
> high). The compositionality that Step 1's pairing lower bound
> implicitly assumes is a necessary hypothesis. With it, the
> separation is proved; without it, the conjecture below is open and
> unreachable by this argument.

### Formal statement

**Theorem (Encoding Obstruction, conjectured).** Let (State, compose, obs, ⊕) be a commutative semiring with derivation satisfying axioms A1-B5 (the eigenvalue arithmetic axioms). Let ε: Terms → ℕ be any primitive recursive injection with primitive recursive inverse. Define obs_ε(n) = ε(obs(decode(n))). Then the coalgebras (State, obs_semantic) and (State, obs_ε) are not bisimilar.

### Proof approach

**Step 1: Lower bound on encoding growth.**

Any primitive recursive injection ε: Terms → ℕ encoding a binary constructor (like compose) must satisfy a super-linear lower bound. Specifically, for the sub-encoding π: ℕ × ℕ → ℕ that handles pairs of sub-term codes:

```
For all m, n: π(m, n) ≥ max(m, n)    (to separate from both components)
Injectivity on the diagonal: π(m, m) ≠ π(m', m') for m ≠ m'
```

Combined with decodability (primitive recursive projections), this forces π(n, n) to grow faster than linearly. Specifically, any injective pairing with computable projections satisfies π(n, n) ∈ ω(n).

This is a known result from the theory of pairing functions. The intuition: a linear function ℕ × ℕ → ℕ has too few outputs (only ~2n values up to n for inputs up to n) to accommodate ~n² pairs.

**Step 2: Upper bound on eigenvalue trajectory growth.**

The semantic observation trajectory of f_k has eigenvalue growth:

```
obs^j(f_k) involves eigenvalue k^j    (by repeated application)
```

This is polynomial in k for fixed j, and geometric in j for fixed k.

**Step 3: Lower bound on syntactic trajectory growth.**

The syntactic observation trajectory of code ε(t) has growth determined by:

```
ε(obs(t)) involves re-encoding a Leibniz-expanded term
```

The Leibniz rule (R7) transforms obs(compose(a, b)) into compose(obs(a), b) ⊕ compose(a, obs(b)) — a **sum of two products**, each involving the sub-terms. Encoding this sum requires pairing the two summands, each of which is itself a product requiring pairing. The encoding of the Leibniz-expanded form involves nested applications of the super-linear pairing function.

After k observation steps on a term of depth d, the syntactic trajectory involves O(2^k) terms (Leibniz doubles at each step) each encoded via the pairing function. The total code size grows as the pairing function iterated 2^k times.

**Step 4: Trajectory divergence.**

For any pairing function π with π(n,n) ∈ ω(n), the syntactic trajectory grows strictly faster than the semantic trajectory after sufficiently many observation steps. Since bisimulation requires trajectory agreement at **all** observation depths, and the trajectories provably diverge, no bisimulation exists.

**Potential subtlety:** The argument must handle the possibility that specific terms (not generic ones) have encodings that accidentally align with eigenvalue structure. The proof must show that for any encoding ε, there exist terms whose trajectories diverge — the impossibility is existential on terms (∃t: trajectories diverge), not universal (which would be stronger but harder).

For the full impossibility (no bisimulation at all), we need: for any encoding ε, there exists at least one state where the two coalgebras disagree observationally. This is sufficient because bisimulation requires agreement on ALL states.

---

## Part 6: What Weaker Relationships Might Hold

The full bisimulation is impossible (if the trilemma argument is correct). But weaker notions could hold and would still be significant.

### Asymptotic behavioral equivalence

**Definition:** The two coalgebras are asymptotically equivalent if, for some normalization, the ratio of obs_code to obs_semantic converges:

```
lim_{n→∞} ε(obs(t_n)) / (n · ε(t_n)) = 1
```

for some family of terms t_n with ε(t_n) = n.

This would say: for "large" eigenstates, the syntactic and semantic observations approximately agree. The encoding distortion vanishes in the limit. This connects to the discrete-continuous bridge (Δ → d/dx as h → 0) — perhaps the two coalgebras agree in the same limit where finite differences converge to derivatives.

**Difficulty:** The encoding distortion (pairing) grows faster than linear, so the ratio likely diverges rather than converges. But this should be proved, not assumed.

### Partial bisimulation on a fragment

**Definition:** A sub-coalgebra S ⊂ State where obs_semantic and obs_code agree.

This would identify the **fragment of computation that has analytic content** — the terms whose Gödel codes happen to be eigenvalue-compatible. If this fragment can be characterized (e.g., terms in normal form, terms of bounded depth, terms encoding specific algebraic operations), it would carve computation at a natural joint.

**The interesting question:** Is the fragment trivial (only constants), finite, or structurally rich? If it's structurally rich — if there's a non-trivial class of terms whose encoding preserves observational behavior — that would be a positive result within the impossibility.

### Natural transformation between functors

**Definition:** A systematic relationship between obs_semantic and obs_code that isn't state-by-state bisimulation but preserves "shape."

If the two observation operations are related by a natural transformation η:

```
η ∘ obs_semantic = obs_code ∘ η
```

for some non-identity η: State → State, then the two coalgebras are "the same up to a change of basis." The encoding wouldn't preserve dynamics directly, but would preserve them after a systematic translation.

**This is the most promising weaker notion.** The distortion introduced by encoding might be systematic (always involving the same pairing-related correction) rather than chaotic. If so, η would be the "decoding correction" — the systematic adjustment needed to translate between eigenvalue arithmetic and code arithmetic.

### Behavioral equivalence on observables (not states)

**Definition:** The two coalgebras give different dynamics on states, but the same dynamics on **observable outputs**.

In the eigenvalue framework, the observable output of a state f_n is ultimately the eigenvalue n. If:

```
eigenvalue(obs_code(ε(t))) = eigenvalue(obs_semantic(f_{ε(t)}))
```

— that is, both observations yield the same eigenvalue even though they produce different intermediate states — then the coalgebras are "observationally equivalent at the output level" even though they disagree on internal dynamics.

This is weaker than bisimulation (which requires agreement at every observation step) but might be exactly the right notion: what matters is that the eigenvalue (the "number") is preserved, not that the path to it is identical.

---

## Part 7: Connection to the P vs NP Structural Analogy

### The trilemma as a structural analogue

The encoding obstruction trilemma has a precise structural parallel to P vs NP:

| Trilemma property | P vs NP analogue |
|---|---|
| **Eigenvalue arithmetic** (linear obs, gives ℕ) | **Verification** (polynomial-time certificate checking) |
| **Self-encoding** (super-linear pairing, gives self-reference) | **Construction** (finding a certificate — potentially super-polynomial) |
| **Coalgebra morphism** (matching growth rates) | **P = NP** (verification cost = construction cost) |

The trilemma says: verification (eigenvalue observation) is linear, construction (encoding) is super-linear, and no system can make them match without destroying one of them. P vs NP asks the same question at the complexity level: is verification always cheaper than construction?

### What this does and doesn't give

**Does give:** A precise algebraic setting where the verification/construction gap manifests as a provable impossibility (the trilemma), not an open conjecture.

**Doesn't give:** Any implication for actual P vs NP. The trilemma lives in a specific algebraic system (eigenvalue arithmetic). P vs NP lives in the complexity of Boolean circuits. The structural parallel is genuine but the logical implication is not established.

**The honest claim:** The trilemma is an instance of the same family of impossibility results that a hypothetical P ≠ NP proof would belong to — "you can't simultaneously preserve two incompatible structures" — realized at the algebraic level rather than the complexity level. Understanding the structural level is groundwork, not a solution.

### The intensional/extensional connection

The trilemma is the intension/extension gap made algebraically precise:

- **Intensional** (the form as a unit): `obs(compose(f₁, f₁))` — named, opaque, eigenvalue read off as a single number. This is the semantic side: what the state *does*. Linear.
- **Extensional** (the form unfolded): `oplus(compose(obs(f₁), f₁), compose(f₁, obs(f₁)))` — substituted, all structure visible, requiring pairing to encode. This is the syntactic side: what the state *is made of*. Super-linear.

The Leibniz rule IS the substitution that extensionalizes: it unfolds `obs(compose(a,b))` into its parts. The encoding must represent these parts (extensional), while the observation reads off a single value (intensional). The two live in incompatible regimes because they are opposite directions of the same duality.

For a passive encoding, this is just the familiar fact that syntax and semantics differ. For an **executable** encoding — where the code must actually perform the substitution — the mismatch becomes operational: the extensionalization step introduces addition (the ⊕ in the Leibniz sum), addition requires carry propagation, and carry requires external state. The executable encoding cannot be self-contained because substitution (extensionalization) crosses information boundaries that the encoding (intensionalization) keeps separate.

---

## Part 8: Relationship to Existing Impossibility Results

The encoding obstruction trilemma, if proved, would belong to a family of known results where individually reasonable structural properties are jointly unsatisfiable.

| Result | Properties in tension | Structural reason |
|---|---|---|
| **Encoding obstruction** (conjectured) | Eigenvalue arithmetic + Self-encoding + Coalgebra morphism | Pairing is super-linear, eigenvalues are linear, arithmetic requires linearity |
| **Gödel's incompleteness** | Consistency + Completeness + Self-reference | Diagonalization: self-reference + negation |
| **Heisenberg uncertainty** | Position precision + Momentum precision | Non-commuting observables (conjugate variables) |
| **Arrow's impossibility** | Transitivity + Unanimity + Non-dictatorship | Aggregation of ranked preferences |
| **No-cloning theorem** | Copying quantum states + Unitarity | Linearity of quantum mechanics |
| **Rice's theorem** | Decidability + Non-trivial semantic property + Self-reference | Reduction to halting problem |
| **CAP theorem** | Consistency + Availability + Partition tolerance | Network delays force trade-offs |

The common pattern: each theorem identifies a set of properties that are individually achievable and pairwise compatible, but not jointly satisfiable. The proof identifies a specific structural reason (a "pinch point") where the requirements conflict.

The encoding obstruction's pinch point is **pairing-linearity incompatibility**: injective encoding of structure requires super-linear pairing, eigenvalue observation requires linear indexing, and the arithmetic connecting them requires both. The self-referential character — arithmetic enables encoding, but arithmetic's linearity prevents encoding from preserving observation — places this in the same category as Gödel's theorem, where the system's expressive power creates the very limitation it reveals.

---

## Part 9: Research Program

### Immediate goal: prove the trilemma

The three components to formalize:

1. **Pairing lower bound:** Any primitive recursive injection ℕ × ℕ → ℕ with primitive recursive projections satisfies π(n,n) ∈ ω(n). (Known result in computability theory — needs citation and precise statement.)

2. **Eigenvalue linearity from Leibniz:** In any commutative semiring with derivation satisfying Leibniz rule, eigenvalues of iterated generators are linear: obs(f_n) = n · f_n. (Proved in the Lean formalization, Semiring.lean.)

3. **Arithmetic necessity for self-encoding:** Gödel encoding requires PA-strength arithmetic, which requires ℕ as a semiring, which requires linear eigenvalues. (Follows from the equiconsistency proof + the eigenvalue theorem.)

The trilemma then follows by combining (1), (2), and (3): linear eigenvalues are necessary for self-encoding, but linear eigenvalues are incompatible with any injective encoding being a coalgebra morphism.

### Secondary goal: characterize the boundary

If the trilemma is proved, characterize what **does** hold:
- Which terms (if any) have encoding-compatible trajectories?
- What is the weakest behavioral equivalence between the two coalgebras?
- Is there a natural transformation relating them?
- Does asymptotic equivalence hold in any limit?
- What is the maximal fragment on which partial bisimulation holds?

### Tertiary goal: formalize in Lean

The trilemma, being a statement about primitive recursive functions, eigenvalue arithmetic, and growth rates, is in principle formalizable. The ingredients are:
- The eigenvalue theorem (already in Semiring.lean)
- A theory of pairing functions (formalizable with Mathlib's number theory)
- Growth rate comparison (formalizable with Mathlib's asymptotic analysis)

This would be the most mathematically substantive result in the entire formalization — a structural impossibility theorem about self-representing systems, proved by machine.

### Long-term goal: connect to complexity theory

If the trilemma can be proved and the boundary characterized:
- Does the boundary between bisimilar and non-bisimilar fragments have complexity-theoretic content?
- Does the growth-rate gap between semantic and syntactic trajectories correspond to known complexity class separations?
- Can the trilemma be generalized beyond eigenvalue systems to other self-representing algebraic structures?

These are speculative but well-motivated by the structural parallel to P vs NP.

---

## Part 10: What the Trilemma Tells Us About the Theory

### The positive reading

The trilemma is not a failure of the theory — it's a **theorem about the theory** (once proved). It tells us something precise about the structure of self-representing eigenvalue systems: they necessarily have a syntax-semantics gap, and the gap has a specific algebraic character (pairing-linearity incompatibility).

This is analogous to how Gödel's incompleteness theorem is not a failure of PA — it's a deep structural result about what PA-strength systems can and cannot do. The encoding obstruction would be a deep structural result about what eigenvalue-arithmetic systems can and cannot faithfully encode.

### What the theory achieves despite the trilemma

The self-representation chain (self-representation.md, Parts 1-9) remains fully intact:

```
Algebraic framework → PA arithmetic → Self-representation → Internal computation → Incompleteness
```

Each arrow is a theorem. The trilemma says the chain cannot close into a loop (the encoding distorts dynamics), but the chain itself — framework encodes itself, defines computation, proves incompleteness — is genuine.

### What the trilemma redirects

The original conjecture asked: does the self-referential loop close? The trilemma answers: **not through encoding**. But this redirects rather than terminates the investigation:

1. **Could the loop close through a mechanism other than Gödel encoding?** Perhaps a non-injective representation (lossy but structure-preserving) could maintain a coalgebra morphism at the cost of not being a full encoding.

2. **Could a weaker closure hold?** Natural transformation, asymptotic equivalence, or partial bisimulation (Part 6) might provide a meaningful sense in which the loop "almost" closes.

3. **Is the gap itself the interesting object?** The precise characterization of where the two coalgebras agree and disagree might be more informative than a yes/no answer to bisimulation. The *structure* of the gap — which is what the boundary characterization (Part 9) would reveal — could be the real mathematical content.

### The deepest reading

The trilemma says: **mathematics is substitution, and substitution is open-ended.** Any formal system powerful enough to name its own expressions can unfold those names (substitute), producing new expressions that can themselves be named. The intensional and extensional views of a form are irreducible to each other in any self-naming system.

For passive encoding, this gives incompleteness: the Gödel sentence names its own unprovability, and the system can substitute into that name (unfold it) but can never reach a final substitution that resolves it — because the resolution would itself be a form that can be named and substituted again.

For executable encoding, this gives the register: to actually *perform* the intension/extension switching (not just describe it), the system must manipulate positions, addition crosses positional boundaries, and the boundary-crossing requires external state. The "map is not the territory" not because mapping is lossy (it's injective), but because **the act of mapping introduces operations (addition, carry) that the territory doesn't contain (eigenvalue scaling is multiplicative, not additive).**

The key distinction between this framework and raw PA: in the eigenvalue framework, the intensional side (obs reads eigenvalue n, multiplicative, local) and the extensional side (Leibniz rule introduces ⊕, additive, non-local) produce *visibly different operations*. In PA, both sides are already arithmetic, so the gap is harder to see. The framework makes the obstruction visible as two different kinds of operation where there should be one.

### Refinement: the information domain and ⊕

The growth-rate argument (pairing is super-linear, eigenvalues are linear) is weaker than it appears. Measured in **information content** (bit length) rather than arithmetic value, both pairing and eigenvalue scaling are additive — the super-linear/linear mismatch disappears. Binary interleaving maps k + k bits to 2k bits; eigenvalue scaling doubles the bit length. Both are additive in the information domain.

However, moving to the information domain transforms ⊕ (addition of numbers) into tropical max (max of bit lengths), which is idempotent and non-cancellative. This destroys the PA arithmetic needed for self-encoding.

The refined obstruction is not growth rates — it is **⊕ itself**. The additive operation that makes eigenvalues form ℕ is the same operation that resists every change of domain that would reconcile encoding with observation. The precise algebraic constraint: ⊕ must be simultaneously cancellative (for PA), characteristic-zero (for eigenvalue theorem), and bit-compatible (for encoding morphism) — and no operation satisfies all three.

See [information-domain.md](information-domain.md) for the full analysis, including the derivative chain as information layers, tropical algebra, the ⊕ spectrum (XOR, p-adic, modular alternatives), and candidate third domains (p-adic integers, 2-adic streams).

---

## Related

- [addition-non-locality.md](addition-non-locality.md) — The foundational layer: carry propagation forces external state in self-encoding systems with addition
- [computing-as-external-state.md](computing-as-external-state.md) — Why computation is language + external state: the obstruction as metatheorem about Turing/Church
- [information-domain.md](information-domain.md) — The information-domain analysis: bitwise encoding, tropical algebra, and the refined ⊕ obstruction
- [self-representation.md](self-representation.md) — The Gödel encoding, self-representation chain, and original discrete-continuous conjecture
- [confluence.md](confluence.md) — The oriented rewriting system that defines obs_code
- [../assessments/novelty.md](../assessments/novelty.md) — Novelty analysis, the eval-quote diagram, and the intensional/extensional framing
