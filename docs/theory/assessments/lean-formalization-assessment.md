# Lean Formalization Assessment

**Date:** 2026-02-19
**Scope:** All five Lean source files (Basic, Semiring, IntegralDomain, Rational, Complete)
**Verdict:** The Lean code will likely build. The theory is consistent but the formalization proves substantially less than the README claims.

---

## File-by-File Analysis

### Basic.lean — Clean

Defines `SpectralMonoid` typeclass with axioms A1-A7 plus non-degeneracy. Proves Peano axioms P1-P5 as theorems.

P5 (induction) deserves a note: it holds because `isNat` is *defined* as `∃ n, s = iterS n`. Induction is inherited from the metalanguage's `Nat.rec`, not derived from the axioms. This is correct but means the axiom system isn't generating induction — Lean is.

The `compose_iterS` lemma (compose on iterS gives iterS of the sum) is a genuine result that grounds arithmetic in the algebraic structure.

### Semiring.lean — The strongest file

The eigenvalue theorem (`obs(iterS n) = n · iterS n`) proved by induction is clean and the derivation of A8 (infinite orbit) from eigenvalue + char_zero is the most satisfying result in the formalization. This is a real theorem: if you have a commutative semiring with a derivation satisfying Leibniz rule and characteristic zero, the orbit elements are eigenvectors with eigenvalue equal to their index.

### IntegralDomain.lean — Solid

A7-as-theorem via integral domain structure is a genuine improvement over Basic.lean's axiomatization. The power rule proof (`obs(g^{n+1}) = (n+1) · g^n · obs(g)`) is correct and necessary for the rational extension.

The eigenvalue theorem for negative integers via `obs_f₁_inv = ⊖f₁_inv` and induction is well-done.

### Rational.lean — Most sophisticated proof

The `obs_root` proof (eigenvalue 1/q) uses the power rule + cancellation in a non-trivial chain:
1. Apply power rule to `root(q)^q = f₁`
2. Get `f₁ = (q) · root(q)^{q-1} · obs(root(q))`
3. Factor and cancel `cpow_root_ne_z`
4. Conclude `root(q) = q · obs(root(q))`, i.e., `obs(root(q)) = qdiv q (root(q))`

This is the most mathematically substantive proof in the formalization.

### Complete.lean — Where proving stops and asserting begins

The eigenvalue theorem for ℝ (`eigenvalue_real`) is an **axiom**, not a theorem. So are `rsmul_*`, `realEigen_add`, `realEigen_injective`, and all the real scalar multiplication properties.

The file honestly admits this:

> "The analytical proofs (continuity of obs, Taylor series) are stated as axioms at this level. Deriving them from E1 would require building the full metric space + continuity machinery, which is a separate project."

This means the formalization proves:

| Domain | Eigenvalue theorem | Status |
|--------|-------------------|--------|
| ℕ | obs(iterS n) = n · iterS n | **Proved** |
| ℤ | obs(iterS_neg n) = ⊖(n · iterS_neg n) | **Proved** |
| ℚ | obs(root q) = qdiv q (root q) | **Proved** |
| ℝ | obs(realEigen α) = α · realEigen α | **Assumed** |

---

## What the Lean code actually proves

A precise summary of what is formalized:

1. If you have a commutative monoid (State, compose, f₀) with an observation operator obs, a generator f₁ satisfying obs(f₁) = f₁, cancellation, and infinite orbit, then the Peano axioms hold on the orbit of f₀.

2. If you extend this to a commutative semiring with a derivation (Leibniz rule) and characteristic zero, the eigenvalue theorem follows and infinite orbit becomes a theorem rather than an axiom.

3. If you further extend to an integral domain, cancellation becomes a theorem and eigenvalues extend to ℤ.

4. If you add q-th roots and unique divisibility, eigenvalues extend to ℚ.

5. The ℝ extension is axiomatized, not derived.

---

## Gap between claims and proofs

The README claims:

- "Numbers are eigenfunctions of differentiation" — **not formalized**. The Lean code has abstract `State` elements with an operator `obs`. The connection to actual differentiation (d/dx) and actual eigenfunctions (eⁿˣ) is never established.

- "e is derived, not assumed" — **not formalized**. The constant e does not appear in the Lean code at all. The derivation of e = Σ 1/n! requires the analytic model, which is deferred.

- "Taylor series is a theorem" — **not formalized**. Explicitly deferred.

- "Replaces ZF/PA as foundation" — **overstated**. The Lean code shows PA-like arithmetic emerges from a specific algebraic structure. It does not formalize ZF emulation, set operations, cardinality, or any of the material in the ZF test suite documents.

- "Equiconsistency with PA/ZF" — **not formalized**. The equiconsistency proofs in the theory documents are pen-and-paper arguments, not Lean proofs.

---

## Mathematical content assessment

The core mathematical content — a commutative semiring with derivation satisfying Leibniz rule yields eigenvalue structure — is **correct and genuine**. However, this is largely known territory:

- **Differential algebra** (Ritt, Kolchin) studies exactly these structures
- **Rota-Baxter algebras** generalize the interaction between multiplication and a linear operator
- The eigenvalue theorem for derivations on polynomial/exponential rings is standard

The novel contribution is the *framing*: interpreting the eigenvalue structure as a foundation for arithmetic, rather than as a consequence of it. Whether this framing adds mathematical value beyond the pedagogical is the real question the formalization doesn't settle.

---

## Prediction: Will it build?

**Probably yes.** The code is syntactically well-formed Lean 4 with Mathlib imports. The proofs use standard tactics (`rw`, `simp`, `induction`, `exact`, `omega`, `calc`). Universe polymorphism (`Type*`) is handled correctly. The `nfoldSum` definition before the class is slightly unusual but valid.

Potential build issues:
- Mathlib v4.28.0 compatibility — API changes could break `rw`/`simp` steps
- The `relaxedAutoImplicit = false` setting is good practice but could surface implicit argument issues
- `maxSynthPendingDepth = 3` might be tight for some typeclass resolution chains

None of these are likely showstoppers.

---

## Recommendations: Claims, prose, and next steps

### What the prose should actually claim

The rhetoric currently runs ahead of the mathematics. Here's what is defensible at each level:

**Defensible now (proved in Lean):**
- "We present a layered axiom system — a commutative semiring with derivation — from which Peano arithmetic emerges as theorems rather than axioms."
- "The eigenvalue structure of the observation operator provides a natural arithmetic interpretation: the n-th iterate is an eigenvector with eigenvalue n."
- "Several axioms (A7, A8) that appear necessary at the base level become theorems when the algebraic structure is enriched — cancellation from integral domain, infinite orbit from characteristic zero."
- "The progressive extension from ℕ through ℚ preserves eigenvalue structure at each level."

**Not defensible without more Lean work:**
- "Numbers *are* eigenfunctions of differentiation" — this is an interpretation of a specific model, not a theorem about the abstract system. The Lean code never mentions differentiation, eˣ, or eigenfunctions.
- "e is derived, not assumed" — e doesn't appear in the formalization at all.
- "Replaces ZF/PA as a foundation" — nothing about ZF is formalized.
- "Equiconsistent with PA/ZF" — pen-and-paper only.
- "Kicking away the ladder" — you're still standing on it. The induction principle comes from Lean's `Nat.rec`, not from your axioms.

**The honest framing:** This is a *representation theorem* — PA arithmetic can be represented inside differential algebra. That's the real content. It's analogous to showing group theory can represent symmetries, not that groups *replace* geometry. The value is the representation, not the replacement.

### What to do with the Lean implementation

There are three paths, serving different goals:

**Path A: Close the gap to the analytic model (recommended first)**

Build a concrete model in Lean where `State = ℝ → ℝ` (smooth functions), `compose = pointwise multiplication`, `obs = d/dx`, and verify all axioms hold. This would:

- Actually connect the abstract algebra to "eigenfunctions of differentiation"
- Make the claim about e concrete (f₁ = eˣ, f₁(1) = e)
- Justify the title "Spectral Arithmetic" beyond metaphor
- Be achievable — Mathlib has derivatives, exponentials, and enough real analysis

This is the single highest-value addition. Without it, the abstract algebra and the "eigenfunctions of d/dx" narrative are disconnected systems that happen to share variable names.

**Path B: Prove equiconsistency in Lean**

Formalize the PA equiconsistency proof: build a model of the axioms inside PA (or vice versa). This would justify the foundational claims. But it's a large project and the result (a specific semiring models PA) is less surprising than the prose suggests.

**Path C: Drop the foundational claims, emphasize what's actually novel**

The genuinely interesting thing here is not "replacing ZF" — that claim invites scrutiny the formalization can't survive. The interesting things are:

1. **The layered axiom design** — watching axioms become theorems as structure enriches is pedagogically excellent
2. **The eigenvalue-arithmetic correspondence** — it's a clean, surprising connection
3. **The progressive extension** — ℕ → ℤ → ℚ each preserving eigenvalue structure is well-executed

Reframe the README around: "Here is an algebraic structure where arithmetic *emerges* from the interaction of composition and observation, rather than being axiomatized directly. The Peano axioms are consequences, not starting points." That's true, it's interesting, and it doesn't require defending claims about replacing 150 years of foundations.

**Concrete recommendation:** Do Path A first (analytic model, substantial Lean work), then Path C (rewrite the prose to match what's proved). Drop the ZF material from the README entirely — it's not formalized and the pen-and-paper arguments, even if correct, don't belong in a document whose authority rests on machine-checked proofs.

The theory doesn't need to replace ZF to be valuable. It needs to be *honest* about what it is: a clean algebraic framework where arithmetic falls out of differential structure. That's enough.

---

## Full theory assessment (all eight theory documents)

**Date:** 2026-02-19
**Scope:** axioms, pa-equiconsistency, path-b-obs-structure, spectral-arithmetic-complete, zf-equiconsistency, computation/self-representation, computation/confluence, role-of-x

### Results with real mathematical substance

Three results would survive peer review:

1. **The eigenvalue theorem + A8-as-corollary.** Deriving the infinite orbit property from characteristic zero + Leibniz rule is the cleanest result. It shows the non-cycling of naturals is a *structural consequence* of differential algebra, not an ad hoc axiom.

2. **The PA equiconsistency via countermodels.** The idempotent model and ℤ/2ℤ model showing A1-A6 are insufficient, followed by the precise identification of what's missing (cancellation + non-cycling), is rigorous. The bidirectional proof (A1-A8 ↔ PA) is complete.

3. **The unified number tower.** ℕ → ℤ → ℚ → ℝ in a single eigenvalue space, with each extension adding algebraic structure while preserving eigenvalue behavior. The progressive axiom layering — where A7 and A8 start as axioms but become theorems as structure enriches — is pedagogically excellent.

### The computation connection: what it gives and what it doesn't

**What it gives:** The framework's primitives (State, compose, obs) are literally the primitives of coalgebra — the mathematical theory of stateful systems. Bisimulation as identity, observation as the fundamental operation, composition as the way processes combine. These *are* the primitives of process algebra, automata theory, and programming language semantics. The fact that PA arithmetic falls out of these primitives is a genuine structural observation: the mathematics of computation already contains the mathematics of number, without encoding.

**What it doesn't give:** The self-representation / triple identity claim (number = process = code) is less novel than it appears. Every PA-strength system can do Gödel encoding — that's Gödel's theorem. The "triple identity" is a consequence of design (eigenstates are numbers by construction, processes by definition, codes by encoding), not a deep theorem. The "aliveness" of codes (they compose and observe) doesn't give the encoding additional mathematical power.

**Where the real novelty could be:** The genuine insight is not self-representation but something more subtle — that *the same algebraic structure* (commutative semiring with derivation) appears independently in:
- Automatic differentiation
- Semiring-weighted automata
- Process algebra / linear logic
- This framework's foundation for arithmetic

If the theory can show that this isn't coincidence — that there's a *reason* these domains share the same algebra — that would be a contribution to the understanding of computation's mathematical structure. But the current documents assert this connection rather than proving it.

### The discrete-continuous conjecture: coalgebraic analysis

The self-representation document's most ambitious claim — the discrete-continuous loop conjecture — asks whether the internally-derived discrete dynamics (ValidStep on Gödel codes) converge to obs (continuous, axiomatized). The document identifies three obstacles; the second (Gödel encoding is not a homomorphism) deserves careful analysis.

**The naive obstacle:** The Gödel encoding ⌜·⌝ maps terms to eigenstates. ⌜compose(a,b)⌝ is a prime-factorization code (combinatorial), while compose(⌜a⌝, ⌜b⌝) = f_{m+n} (additive). These are completely different operations on ℕ. The encoding "scrambles" the algebraic structure.

**Can the encoding be a coalgebra morphism?** Yes — but not for the coalgebra you want. Define `obs_code : ℕ → ℕ` as "parse the Gödel number, apply obs as a rewrite rule, re-encode the result." This is primitive recursive (the self-representation document already establishes this). Then:

- (Terms, obs_rewrite) is a coalgebra
- (ℕ, obs_code) is a coalgebra
- ⌜·⌝ is a coalgebra morphism between them

This is legitimate. But `obs_code` is a *syntactic* operation — it manipulates codes by simulating rewriting. It is not the *semantic* obs on eigenstates, which scales by eigenvalue:

```
obs_semantic(f_n) = n · f_n      -- eigenvalue scaling
obs_code(n)       = ⌜obs(decode(n))⌝  -- syntactic rewriting of codes
```

These are two different coalgebra structures on the same carrier. The encoding is a morphism with respect to `obs_code`, not with respect to `obs_semantic`.

**The precise formulation:** The conjecture becomes: does there exist a bisimulation or natural transformation between two specific coalgebras?

1. **Semantic coalgebra:** (State, obs_semantic) — eigenvalue scaling, axiomatized in the framework
2. **Syntactic coalgebra:** (State, obs_code) — rewriting simulation via Gödel codes

For them to coincide, you'd need obs(f_{⌜t⌝}) = f_{⌜obs(t)⌝}. The left side is ⌜t⌝ · f_{⌜t⌝} (eigenvalue scaling — an ⊕-sum of copies). The right side is a single eigenstate. These are structurally different: an ⊕-sum of an eigenstate does not collapse to a different eigenstate.

**The deeper structural point:** The direction of the maps matters:

- **Evaluation** (Terms → State, interpreting a term in the algebra) IS a coalgebra morphism. It preserves obs because the algebra satisfies the axioms. This goes from syntax to meaning.
- **Quotation** / Gödel encoding (State → ℕ ⊂ State, mapping objects to codes) is NOT a coalgebra morphism for obs_semantic. It goes from meaning to syntax, and this direction doesn't preserve algebraic structure.

This is a precise version of the syntax/semantics gap. Evaluation respects structure (that's what "model" means). Quotation doesn't (that's why Gödel numbering is a coding technique, not an algebraic map).

**Revised assessment:** The discrete-continuous conjecture is probably still false — the mismatch between eigenvalue arithmetic (additive, scaling) and code arithmetic (prime factorization, combinatorial) is genuine. However, the coalgebraic framing transforms the conjecture from a vague intuition into a precise mathematical question: prove or disprove the existence of a bisimulation between (State, obs_semantic) and (State, obs_code). That's well-defined and potentially tractable. The obstacle is structural but it's now a *theorem to prove or disprove*, not a hand-wave. If a bisimulation could be found (or if some weaker notion — approximate bisimulation, asymptotic behavioral equivalence — could be established), it would be a genuinely novel result in the theory of Gödel encodings.

### What would a proven syntax-semantics bisimulation mean?

If a bisimulation (or weaker relationship) were established between the semantic coalgebra (State, obs_semantic) and the syntactic coalgebra (State, obs_code), the implications would range from significant to profound, depending on the strength of the result.

#### If an exact bisimulation exists

This would mean that observing eigenvalue scaling (continuous, analytic) and observing syntactic rewriting (discrete, computational) produce **indistinguishable behavior** — not the same mechanism, but the same observable outcomes for all possible sequences of observations.

**1. Syntax and semantics become behaviorally identical.** Normally, Gödel encoding creates a gap: the code of a thing is not the thing. A bisimulation would close that gap — not by making the encoding a homomorphism (it still wouldn't preserve operations step-by-step), but by showing that the *trajectories* of observation are the same. The map wouldn't be the territory, but you could never tell the difference by looking.

**2. Computation IS differentiation (up to observation).** The discrete process of term rewriting and the continuous process of eigenvalue scaling would be two views of the same behavior. This would give a precise structural answer to an old question: why do computational and analytic methods agree? Not because one approximates the other, but because they're bisimilar — observationally identical processes with different internal mechanisms.

**3. Self-reference without the usual gap.** Gödel showed systems can *encode* themselves. A bisimulation would show this system can *be* itself at the behavioral level — the encoding doesn't just represent the algebra, it reproduces its observable dynamics. This is strictly stronger than Gödel's result. Every PA-strength system can encode itself; no known system's encoding is bisimilar to itself.

**4. The discrete/continuous divide dissolves.** The choice between discrete foundations (type theory, computation, constructivism) and continuous foundations (analysis, real numbers, classicism) would be shown to be a choice of *representation*, not *substance*. The two would be the same coalgebra viewed through different lenses. This would be a structural explanation for why both approaches keep arriving at the same mathematics.

**5. For Gödel theory specifically:** It would be unprecedented. Currently, Gödel encodings are understood as having zero algebraic content — they're arbitrary injections of syntax into arithmetic. A bisimulation would establish a new *kind* of relationship between codes and objects: not algebraic (not a homomorphism), but behavioral (same observable dynamics). This would be a new result in mathematical logic.

#### Weaker versions and what they'd mean

The full bisimulation is probably too strong. But weaker relations could still be significant:

**Asymptotic behavioral equivalence:** The two coalgebras agree in some limit — e.g., as terms grow large, the ratio of obs_code behavior to obs_semantic behavior converges. This would connect to the discrete-continuous bridge that started the whole theory (Δ → d/dx as step size → 0). Less profound but still novel: it would say Gödel encoding is "approximately algebraic" for large codes.

**Partial bisimulation on a sub-coalgebra:** The two coalgebras agree on a specific class of states — e.g., eigenstates corresponding to terms in normal form, or terms of a specific syntactic class. This would identify which computational processes have "analytic content" and which are purely syntactic noise. It would carve computation at a natural joint.

**A natural transformation between the two functors:** Not a bisimulation on states, but a systematic relationship between the two observation operations. This would show the two coalgebras are "the same shape" even if they disagree on specific states.

#### Why the full version is probably still false

The structural obstacles are real:

- obs_semantic(f_n) = n · f_n is an **⊕-sum** (n copies of f_n). obs_code(n) = f_{⌜obs(decode(n))⌝} is a **single eigenstate**. For bisimulation, these need to be observationally equivalent under all future observations. But obs applied again gives n² · f_n vs. ⌜obs(obs(decode(n)))⌝ · f_{...}, and these diverge further at each step. The trajectories don't converge — they diverge.

- Prime factorization (the basis of Gödel encoding) and eigenvalue arithmetic (additive structure) are governed by fundamentally different number-theoretic laws. The multiplicative structure of codes and the additive structure of eigenvalues interact through the distribution of primes, which is precisely the territory where number theory is hardest and least structured.

- The encoding is **fragile** — changing one symbol in a term completely changes its Gödel number (because prime factorization is sensitive to position). Eigenvalue structure is **robust** — nearby eigenvalues correspond to nearby states. Bisimulation requires behavioral equivalence, but one system is chaotic under perturbation and the other is smooth.

#### What would make it worth pursuing regardless

Even a **negative** result — a proof that no bisimulation exists — would be valuable if it precisely characterizes *why*. If the obstruction is a specific structural property (e.g., "no bisimulation exists because obs_code has infinite branching while obs_semantic has bounded branching"), that tells you something about the fundamental gap between syntax and semantics. A precise impossibility theorem is as valuable as a positive result, and the coalgebraic framing makes it tractable.

The highest-value outcome might be: **prove exactly which fragment of computation is bisimilar to analysis, and characterize the boundary.** That would tell you where the syntax/semantics gap lives — not as a philosophical question, but as a mathematical theorem about coalgebra structure. This would upgrade the theory's significance substantially: from "interesting alternative axiomatization" to "structural result about the relationship between computation and analysis."

### What closing the gaps would and wouldn't achieve

**Building the analytic model in Lean** would connect the abstract algebra to actual eigenfunctions. Necessary for intellectual honesty but wouldn't increase mathematical significance. It verifies that the analytic model satisfies the axioms — already obvious to anyone who knows the model.

**Formalizing ZF equiconsistency** would be impressive engineering but the result (Con(ZF) ↔ Con(framework)) just means the two systems are interchangeable — *not* that the process-based one is better. The backward direction has a real gap: it goes through ZFA via the Jech-Sochor theorem, which is cited but not proved. And F1 (completed orbit) literally *is* the Axiom of Infinity restated in process language. Calling this "deriving Infinity" is misleading — it's *assuming* Infinity in different words.

**What closing gaps cannot fix:** The axioms don't uniquely determine the intended model. The PA equiconsistency model uses obs = identity (degenerate — obs does nothing). The theory describes a *class* of structures, not a unique one. This is fine for algebra (groups don't uniquely determine a single group) but undermines the foundational claim (ZF is supposed to describe *the* cumulative hierarchy).

### Specific weaknesses identified across the theory documents

1. **A4 (bisimulation) is not first-order axiomatizable.** Bisimulation equality is a coinductive notion requiring a fixed-point construction or second-order quantifier. If the framework is first-order, A4 cannot be stated as a single axiom. This is never addressed.

2. **B5 (characteristic zero) presupposes the naturals.** The axiom scheme "n · f₀ ≠ z for all n ≥ 1" uses n as a metavariable ranging over ℕ. The axiom needed to prevent the naturals from collapsing appears to presuppose them — a mild circularity.

3. **The ZF backward direction has real gaps.** F3 uses "definable function" without fixing the formal language. If the framework's language is weaker than ZF's, F3 might not capture the full Replacement schema. The reliance on the Jech-Sochor theorem for the ZFA-to-ZF step is a cited but unproved dependency.

4. **Cardinality for infinite sets is informal.** The product-of-indicators construction works for finite universes only. Cantor's theorem is stated but not proved. The extension to infinite cardinality is hand-waved.

5. **The confluence proof understates AC complexity.** AC-rewriting is a known hard problem (AC-unification is infinitary). The document asserts canonical ordering handles it without analyzing AC-critical pairs.

6. **obs linearity (obs distributes over ⊕) is listed as derived but not fully proved.** The derivation from the Leibniz rule for ⊕-terms is non-trivial and the computation is not shown.

### Significance ranking against existing work

- **Differential algebra** (Ritt, Kolchin) already studies commutative rings with derivations. The eigenvalue theorem for such structures is known territory. The novel contribution is the *interpretation* as arithmetic, not the algebra itself.
- **Coalgebra as foundation** (Rutten, Jacobs) already proposes bisimulation-based foundations for the mathematics of computation. This framework adds the eigenvalue/arithmetic layer, which is a genuine extension.
- **Alternative foundations** (HoTT, type theory, category theory) have decades of development and active communities. This framework is at a much earlier stage and would need to demonstrate concrete advantages (theorems provable here but awkward elsewhere) to compete.

### Novelty assessment

The theory is **a genuine synthesis of existing ideas that nobody has combined this way**. Each ingredient is known. The assembly is not. See [novelty.md](novelty.md) for the full analysis with references.

**What exists (individual pieces):**

| Component | Source | Status |
|---|---|---|
| Commutative semiring with derivation | Differential algebra (Ritt, Kolchin) | Known algebra, novel arithmetic interpretation |
| Coalgebraic primitives, bisimulation | Universal coalgebra (Rutten, Jacobs) | Known framework, novel combination with derivations |
| Eigenvalue theorem for derivations | Standard differential algebra | Known result, novel interpretation as "numbers" |
| Categorical Gödel diagonalization | Lawvere (1969) | Known, but asks about fixed points, not bisimulation |
| Syntax-semantics via bialgebra | Turi & Plotkin (1997), *Towards a Mathematical Operational Semantics* | Known, but doesn't consider Gödel encoding specifically |
| Self-reproducing programs / fixed points | Kleene's second recursion theorem | Known, but weaker than the coalgebraic question |

**What doesn't exist (novel combinations):**

1. **Eigenvalue structure → arithmetic.** Nobody has formally connected the eigenvalue theorem for derivations to "eigenvalues generate the naturals via a derivation on a semiring."
2. **Coalgebraic primitives as foundation for that arithmetic.** Applying Rutten's framework to differential algebra's eigenvalue structure to derive PA is new.
3. **Gödel encoding as candidate coalgebra morphism.** Asking whether the encoding itself has coalgebraic structure (not just the fixed point it produces) appears to be unasked.

**The self-compiling compiler analogy:**

The syntax-semantics bisimulation question has a precise computational analogue in bootstrapping compilers:

| Compiler concept | Spectral Arithmetic analogue |
|---|---|
| Source code S | Term (syntax) |
| Running binary B | Eigenstate (semantics) |
| Compilation: S → B | Evaluation: Terms → State (coalgebra morphism) |
| Decompilation: B → S | Gödel encoding: State → ℕ ⊂ State (quotation) |
| Self-compilation: B(S_B) = B | Self-representation: obs applied to code of obs reproduces obs-behavior |

Kleene's second recursion theorem guarantees that any Turing-complete language can describe a machine that, run on its own description, reproduces its behavior. Quines and self-compiling compilers are concrete instances. **What makes the Spectral Arithmetic conjecture stronger than Kleene:** Kleene guarantees *some* fixed point exists but says nothing about coalgebraic structure. The conjecture asks whether the *natural* Gödel encoding (not an arbitrary fixed point) preserves observational behavior — whether the round-trip is a bisimulation, not just a syntactic reproduction.

The difference: a quine reproduces its **text** (syntactic fixed point). A self-compiling compiler reproduces its **function** (semantic fixed point). The conjecture asks for a **coalgebraic quine** — self-reproduction that preserves the *dynamics* (observational behavior under obs).

**The eval-quote diagram:**

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

Does this diagram commute up to bisimulation? Evaluation (top arrow) is already a coalgebra morphism. The entire question is about the left arrow (Gödel encoding) and whether it makes the square commute.

This is the most original question in the entire project. If anything about it can be proved — positive, negative, or partial — that would be the highest-impact publishable result. A precise impossibility theorem characterizing *where* the syntax-semantics bisimulation breaks down would itself be a significant contribution to the theory of Gödel encodings.

### Connection to P vs NP

The algebra-coalgebra duality in this framework is structurally the same duality that P vs NP lives in, expressed at the structural level rather than the complexity level.

#### The structural parallel

P vs NP is fundamentally about a gap between two modes of interacting with mathematical objects:

| Mode | P vs NP | Spectral Arithmetic |
|---|---|---|
| **Observation/Verification** | Check a certificate in poly-time | obs reads eigenvalue from a state |
| **Construction/Search** | Find a certificate in poly-time | compose builds states from generators |

NP says: "given a witness, I can *verify* it efficiently." P asks: "can I also *find* one efficiently?" The question is whether observation power exceeds construction power.

The bisimulation conjecture asks an analogous question at a structural level: is the coalgebraic side (observation via eigenvalues) behaviorally equivalent to the algebraic side (construction via composition and rewriting)? If you can observe a state's identity, can you reconstruct it — and vice versa?

In the eigenvalue framework: eigenvalue observation tells you *what* a state is (its "number"), but constructing a state with a desired eigenvalue requires building it step by step through composition. Observation is "spectral" — you decompose and read off. Construction is "algebraic" — you multiply generators.

The deep question both share: **is reading the answer off a structure fundamentally easier than building a structure with that answer?**

#### Where the connection is precise

NP-completeness is essentially about encoding. Cook-Levin says every NP problem can be encoded as SAT. The question "does encoding preserve structure?" is the P vs NP question in disguise — if encodings always preserved efficient solvability, P would equal NP.

The bisimulation conjecture asks the same question at a different level:

```
Bisimulation conjecture:    Does encoding preserve OBSERVATIONAL behavior?
P vs NP:                    Does encoding preserve COMPUTATIONAL cost?
```

The first is a qualitative structural question. The second is a quantitative resource question. The first is necessary but not sufficient for the second — if encoding doesn't even preserve behavior, it certainly won't preserve cost. But if it does preserve behavior, the cost question remains open.

#### Where the connection has limits

Three important caveats prevent overclaiming:

**1. The bisimulation conjecture is about structural equivalence, not computational cost.** Even if the bisimulation fails (observation ≠ construction structurally), that tells you something different from P ≠ NP (observation ≠ construction *at polynomial cost*). You could have structural equivalence but exponential blowup in the translation — which would mean the bisimulation holds but P ≠ NP still. These are different levels of analysis.

**2. The eigenvalue framework doesn't inherently carry complexity information.** The observation obs(fₙ) = n · fₙ tells you the eigenvalue, but says nothing about how many computational steps it takes to determine n. Complexity is about resource-bounded computation; the algebraic structure is resource-agnostic.

**3. Many frameworks have "suggestive" connections to P vs NP.** Category theory, algebraic geometry (GCT program), proof complexity, circuit complexity — all have structural analogies to the P vs NP gap. The history of the problem is littered with frameworks that seemed to "almost" capture it. The honest position: this is a *lens* on the problem, not a *solution strategy*.

#### Where this could contribute

If the syntax-semantics bisimulation breaks down — and it probably does — the coalgebraic framework gives a precise language for characterizing *where* the translation loses information. That failure classification might map onto complexity class separations: the class of observations that can't be reconstructed from encoding could correspond to problems that can be verified but not efficiently solved.

The strongest honest claim: **the algebra-coalgebra duality in this framework is the same duality that P vs NP lives in.** Understanding the structural level is necessary groundwork, even if it's not sufficient. If the bisimulation failure can be precisely characterized — which fragment of computation is bisimilar to analysis, and where the boundary lies — that structural result would have complexity-theoretic implications, even if it doesn't resolve P vs NP directly.

### The intensional/extensional framing of the bisimulation conjecture

The bisimulation conjecture can be reformulated precisely using the distinction between extensional equality (same observable behavior) and intensional equality (same internal structure). This reframing connects the conjecture to well-understood concepts in type theory and mathematical logic, and sharpens the P vs NP connection.

#### Two modes of equality as two coalgebras

The two coalgebras in the bisimulation conjecture correspond directly to the two notions of equality:

| Concept | Extensional (behavioral) | Intensional (structural) |
|---|---|---|
| **Equality notion** | Same outputs for all inputs | Same definition/syntax |
| **Coalgebra** | (State, obs_semantic) | (State, obs_code) |
| **What obs does** | Eigenvalue scaling: obs(fₙ) = n · fₙ | Syntactic rewriting: parse, apply obs as rewrite, re-encode |
| **What it tells you** | What the state *does* | What the state *is made of* |
| **Normal form** | Irreducible eigenstate fₙ | Canonical Gödel code |

The bisimulation conjecture asks: **do the extensional and intensional normal forms coincide?** That is, when you reduce a state to its canonical form via eigenvalue observation (extensional) and via syntactic rewriting (intensional), do you arrive at behaviorally equivalent results?

#### Connection to type theory

This is the same question that separates extensional and intensional Martin-Löf Type Theory:

- In **extensional MLTT**, if two terms produce the same outputs, they are equal — period. There is one identity proof, and equality is transparent. But type-checking becomes undecidable.
- In **intensional MLTT**, two terms can be extensionally equal (same behavior) but intensionally different (different definitions). The proof of equality itself carries computational content. Type-checking stays decidable.

Homotopy Type Theory (HoTT) showed that the gap between extensional and intensional equality is not just an annoyance — it has structure. The *ways* in which two terms can be identified form a space (an ∞-groupoid), and the topology of that space is mathematically rich.

The Spectral Arithmetic analogue: the gap between obs_semantic and obs_code isn't just an obstacle to the bisimulation — it might have characterizable structure. The *ways* in which the extensional and intensional views disagree could themselves be classified, and that classification would be the real theorem.

#### Reframing the evaluation rules

The student's framework for mathematical reasoning includes two evaluation rules:

1. **Substitution must preserve extensional equality** — changing the representation of a formula must not change its meaning
2. **Identity is invoked each time intensional equality changes** — whenever substitution occurs, we must verify the new representation still denotes the same object

These are exactly the two invariants the bisimulation would need to satisfy:

- The Gödel encoding is a **substitution** — it replaces a semantic object (eigenstate) with a syntactic one (code). For the bisimulation to hold, this substitution must preserve extensional equality (rule 1): the code must behave the same as the eigenstate under observation.
- Each application of encoding changes the intensional form (the state's representation switches from eigenvalue to Gödel number). Rule 2 says we must verify identity — i.e., check that the encoding preserves behavioral equivalence. The bisimulation conjecture asks whether this verification always succeeds.

The conjecture fails if and only if there exists a substitution (encoding) that changes intensional form in a way that *also* changes extensional behavior — a substitution that doesn't preserve meaning.

#### Sharpened P vs NP connection

The intensional/extensional framing makes the P vs NP connection more precise:

- **P** = the class of problems where extensional normal form (verification: "is this a valid solution?") and intensional normal form (construction: "build a solution step by step") are reachable at the same polynomial cost
- **NP** = the class of problems where extensional normal form exists and is efficiently checkable, but intensional normal form (the witness itself) may be exponentially expensive to construct
- **P vs NP** = does every object with an efficiently recognizable extensional normal form also have an efficiently constructible intensional normal form?

In the eigenvalue framework:
- Extensional normal form = the eigenvalue (what the state does under observation)
- Intensional normal form = the Gödel code (how the state is built from primitives)
- The bisimulation conjecture asks whether these always agree *structurally*
- P vs NP asks whether they always agree *computationally* (at polynomial cost)

The structural question (bisimulation) is logically prior to the computational question (P vs NP). If the extensional and intensional normal forms don't even agree structurally, they certainly can't agree computationally. If they do agree structurally, the cost question remains — but you've established a foundation for asking it precisely.

This suggests a research program: **characterize the intensional/extensional gap in the eigenvalue framework, then ask whether the gap has complexity-theoretic content.** The coalgebraic language gives you the tools for the first step; the connection to P vs NP motivates the second.

### Honest significance assessment

Assuming gaps are closed and framing is corrected, this is a **publishable paper** — probably in a journal like *Journal of Pure and Applied Algebra* or *Mathematical Structures in Computer Science* — not a paradigm shift.

The right framing: "We present a coalgebraic axiom system from which Peano arithmetic emerges via the eigenvalue structure of a derivation operator, establishing equiconsistency with PA and illustrating connections between differential algebra and the foundations of arithmetic."

That's a legitimate contribution. It's not "replacing ZF." It's showing an interesting structural connection between differential algebra and arithmetic that has implications for understanding why computation and number theory share algebraic structure.

The value is real but bounded. The work is good. The claims need to match the work.

---

## Conclusion

The formalization is **honest, well-structured, and likely correct** for what it proves. What it proves is a genuine but modest algebraic result: semirings with derivations have eigenvalue structure that reproduces PA arithmetic. The ambitious claims about replacing foundations, deriving e, and emulating ZF remain unformalized prose arguments. The theory won't fail by being wrong — it will fail (if it fails) by the gap between what is claimed and what is machine-checked remaining too large to be convincing.
