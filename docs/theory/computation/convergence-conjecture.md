# The Convergence Conjecture: Is There a Non-Divergent Variant?

## Date: 2026-02-21

## Summary

The encoding obstruction is proved: no injective encoding commutes with the Leibniz extensionalization (`no_coalgebra_morphism`), the intension/extension gap grows exponentially with each substitution step (`extensionalize_more_than_doubles`), and there is no fixed point (`substitution_chain_distinct`). The exact coalgebra morphism is impossible.

But the meaning is preserved at every level (`semantic_invariance_general`). The system isn't semantically diverging — only formally. This raises the central open question:

**Does there exist a weaker encoding — non-injective, approximate, or up to some equivalence — where the intension/extension switching converges?**

If yes: the obstruction has a boundary, and the boundary is the interesting object. Something like self-representation exists, just not the exact version. The system can approximately know itself.

If no: the divergence is total. No variant of self-representation — not even an approximate one — avoids the exponential gap. Self-knowledge is structurally impossible at every resolution.

---

## Part 1: What's Proved (The Exact Case)

The Lean formalization establishes three facts that together constitute the exact impossibility:

| Theorem | What it says | Lean name |
|---|---|---|
| **Universal obstruction** | For ALL injective ε and ALL terms a, b: ε(extensionalize) ≠ ε(original) | `no_coalgebra_morphism` |
| **Exponential divergence** | Each extensionalization more than doubles term size: size(rewritten) > 2 × size(original) | `extensionalize_more_than_doubles` |
| **No fixed point** | Three levels of extensionalization produce three distinct terms | `substitution_chain_distinct` |

And the crucial asymmetry:

| Theorem | What it says | Lean name |
|---|---|---|
| **Semantic invariance** | eval(original) = eval(extensionalized) for ALL terms, ALL models | `semantic_invariance_general` |

The gap is in the **form**, not the **content**. Naming (encoding) and unfolding (execution) disagree on syntax while agreeing on semantics. This is why the convergence question is well-posed: the semantic side already converges (it's invariant). The question is whether the syntactic side can be made to converge too, under a weaker notion of "encoding."

---

## Part 2: The Candidates

### Candidate 1: Encoding up to semantic equivalence

**Idea:** Quotient the term algebra by evaluation. Two terms get the same code if eval(t₁) = eval(t₂) in all models. Since `obsRewrite_eval` proves eval(obsRewrite(t)) = eval(t), the extensionalized and intensional forms would get the same code. The "encoding" commutes trivially.

**What it sacrifices:** Injectivity. Different terms with the same semantics get the same code. The encoding can no longer distinguish `obs(compose(f₁, f₁))` from `oplus(compose(f₁, f₁), compose(f₁, f₁))` — they mean the same thing, so they get the same name. You lose structural self-representation: the system can name its behaviors but not its syntax.

**What it keeps:** Arithmetic (eigenvalues still work) and the morphism (trivially, since the quotient absorbs the extensionalization).

**Assessment:** This is the degenerate case. The morphism "works" because you've defined away the gap. The system can't talk about its own structure — only its own behavior. This is like a programming language that can reflect on output types but not on source code. Useful, but not self-representation in the Gödel sense.

**Formal status:** Trivially achievable. Not interesting as a convergence result because there's nothing to converge — the quotient collapses the gap immediately.

---

### Candidate 2: Encoding of normal forms only

**Idea:** Only encode terms that are fully rewritten — terms in normal form where no obsRewrite can fire. The confluence result guarantees unique normal forms. Since obsRewrite doesn't apply to normal forms, the encoding trivially commutes (there's nothing to rewrite).

**What it sacrifices:** Self-execution. You can encode results but not processes. The term `obs(compose(f₁, f₁))` is not in normal form — it's a computation in progress. Its normal form is `oplus(compose(f₁, f₁), compose(f₁, f₁))` (after deep rewriting resolves all obs sub-terms). You can encode the answer but not the question.

**What it keeps:** Injectivity (normal forms are unique, so the encoding is injective on the normal-form fragment) and arithmetic.

**Assessment:** This gives you a "result-only" self-representation. The system can encode what things evaluate to, but not the process of evaluation. It can name answers but not questions. This corresponds to a model of computation where you can inspect final states but not intermediate steps — a purely declarative self-knowledge.

**Formal status:** The confluence + termination results (from confluence.md) guarantee normal forms exist and are reachable. The encoding on normal forms is well-defined and injective. What's lost is exactly the computational content — the ability to represent obs-in-progress.

**Open question:** Is the normal-form fragment expressive enough for Gödel encoding? Can you encode "this term reduces to that normal form" as a statement within the normal-form fragment? If yes, you get self-reference about results (a restricted incompleteness). If no, the fragment is too weak for interesting self-representation.

---

### Candidate 3: Bounded-depth approximate morphism

**Idea:** Define a family of encodings ε_k that commute with obsRewrite up to depth k. At depth 0, ε₀ is any injective encoding. At depth 1, ε₁ corrects for the first extensionalization. At depth k, ε_k corrects for k extensionalizations. The question is whether the sequence {ε_k} converges.

**What it sacrifices:** Exactness. Each ε_k is only approximately correct. The error at depth k+1 is the residual divergence that ε_k doesn't account for.

**What it keeps:** All three properties — approximately. The encoding is injective (at each finite depth), arithmetic works, and the morphism holds up to depth k.

**Assessment:** This is the most promising candidate and the most mathematically interesting. The question becomes:

**Does the approximation error shrink as k → ∞?**

If the error shrinks: there exists a limiting encoding ε_∞ that is an exact coalgebra morphism in the limit. The obstruction is a finite-depth phenomenon that vanishes at infinity. Self-representation is possible "in the limit."

If the error grows: the divergence is genuine at every scale. Each correction introduces more error than it fixes. Self-representation is impossible even approximately.

If the error oscillates or stabilizes: there's a non-trivial boundary between representable and non-representable structure.

**Connection to the discrete-continuous conjecture:** This is precisely the question from self-representation.md Part 10. The algebraic Δ_h (finite differences) and the computational Δ_step (ValidStep) are depth-k approximations to obs. The discrete-continuous conjecture asks whether Δ_h → obs as h → 0. In the bounded-depth framing, this becomes: does ε_k → ε_∞ as k → ∞?

**What convergence would mean:**
- e = lim(1 + 1/n)^n would be derived from self-reference — the discrete base 2 (from binary branching in the Leibniz rule) refined to the continuous base e as the depth limit is taken
- The analytic model (obs = d/dx) would be selected by the framework's own self-referential structure
- Self-representation would be possible in the continuum limit, even though it's impossible at any finite depth

**What divergence would mean:**
- The obstruction is total — no approximation scheme converges
- Self-knowledge is structurally impossible at every resolution
- The gap between naming and unfolding is irreducible, not just at the exact level but at every approximate level

**Formal status:** Not formalized. The definition of "bounded-depth approximate morphism" and "convergence of encoding sequences" would need precise formulation. This is the main open formalization target.

---

### Candidate 4: Non-positional encoding

**Idea:** Abandon positional representation entirely. Instead of encoding terms as natural numbers (which forces unique positional representation, which forces carry), encode them as objects in a different mathematical structure — lambda terms, categories, continuation-passing style, or some algebraic structure where addition is local or absent.

**What it sacrifices:** Ordering and decidability. The ⊕ impossibility (`oplus_bitwise_impossible`) blocks bitwise approaches. The carry propagation (`carry_propagation_general`) blocks any base-b positional approach. A non-positional encoding would need to avoid positional representation entirely.

**What it keeps:** Unclear. The question is whether a non-positional encoding can support enough structure for self-representation (Gödel decoding, bounded quantification, primitive recursive predicates) without reintroducing carry propagation through the back door.

**Assessment:** The most speculative candidate. Known non-positional representations:

| Representation | Addition | Ordering | Self-encoding? |
|---|---|---|---|
| Lambda encoding (Church numerals) | O(n) sequential application | Requires normalization | Possible but inefficient |
| Continuation-passing | Deferred computation | Non-obvious | Open |
| Categorical (initial algebra) | Fold/unfold | Structure-dependent | Open |
| p-adic integers | Carry propagates LEFT (finite) | Non-standard | Open |

The p-adic case is particularly interesting: in p-adic arithmetic, carry propagates in the opposite direction (toward higher digits) and terminates in finite steps for any given precision. The carry is still non-local but bounded. This might give a "bounded carry" version of arithmetic where the obstruction is finite rather than unbounded.

**Formal status:** Not formalized. Would require defining alternative term encodings and proving (or disproving) the morphism condition in each case.

---

## Part 3: The Convergence Conjecture

### Statement

**Conjecture (Convergence).** Define the *depth-k morphism error* as:

```
E_k(ε, t) = |ε(rewrite^k(obs(t))) - ε(obs(rewrite^k(t)))|
```

where rewrite^k denotes k-fold deep extensionalization. The conjecture asks:

**Does there exist a family of injective encodings {ε_k} such that E_k(ε_k, t) → 0 as k → ∞ for all terms t?**

If yes: self-representation converges in the limit. The exact obstruction (E_0 > 0 for all injective ε) is a finite-depth phenomenon.

If no: the obstruction is total. Self-representation diverges at every depth.

### What we know

**Against convergence:**
- `extensionalize_more_than_doubles`: each step more than doubles the term size. The syntactic complexity grows exponentially with depth.
- The exponential growth means the correction needed at each depth grows exponentially. For {ε_k} to converge, each ε_k must absorb an exponentially growing correction.
- In most natural encoding schemes, absorbing exponential growth requires exponential resources — which suggests the error grows rather than shrinks.

**For convergence:**
- `semantic_invariance_general`: the meaning is invariant at every depth. The semantic side has already converged (it's constant). If there exists an encoding that tracks semantics rather than syntax, it would converge trivially (Candidate 1).
- The discrete-continuous bridge: in the analytic model, finite differences converge to derivatives. The algebraic analogue might hold.
- Renormalization in physics: divergent perturbation series can sometimes be resummed via renormalization. The extensionalization chain might admit a similar resummation where the exponential divergence is absorbed into a redefinition of the encoding at each scale.

### The role of e

If convergence holds, the limiting encoding would be characterized by the rate at which the discrete (depth-k, base-2 from binary branching) approximation approaches the continuous (depth-∞) limit. This rate is governed by:

```
lim_{n→∞} (1 + 1/n)^n = e
```

The number e would emerge as the characteristic constant of convergent self-representation — the rate at which the intension/extension gap closes in the limit. In the analytic model, this is standard (finite differences → derivatives, eigenbase 2 at h=1 → eigenbase e at h→0). The conjecture would make this algebraic rather than analytic.

---

## Part 4: What Resolution Would Mean

### If convergence holds

1. **Self-representation is possible in the continuum limit.** The exact version fails (proved). The approximate version converges. The obstruction is a discretization artifact that vanishes at infinite depth.

2. **The analytic model is selected by self-reference.** The convergent encoding would force obs to act as a derivative (the unique operation whose eigenvalues are the natural numbers AND whose finite-depth approximations converge). The framework's own self-referential structure would select the analytic representation.

3. **e is derived from self-reference.** The Euler number would be the convergence rate of self-representing arithmetic — not an external constant but a structural invariant of the intension/extension gap.

4. **Compilation and execution are separate at finite depth but merge at infinity.** The von Neumann bottleneck would be a finite-depth phenomenon. In the limit, encoding and execution would coincide. This would have implications for the theoretical limits of computation.

### If convergence fails

1. **The obstruction is total.** No approximation scheme works. Self-representation diverges at every depth and every resolution.

2. **The intension/extension gap is irreducible at every scale.** Not just "naming can't catch substitution" but "naming can't even asymptotically approach substitution."

3. **Compilation and execution are fundamentally separate.** Not a finite-depth artifact but a structural theorem about the nature of formal systems. The von Neumann bottleneck is absolute.

4. **There is no bottom, at any resolution.** The perpetual switching between intension and extension never converges, not even in a limiting sense. Self-knowledge is structurally impossible.

### The honest assessment

The trajectory divergence (`extensionalize_more_than_doubles`) suggests divergence — each step more than doubles the complexity, so the corrections grow exponentially. For convergence, you'd need the encodings to absorb this exponential growth, which seems to require exponential resources at each depth.

But semantic invariance (`semantic_invariance_general`) shows the CONTENT converges trivially. The question is whether there's a middle ground between "exact syntactic match" (impossible) and "semantic quotient" (trivial) — an encoding that preserves more structure than behaviors but less than full syntax, and converges.

The renormalization analogy is suggestive: in QFT, perturbation series diverge term-by-term but can be resummed. The extensionalization chain diverges step-by-step but might be resummable. Whether this analogy has formal content is the open question.

---

## Part 5: Formalization Path

To make the conjecture precise and eventually provable/disprovable:

### Step 1: Define the approximation framework

```
-- Depth-k extensionalization
def iterDeepRewrite : ℕ → Term → Term
  | 0, t => t
  | k+1, t => deepRewrite (iterDeepRewrite k t)

-- Morphism error at depth k
def morphismError (ε : Term → ℕ) (t : Term) (k : ℕ) : ℕ :=
  -- Distance between the two paths through the diagram at depth k
  -- Path 1: extensionalize k times, then encode
  -- Path 2: encode, then ... (semantic side)
  sorry -- needs precise definition
```

### Step 2: Prove the error grows

Show that for any fixed injective ε, the morphism error grows with k:

```
-- Conjecture: error grows at least exponentially
theorem error_grows (ε : Term → ℕ) (hε : Injective ε) :
    ∀ k, morphismError ε (obs (compose f₁ f₁)) (k+1) >
         morphismError ε (obs (compose f₁ f₁)) k
```

### Step 3: Investigate whether adaptive encodings can compensate

The key question: can the ENCODING change with depth to absorb the growth?

```
-- A family of encodings, one per depth
def EncodingFamily := ℕ → (Term → ℕ)

-- Convergent family: error at depth k with encoding ε_k shrinks
def Converges (εs : EncodingFamily) (t : Term) : Prop :=
    ∀ bound, ∃ k₀, ∀ k ≥ k₀, morphismError (εs k) t k < bound
```

### Step 4: Prove or disprove convergence

Either:
- Construct a convergent family (proof of convergence)
- Prove no family converges (proof of total divergence)

**Expected difficulty:** The construction would likely require the analytic model and real analysis (limits, exponentials, Cauchy sequences). The refutation would require showing that the exponential growth of term size forces any encoding family to diverge. Both are substantial.

---

## Related

- [encoding-obstruction.md](encoding-obstruction.md) — The exact obstruction: intension/extension gap, trilemma
- [self-representation.md](self-representation.md) — Part 10: the original discrete-continuous conjecture
- [impossibility-hierarchy.md](impossibility-hierarchy.md) — The hierarchy: no bottom, perpetual switching
- [addition-non-locality.md](addition-non-locality.md) — The mechanism: carry propagation
- [observer-as-register.md](observer-as-register.md) — The interpretation: observer as mode-switching register
- [obstruction/README.md](obstruction/README.md) — The Lean formalization status
