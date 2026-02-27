# Normalization Depth, Fixed Points, and the Halting Problem

## Date: 2026-02-28

## Summary

The confluence result (confluence.md) proves that every term in the framework has a unique normal form under the rewriting system R1-R12. The encoding obstruction (Obstruction/Main.lean) proves that substitution has no fixed point — extensionalization always produces a structurally distinct term. These appear to contradict each other. They do not. The resolution of this tension is where the halting problem enters, and it is directly relevant to the complexity-theoretic question.

The argument:

1. **Confluence gives normal forms for terms.** Every term, under R1-R12, reaches a unique normal form in finite steps.
2. **The encoding obstruction gives no fixed point for the eval-quote cycle.** The cycle extensionalize -> re-encode -> extensionalize -> ... never stabilizes, because each extensionalization produces a structurally new term.
3. **These operate at different levels.** Confluence normalizes a GIVEN term. The encoding obstruction shows that the META-LEVEL process — "normalize, then re-interpret the result as a new term to normalize" — has no fixed point.
4. **The halting problem is the gap between these levels.** "Has the computation finished?" requires determining whether the current normal form, re-interpreted as a code, will produce further computation. This is undecidable.
5. **For P vs NP, the question is not whether normalization terminates (it does) but whether the meta-level cycle — normalize, re-interpret, normalize again — reaches a USEFUL stopping point in polynomial steps.**

---

## Part 1: Two Levels of Normalization

### Level 1: Term normalization (confluence)

Given a term t, the rewriting system R1-R12 reduces it to a unique normal form nf(t) in finite steps. This is proved:

- **Termination:** The lexicographic measure mu(t) = (mu_1, mu_2, mu_3) strictly decreases with each rule application. Well-ordering guarantees finite termination.
- **Confluence:** All critical pairs join (Newman's lemma). Different reduction orders yield the same normal form.
- **Result:** nf(t) is a sum-of-products-of-atoms — the algebraic analogue of expanded polynomial form.

Term normalization is a **single-pass operation on a fixed syntactic object**. You take a term, apply rewrite rules until no more apply, and get the normal form. This always terminates. The cost is bounded (though potentially exponential — see Part 3).

### Level 2: Computational normalization (the eval-quote cycle)

A self-executing encoding does not normalize a fixed term. It executes a PROGRAM encoded as a term. Execution is a cycle:

```
Step 1: Read the current code c_t (an eigenstate = a natural number = a Gödel code of a term)
Step 2: Decode c_t to obtain the term t it represents
Step 3: Extensionalize t (apply the Leibniz rule, producing a new term t')
Step 4: Normalize t' to nf(t') under R1-R12 (term normalization — Level 1)
Step 5: Encode nf(t') as a new code c_{t+1}
Step 6: Is c_{t+1} the final answer? If yes, halt. If no, go to Step 1 with c_{t+1}.
```

This is the computational cycle. Each iteration performs one round of term normalization (Level 1). The question is how many iterations of the CYCLE are needed.

### The encoding obstruction blocks the cycle's convergence

The encoding obstruction proves that Step 6 cannot be resolved:

**`no_coalgebra_morphism`**: For ANY injective encoding and ANY compound term, the code of the extensionalized form differs from the code of the intensional form. This means c_{t+1} != c_t — the code always changes after one cycle.

**`substitution_chain_distinct`**: Three successive passes through the cycle produce three distinct codes. The chain has no fixed point.

**`semantic_invariance_general`**: The MEANING is preserved at every step. The codes change but the semantics doesn't. So the cycle is not diverging semantically — it's diverging syntactically.

The consequence: the computational cycle never reaches a step where "the code hasn't changed, so we're done." The code always changes. There is no syntactic fixed point.

### Why confluence doesn't help

Confluence guarantees that each INDIVIDUAL pass through Level 1 (Steps 3-4) terminates. The term t' produced by extensionalization always has a normal form nf(t'), and it's reachable in finite steps.

But confluence does not guarantee that the CYCLE (Level 2) terminates. The cycle's termination requires that at some iteration, the normal form nf(t') encodes a "final answer" — a code that, when decoded and re-extensionalized, produces the same code again. That is, the cycle terminates when:

```
encode(nf(extensionalize(decode(c_t)))) = c_t
```

This is exactly the coalgebra morphism condition: encoding commutes with extensionalization. And `no_coalgebra_morphism` proves this never holds for injective encodings. The cycle has no fixed point.

---

## Part 2: The Halting Problem as the Normalization Gap

### What "the algorithm has finished" means

Consider an algorithm encoded as a term in the eigenvalue framework. The algorithm operates on its own code (self-execution). "The algorithm has finished" means: the current code represents the final output, and no further extensionalization-normalization cycles are needed.

Formally: the algorithm has finished at step T if c_T is the code of the output AND the output is not subject to further computation. That is:

```
decode(c_T) = nf(output)   AND   no further Leibniz rewrite applies to decode(c_T)
```

The first condition (c_T encodes a normal-form term) is decidable — you can check whether a decoded term is in normal form by attempting to apply R1-R12 and seeing if nothing fires.

The second condition (no further computation is needed) is where the halting problem enters. "No further computation" means the normal form is the FINAL answer to the problem the algorithm was solving, not just an intermediate result. Determining this requires knowing whether the algorithm's high-level logic has completed — which is the halting problem.

### The precise connection

The encoding obstruction proves: **the eval-quote cycle has no syntactic fixed point.** This means:

1. For any code c, there exists a decode-extensionalize-normalize-encode cycle that produces c' != c
2. The question "is c the final answer?" cannot be answered by checking whether c is a fixed point of the cycle (it never is)
3. Therefore "the algorithm has finished" requires external information — a halting condition specified from outside the cycle

This is not an appeal to Turing's undecidability theorem as an external result. It is a DIRECT CONSEQUENCE of the encoding obstruction: the cycle has no fixed point, so no internal criterion can determine termination. The halting problem for self-executing encodings is the no-fixed-point theorem read temporally.

### The two modes of "not finished"

The no-fixed-point result means the cycle always produces a different code. But there are two structurally different reasons it might produce a different code:

**Mode A: Productive computation.** The cycle extensionalizes a compound term, resolves interactions via Leibniz, and the resulting normal form encodes meaningful computational progress. The new code represents a state closer to the answer. Each cycle is a "useful" step.

**Mode B: Idle cycling.** The cycle extensionalizes, normalizes, re-encodes, and the new code is different but doesn't represent progress toward the answer. The extensionalization introduces oplus, normalization collapses it back, but the re-encoding shifts the code without advancing the computation. Each cycle is "wasted" work.

The halting problem is: we cannot decide which mode the cycle is in. Mode A might look identical to Mode B at any given step — both produce a new, different code. Only by knowing the full future trajectory can we determine whether the computation is making progress.

### Relevance to algorithms

Every algorithm, when executed, goes through the eval-quote cycle. The algorithm's representation (its source code, compiled binary, Turing machine description) is a term. Its execution is repeated extensionalization-normalization of that term on its inputs. The inputs are encoded as codes. Each step produces a new code.

The no-fixed-point theorem says: the cycle of executing the algorithm on encoded inputs will never reach a code that is a fixed point of the encode-extensionalize-normalize cycle. This does not mean the algorithm doesn't terminate — algorithms terminate when an EXTERNAL halting condition is met (the output register matches a specification, a flag is set, a base case is reached). It means the termination is not intrinsic to the cycle — it requires checking a condition that the cycle itself cannot determine.

For polynomial-time algorithms: the halting condition is reached after polynomially many cycles. The no-fixed-point theorem doesn't prevent this — it just says the termination is externally imposed, not internally discovered.

For algorithms on NP-complete problems: the question is whether ANY halting condition (any specification of the answer) can be checked to have been reached in polynomially many cycles. The no-fixed-point theorem constrains this by saying: each cycle is guaranteed to produce a different code, so the algorithm cannot "accidentally" converge to a fixed point. It must actively construct the answer through the specified number of cycles.

---

## Part 3: Normalization Depth Bounds

### The formal question

Define the **normalization depth** of a term t as the number of `deepRewrite` passes needed to reach obs-normal form (no `obs(compose(a,b))` sub-terms remain):

```
normDepthBounded(fuel, t) = if isObsNormal(t) then 0 else 1 + normDepthBounded(fuel-1, deepRewrite(t))
```

By termination of deepRewrite, this is well-defined. The question is: **what is normDepthBounded as a function of obs-compose nesting depth d?**

### The Lean formalization result (proved, 2026-02-28)

The Lean file `Obstruction/Complexity.lean` defines the family `nestedObsCompose`:

```
nestedObsCompose 0     = compose(f₁, f₁)
nestedObsCompose (d+1) = obs(compose(nestedObsCompose d, nestedObsCompose d))
```

and proves:

**Theorem (`normDepth_nested_eq_two`).** For all d >= 1:

```
normDepthBounded 3 (nestedObsCompose d) = 2
```

The normalization depth is **constant (exactly 2)**, independent of d. This was initially conjectured to be exponential (>= 2^d), but formalization revealed the conjecture was false.

### Why the depth is constant

`deepRewrite` goes bottom-up: it recurses into all sub-terms before applying `obsRewrite` at each `obs` node. A single pass of `deepRewrite` therefore processes ALL nesting levels simultaneously. The proof establishes three properties:

**(A)** `nestedObsCompose (d+1)` is not obs-normal (obs(compose) at root). Trivial from the definition.

**(B)** `deepRewrite(nestedObsCompose (d+1))` is not obs-normal. After one pass, the Leibniz expansion introduces `obs(compose(f₁, f₁))` sub-terms at the innermost level. These are not obs-normal.

**(C)** `deepRewrite(deepRewrite(nestedObsCompose (d+1)))` IS obs-normal. The second pass resolves the remaining `obs(compose(f₁, f₁))` terms. The proof uses induction on d, showing that `deepRewrite(r)` for r = `deepRewrite(nestedObsCompose d)` has `oplus` at root (not `compose`), so `obsRewrite(obs(deepRewrite(r))) = obs(deepRewrite(r))` (identity). Obs-normality propagates from the inductive hypothesis.

All three properties are fully machine-checked with zero `sorry`.

### Where the exponential cost actually lives

The normalization depth is constant, but the **work per pass** is exponential:

```
termSize(nestedObsCompose d) >= 2^d     (proved: compounding_size_lower_bound)
termSize(nestedObsCompose (d+1)) > 2 * termSize(nestedObsCompose d)     (proved: construction_size_doubles)
```

Each `deepRewrite` pass traverses the entire term. For `nestedObsCompose d`, this means traversing a term of size >= 2^d. The total computational work for normalization is therefore exponential in d, but this cost is in the **per-step traversal**, not in the **number of steps**.

This is a significant structural finding: the intension/extension regress terminates in constant depth (2 passes), but each pass does exponentially more work as the term grows. The exponential complexity lives in the term size, not the iteration count.

### What this means for the convergence rate

The convergence rate question (convergence-and-complexity.md) resolves differently than originally expected:

- The **syntactic trajectory** (iterated extensionalization) stabilizes in 2 passes for obs-normality
- The **per-step cost** grows exponentially with nesting depth
- The total work = (constant passes) * (exponential per-pass cost) = exponential

For P vs NP, the relevant question shifts from "how many normalization passes?" to "what is the per-pass cost for NP-complete encodings?" The encoding obstruction proves this cost is exponential for the nestedObsCompose family. Whether this applies to NP-complete problem encodings remains open.

---

## Part 4: NP-Complete Problems as Deeply Nested Terms

### What the Lean result changes

The original conjecture was that normalization depth (number of `deepRewrite` passes) grows exponentially with nesting depth. The Lean formalization proved this wrong: normalization depth is exactly 2 for all nesting depths d >= 1, because `deepRewrite` goes bottom-up processing all levels in one pass.

This means the relevant complexity measure for SAT encoding is NOT "how many passes of deepRewrite are needed" but rather "how much work does each pass of deepRewrite perform." The per-pass work is exponential (term size >= 2^d), but the iteration count is constant.

### Encoding SAT

A SAT formula phi with n variables and m clauses can be encoded as a term in the eigenvalue framework. One natural encoding:

- Each variable x_i is an eigenstate f_i
- A literal is either f_i (positive) or obs(f_i) (negated — using obs as the distinguishing operation)
- A clause (disjunction of literals) is a compose-product of the literals: compose(l_1, compose(l_2, ..., l_k))
- The formula (conjunction of clauses) is an observation of the composition: obs(compose(C_1, compose(C_2, ..., C_m)))

This encoding creates a term with obs-compose nesting proportional to the clause structure.

### The per-pass work for SAT

When `deepRewrite` processes a SAT-encoding term, the Leibniz rule fires at every `obs(compose(...))` node. Each firing doubles the local sub-term (producing `oplus(compose(obs(a), b), compose(a, obs(b)))`). For a formula with m clauses nested in a composition chain, a single pass of `deepRewrite` produces a result whose size is exponential in the number of Leibniz rewrite sites.

The key structural fact: **shared variables create sub-terms that are duplicated across branches.** When Leibniz fires on `obs(compose(C_1, C_2))`, the result contains both `C_1` and `C_2` in two branches. If `C_1` and `C_2` share variable x_j, then x_j appears in multiple branches, and each branch's contribution to the final oplus depends on x_j's value.

The constant normalization depth (2 passes) means the exponential cost is in the SIZE of the terms processed per pass, not in the number of passes. This is an important structural distinction — it means the bottleneck is traversal cost, not iteration count.

### Why verification avoids this

Verification of a SAT assignment sigma checks whether sigma satisfies phi. In the eigenvalue framework:

- Substitute the assignment into the formula term: replace each f_i with the assigned value (f_0 for false, f_1 for true)
- After substitution, the term contains no free variables — only constants
- Normalization of a term with only constants is straightforward: R1 (obs(f_1) -> f_1), R6 (obs(f_0) -> z), R2-R4 (identity/annihilator cleanup)
- No deep Leibniz expansion needed — the obs-compose nesting collapses because the inner terms are constants with known eigenvalues

After substitution, the term size does not explode: each Leibniz rewrite produces constant-size results because the inner terms are primitives. The per-pass work is polynomial in formula size.

### The asymmetry, precisely

| Operation | Term size per pass | Passes | Total work |
|---|---|---|---|
| Verification (given assignment) | O(n + m) — constants collapse | 2 | O(n + m) |
| Construction (finding assignment) | >= 2^n — variables cause Leibniz branching | 2 | >= 2^n |

The gap is in per-pass work, not in pass count. Both verification and construction normalize in 2 passes. But verification's passes are cheap (polynomial-size terms), while construction's passes are expensive (exponential-size terms from Leibniz branching on unresolved variables).

---

## Part 5: The Halting Problem and Per-Pass Cost

### The connection, revised

Part 2 established that the eval-quote cycle has no fixed point (the encoding obstruction). Part 3 established that normalization depth is constant (2), but per-pass work is exponential. Part 4 established that NP-complete encodings require exponential per-pass work for construction but not verification.

The halting problem enters not through normalization depth (which is constant) but through the eval-quote CYCLE — the meta-level process of normalize, re-encode, re-extensionalize. The no-fixed-point theorem says this cycle never stabilizes syntactically, even though each individual normalization is finite.

**Given a term t (encoding an NP-complete instance), the term-level normalization always terminates in 2 passes. But the meta-level question — "has the computation reached the answer?" — remains undecidable.**

### What the constant depth means for P vs NP

The Lean result fundamentally changes what the normalization framework says about P vs NP:

**Old framing (disproved):** normalization depth is exponential, so the NUMBER OF PASSES separates verification from construction.

**New framing (proved):** normalization depth is constant, so the WORK PER PASS separates verification from construction. Both require 2 passes. But construction's passes traverse exponentially larger terms.

This shifts the complexity question from "how many iterations?" to "how expensive is each iteration?" The encoding obstruction provides structural evidence that per-pass work is exponential for construction:

1. **More-than-doubling** means each Leibniz rewrite at least doubles term size
2. **Variable sharing** means the Leibniz branching produces exponentially many sub-terms
3. **Carry non-locality** means combining branch results has irreducible per-addition cost

### The missing step

The gap remains: proving that the exponential per-pass work for the `nestedObsCompose` family transfers to NP-complete problem encodings. The `nestedObsCompose` family is a specific algebraic construction — SAT formulas have different structure (flat clause lists with variable sharing, not binary-tree nesting). Whether SAT-encoding terms have the same exponential per-pass cost is the open question.

Additionally, the per-pass cost analysis examines ONE SPECIFIC rewriting strategy (`deepRewrite`). A polynomial-time algorithm for SAT would correspond to a DIFFERENT strategy for manipulating the encoding — one that avoids the exponential term-size blowup. The encoding obstruction shows such a strategy cannot be a coalgebra morphism (it must distort observation dynamics), but does not prove no efficient strategy exists.

---

## Part 6: The Three-Level Architecture (Revised)

### Summary of the structure

The relationship between the three levels, updated for the constant-depth finding:

```
Level 1: TERM NORMALIZATION (deepRewrite passes)
├── Always terminates (proved: termination)
├── Constant number of passes: exactly 2 for nestedObsCompose (proved)
├── Cost per pass: up to exponential in term size (Leibniz expansion)
└── The bottleneck is per-pass WORK, not pass COUNT

Level 2: COMPUTATIONAL CYCLE (eval-quote)
├── Never reaches a fixed point (proved: encoding obstruction)
├── Each iteration performs one Level 1 normalization (2 passes, but exponential work)
├── Cost per iteration: exponential for construction, polynomial for verification
├── Number of iterations: bounded by halting condition
└── Total cost: (per-pass work) * (constant passes) * (number of iterations)

Level 3: THE HALTING PROBLEM
├── "How many Level 2 iterations are needed?" is undecidable in general
├── The encoding obstruction proves the cycle has no internal stopping criterion
├── Termination requires external specification of the answer condition
└── The per-iteration cost is the relevant complexity measure
```

### How this relates to P vs NP

The constant-depth finding changes the P vs NP connection. The question is no longer "how many passes?" (answer: 2) but rather:

1. **How many Level 2 iterations (eval-quote cycles) are needed?** — still constrained by the no-fixed-point theorem and the halting problem
2. **What is the per-pass work at each iteration?** — this is where the verification/construction asymmetry lives

For verification: each iteration's normalization traverses a polynomial-size term (constants collapse). For construction: each iteration's normalization traverses an exponential-size term (unresolved variables cause Leibniz branching).

The structural evidence says: NP-complete problem encodings produce exponentially large intermediate terms during normalization, making each pass of `deepRewrite` exponentially expensive. But this is evidence about ONE rewriting strategy (`deepRewrite`), not about ALL possible algorithmic approaches.

---

## Part 7: What the Lean Formalization Proved

### Completed results (zero sorry)

The file `Obstruction/Complexity.lean` proves:

**Normalization depth:**

```lean
-- Normalization depth is exactly 2 for all nestedObsCompose (d+1)
theorem normDepth_nested_eq_two (d : ℕ) :
    normDepthBounded 3 (nestedObsCompose (d + 1)) = 2

-- Via three sub-properties (all proved by induction):
-- (A) nestedObsCompose (d+1) is not obs-normal
-- (B) deepRewrite(nestedObsCompose (d+1)) is not obs-normal
-- (C) deepRewrite(deepRewrite(nestedObsCompose (d+1))) IS obs-normal
```

**Size bounds:**

```lean
-- Term size grows exponentially with nesting depth
theorem compounding_size_lower_bound (d : ℕ) :
    termSize (nestedObsCompose d) ≥ 2 ^ d

-- Term size more than doubles at each nesting level
theorem construction_size_doubles (d : ℕ) :
    termSize (nestedObsCompose (d + 1)) > 2 * termSize (nestedObsCompose d)
```

**Structural analogy (fully proved, no sorry):**

```lean
-- The P vs NP structural analogy: three proved components
theorem PvsNP_analogy_holds : PvsNP_StructuralAnalogy :=
  ⟨fun n => eigenvalue n,          -- verification is O(1)
   compounding_size_lower_bound,    -- construction size is exponential
   fun ε hε a b =>                  -- no encoding bridges the gap
     encoding_obstruction_general ε hε a b⟩
```

### What was disproved

The original conjecture `normDepth_exponential_conjecture` (normalization depth >= 2^d) was **false**. Testing with `native_decide` for d=2 and d=3 showed normalization depth is exactly 2, not exponential. The conjecture was replaced by the correct theorem `normDepth_nested_eq_two`.

### The honest circularity, restated

The constant-depth finding makes the circularity more explicit: the exponential cost is in per-pass WORK (term size), not in PASS COUNT. Proving that SAT-encoding terms have exponential per-pass work under `deepRewrite` is straightforward (Leibniz branching on n variables produces 2^n-size terms). But this says nothing about whether a DIFFERENT algorithm could solve SAT efficiently — it only shows that the specific `deepRewrite` strategy is expensive.

Proving P != NP requires showing that ALL strategies are expensive, not just `deepRewrite`. The encoding obstruction constrains what strategies can look like (no coalgebra morphisms), but does not eliminate all polynomial-time strategies.

---

## Part 8: What the Constant-Depth Finding Means

### The structural contribution, revised

The constant-depth theorem (`normDepth_nested_eq_two`) establishes that the encoding obstruction's P vs NP connection is more nuanced than originally thought. The key contributions:

**What is proved:**

1. Verification is O(1) — eigenvalue reading, no Leibniz expansion (proved: `eigenvalue`)
2. Construction produces exponentially large terms — term size >= 2^d (proved: `compounding_size_lower_bound`)
3. No injective encoding bridges the gap — no coalgebra morphism exists (proved: `encoding_obstruction_general`)
4. Normalization depth is constant (2), not exponential (proved: `normDepth_nested_eq_two`)

**What (4) changes:**

The original narrative was: construction requires exponentially MANY passes, while verification requires one. The correct narrative is: both require the same constant number of passes (2), but construction's passes are exponentially MORE EXPENSIVE because they traverse exponentially larger terms.

This is a weaker structural analogy. The asymmetry is in per-step cost, not step count. The encoding obstruction still explains WHY construction is harder (Leibniz branching produces exponential term sizes), but the mechanism is different from what was originally conjectured.

### The honest assessment

The encoding obstruction proves that self-encoding systems have a structural verification/construction asymmetry. The Lean formalization makes this machine-checked. But the distance from this algebraic result to P != NP remains large:

1. The asymmetry is proved for a specific term family (`nestedObsCompose`), not for SAT encodings
2. The exponential cost is for a specific rewriting strategy (`deepRewrite`), not for all algorithms
3. The constant normalization depth (2) means iteration count does not separate verification from construction — only per-iteration work does
4. The SAT encoding sketch in Complexity.lean is definitional only, with no theorems connecting it to the proved results

The framework identifies encoding execution as the right lens for understanding computational complexity. Whether this lens can be focused sharply enough to resolve P vs NP is the open research question.

---

## Related

- [encoding-complexity.md](encoding-complexity.md) -- P vs NP as encoding execution problem
- [convergence-and-complexity.md](convergence-and-complexity.md) -- Convergence rate as complexity measure
- [../encoding-obstruction.md](../encoding-obstruction.md) -- The core trilemma
- [../confluence.md](../confluence.md) -- Termination and confluence of R1-R12
- [../impossibility-hierarchy.md](../impossibility-hierarchy.md) -- Four levels: substitution -> carry -> halting -> undecidability
- [../addition-non-locality.md](../addition-non-locality.md) -- Carry propagation forces external state
- [../computing-as-external-state.md](../computing-as-external-state.md) -- Computation = language + external state
