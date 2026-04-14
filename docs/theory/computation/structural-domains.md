# Structural Domains of Mathematical Language

## Date: 2026-04-14

## Summary

The encoding obstruction program has established two structural domains:

1. **Term algebras** (syntax) -- what mathematical expressions look like
2. **Rewrite rules** (dynamics) -- how expressions transform during evaluation

The obstruction lives at their intersection: evaluation changes syntactic form while preserving semantic content, and no injective encoding commutes with this process (`Universal.lean`, `EvalRewrite.lean`).

But mathematical language has more structure than these two. Three additional domains are directly relevant to the program -- each offers a sharper mechanism for WHY the obstruction holds and a concrete path to the open problems (#33, #34, #35, #36):

- **Binding and substitution** -- the actual mechanism of self-reference
- **Cut elimination** -- evaluation at the level of proofs, with proved exponential blowup
- **Curry-Howard** -- the identification of proofs with programs, giving a direct path from halting to proof complexity

This document articulates each domain's structural role and its connection to the obstruction program.

---

## Part 1: Binding and Substitution

### The mechanism of self-reference

The diagonal lemma (`Diagonal.lean`) uses substitution as its core operation. The Godel sentence construction is `subst(phi, fcode(phi))` -- plugging a formula's own code into itself. The `GodelSystem` structure has `subst : Formula -> N -> Sentence` as an axiomatized primitive.

But we have not analyzed WHY substitution creates the obstruction. The current proof says: `subst(phi, fcode(phi))` produces a sentence, which is a different syntactic category than `phi` (a formula). Different category -> different root constructor -> different code -> obstruction.

This is correct but shallow. A deeper question: **why does substitution necessarily change form?**

### The binding structure

The theory of binding gives multiple accounts of substitution:

| Framework | Representation | What substitution does |
|-----------|---------------|------------------------|
| de Bruijn indices | Variables as nameless natural numbers | Decrements indices, shifts free variables |
| Nominal sets | Names with alpha-equivalence | Renames to avoid capture |
| Higher-order abstract syntax (HOAS) | Variables as meta-level functions | Beta reduction in meta-language |
| Locally nameless | Free names + bound indices | Switches between name and index views |

Each framework reveals a different aspect of substitution. Common to all: **substitution changes the term's internal structure in a way that depends on the term being substituted AND the binding context**. You cannot substitute without examining the term's structure. You cannot examine structure without changing the abstract "shape" of the whole.

### The conjecture

**Any faithful theory of binding makes substitution a form-changing operation.** This is stronger than "there exists some substitution that changes form" -- it says binding structure ITSELF forces the obstruction, regardless of which representation you choose.

If provable, this would deepen the obstruction: not "evaluation happens to change form in this example" but "evaluation IS form change, via the binding structure that any formal system must have."

### Relevance to the program

**Issue #34 (root constructor change vs generic non-trivial semantics):** the binding structure is WHERE the root constructor change comes from. The root change isn't an accident of how we wrote the term algebra -- it's forced by how binding interacts with substitution. Formalizing this would sharpen the paper's central distinction.

**Issue #35 (GodelSystem for PA):** the binding structure is most of the work. If you formalize substitution correctly, representability of the diagonal function follows (the diagonal function IS the self-substitution function). Getting binding right is the hard part of instantiating GodelSystem for any specific theory.

### Where to look

The project already has `Lambda/Expr.lean` with substitution for lambda terms. Extending this with explicit binding analysis and connecting it to the term algebra framework in `Universal.lean` would be the natural next step.

---

## Part 2: Cut Elimination

### Evaluation at the level of proofs

Sequent calculus proofs have an internal structure: axioms, logical rules, and a special "cut" rule that allows using intermediate lemmas. Cut elimination is a rewrite system that transforms proofs WITH cuts into cut-free proofs.

Cut elimination has all the features of an `EvalRewriteWitness`:

- **Form changes:** a cut-containing proof has different structure than a cut-free proof
- **Semantics preserved:** the theorem proved is the same
- **Trajectory divergence:** the cut-free proof can be **exponentially or even non-elementarily longer** than the original (Statman 1979, Orevkov 1979)

The Gentzen Hauptsatz (cut elimination theorem) says cut elimination always terminates. Statman showed the termination takes non-elementary time in the worst case -- meaning the cut-free proof can be iterated-exponentially longer than the proof with cuts.

### The obstruction at proof level

Cut elimination IS the encoding obstruction applied to proof terms:

- Cuts are INTENSIONAL: they compress the proof by naming intermediate results (lemmas)
- Cut-free proofs are EXTENSIONAL: everything is unfolded, every inference step explicit
- Cut elimination is EXTENSIONALIZATION of proofs

This is literally the intension/extension gap applied to proof structure. Reducing a cut is substituting a proof of a lemma into every use site -- the same self-substitution mechanism that creates the obstruction.

### The exponential blowup IS the trajectory divergence

In `Universal.lean`, the `leibniz_more_than_doubles` theorem shows that extensionalization more than doubles term size. Iterated extensionalization grows at least as 2^k.

The Statman-Orevkov cut elimination lower bound shows cut-free proofs can be non-elementarily longer than proofs with cuts. This is the proof-theoretic analogue of the trajectory divergence theorem.

**The concrete target:** formalize cut elimination as an `EvalRewriteWitness` and derive the exponential (or super-exponential) blowup from the obstruction framework. If this works, the encoding obstruction has proof-complexity teeth -- the same structural fact that causes incompleteness also causes proof blowup.

### Relevance to the program

**Issue #33 (encoding obstruction -> proof complexity lower bounds):** cut elimination is the direct path. The blowup is a KNOWN result (Statman 1979). Connecting it to the obstruction would be the concrete demonstration that the obstruction yields complexity lower bounds.

**The paper (ITP/CPP):** cut elimination as an instance of `EvalRewriteWitness`, with the blowup as a consequence, would be a major technical contribution. It would show the obstruction framework captures a well-known proof-theoretic result as a special case.

### Where to look

The Lambda directory has beta reduction, which is cut elimination via Curry-Howard (see Part 3). Formalizing the explicit connection -- showing that `leibniz_more_than_doubles` on lambda terms corresponds to proof size growth under cut elimination -- is the bridge.

---

## Part 3: Curry-Howard (Proofs as Programs)

### The identification

The Curry-Howard correspondence says:

| Logic | Programming |
|-------|-------------|
| Propositions | Types |
| Proofs | Programs (terms) |
| Implication | Function types |
| Conjunction | Product types |
| Disjunction | Sum types |
| Cut | Beta redex |
| Cut elimination | Beta reduction |
| Proof normalization | Program evaluation |

This is not an analogy. It is an ISOMORPHISM. A proof IS a program. Proof normalization IS program evaluation.

### The direct path from halting to proof complexity

`Halting.lean` proves: the halting problem is an `EvalRewriteWitness`. Program execution changes form while preserving semantics, and no halting decider can commute with execution.

Via Curry-Howard:
- Programs = proofs (lambda terms = typed proof terms)
- Execution = cut elimination (beta reduction = proof normalization)
- Halting = normalization (program termination = proof reaching cut-free form)

Therefore: **the halting problem IS the problem of determining whether a proof normalizes.**

This collapses a conceptual distance. The encoding obstruction on program execution IS the encoding obstruction on proof normalization. They are the same obstruction via Curry-Howard -- not two instances of a common pattern, but literally the same theorem applied to two descriptions of the same objects.

### Why this matters for issue #36

Issue #36 asks: "prove that proof system verification requires arithmetic and therefore has `EvalRewriteWitness`."

The Curry-Howard route makes this cleaner. Via the correspondence:

- Proof verification = type checking (for typed proof terms) + normalization (for checking proofs reduce to the claimed theorem)
- Type checking is decidable (for standard systems) but normalization is not
- The undecidability of normalization IS the halting problem
- `Halting.lean` already proves the halting problem is an `EvalRewriteWitness`

So: proof verification involves normalization, normalization is an `EvalRewriteWitness`, therefore proof verification has the obstruction. No need to separately argue "verification requires arithmetic" -- it's built into the Curry-Howard identification.

### The typed vs untyped distinction

For Curry-Howard to make normalization equivalent to computation, we need typed lambda calculus. In simply-typed lambda calculus, all programs terminate (strong normalization theorem). So the halting problem doesn't apply -- every proof normalizes.

But in dependent type theory (Lean, Agda, Coq), and in second-order logic and beyond, normalization CAN be non-terminating in the general case, OR can have non-elementary length (Statman). The obstruction applies.

The precise claim: **the encoding obstruction applies to any type theory expressive enough to encode arithmetic (which is any theory capable of self-reference).** This matches the video's mutual interpretability result: self-reference requires arithmetic, arithmetic requires the obstruction.

### Relevance to the program

**Issue #36 (proof systems require arithmetic):** Curry-Howard gives a direct argument. Proof verification involves checking normalization. Normalization in any sufficiently expressive system is computation. Computation has the obstruction (halting problem). Therefore proof verification has the obstruction.

**Issue #33 (obstruction -> proof complexity):** Curry-Howard connects proof complexity to program complexity. Proof length corresponds to program size. Super-polynomial proof length corresponds to super-polynomial program descriptions of polynomial-time algorithms. The encoding obstruction on programs might translate to the encoding obstruction on proofs directly.

**The unified picture:** the obstruction applies to
- **Term algebras** (Universal.lean): syntactic form
- **Arithmetic evaluation** (EvalRewrite.lean): PA's own rules
- **Diagonal construction** (Diagonal.lean): self-reference via substitution
- **Program execution** (Halting.lean): computation over time
- **Proof normalization** (conjectured, via Curry-Howard): cut elimination

All five are instances of the same `EvalRewriteWitness` pattern, applied to different aspects of mathematical activity.

### Where to look

The Lambda directory has lambda calculus formalization. Extending this to typed terms with normalization, then identifying normalization as `EvalRewriteWitness`, completes the Curry-Howard bridge.

---

## Part 4: The Unified Landscape

### Five instances of the obstruction

| Domain | What the obstruction says | Lean file |
|--------|---------------------------|-----------|
| Term algebras | Leibniz rewrite changes root constructor | `Universal.lean` |
| PA arithmetic | Multiplication evaluation introduces addition | `EvalRewrite.lean` |
| Self-reference | Substitution creates diagonal, incompleteness follows | `Diagonal.lean` |
| Computation | Execution changes program state, halting undecidable | `Halting.lean` |
| Proof normalization | Cut elimination changes proof structure, blowup follows | Open (via Curry-Howard) |

Each is a reading of the same structural fact: **form changes, meaning is preserved, encoding cannot commute**.

### The common mechanism: self-substitution

Every instance involves a term being applied to (or substituted with) its own representation:

- Diagonal lemma: `subst(phi, fcode(phi))` -- formula applied to its own code
- Halting problem: `D(code(D))` -- program applied to its own code
- Cut elimination: proof of lemma substituted INTO proof using lemma (at every use site)
- Recursive definitions: function defined in terms of itself

Self-substitution IS the mechanism. The encoding obstruction IS why self-substitution cannot be tracked by any injective encoding.

### The three additional domains

The three domains in this document (binding, cut elimination, Curry-Howard) are not new applications of the obstruction -- they are deeper mechanisms for WHY the existing applications hold:

- **Binding** explains why substitution changes form (not "it just happens to" but "binding structure forces it")
- **Cut elimination** gives a concrete proof-theoretic instance with proved exponential blowup
- **Curry-Howard** collapses the conceptual distance between program halting and proof normalization

Together, they suggest the next phase of the program:

1. **Formalize binding structure** -- deepen the foundation for why substitution changes form (issue #34)
2. **Formalize cut elimination** as `EvalRewriteWitness` -- concrete proof-theoretic instance (issue #33)
3. **Formalize Curry-Howard bridge** -- connect halting to proof normalization directly (issue #36)

### The paper's scope

The current work (Universal.lean, EvalRewrite.lean, Diagonal.lean, Halting.lean, Incompleteness.lean) is sufficient for an ITP/CPP paper on the universal encoding obstruction. The three domains in this document would be extensions -- either follow-up papers or expanded sections.

Suggested order:
1. **Paper 1 (current):** the universal encoding obstruction unifies incompleteness and halting
2. **Paper 2 (after issue #33):** the obstruction implies proof complexity lower bounds (via cut elimination)
3. **Paper 3 (after issue #36):** proof systems have the obstruction universally (via Curry-Howard)
4. **Paper 4 (aspirational):** P vs NP independence from the obstruction framework

Each paper is independently valuable. Each builds on the previous. The full program spans years, not months. But the path is identifiable, which is rare for work touching P vs NP.

---

## Part 5: What Else Is in the Language?

### Other structural features (less directly relevant but worth noting)

**Quantifiers and the arithmetic hierarchy:** Godel sentences are Pi-1. Consistency statements are Pi-1. Proof complexity lower bounds are Pi-2 (for all inputs x, the proof of x requires super-polynomial length). The hierarchy constrains which obstructions apply at which level.

**Modalities and indexed types:** knowledge, provability, and possibility have their own structural theories (modal logic, doxastic logic, dynamic logic). Lob's theorem ("if the theory proves `Prov(s) -> s`, then it proves `s`") is a modal version of incompleteness. The obstruction might generalize to modal settings.

**Category theory and universal properties:** Lawvere's fixed-point theorem (1969) is a categorical generalization of Cantor, Godel, and Tarski. The encoding obstruction might be a refinement of Lawvere's theorem with specific content about FORM change vs. SEMANTIC change.

**Linear logic and resource sensitivity:** Girard's linear logic tracks how many times each assumption is used. Cut elimination in linear logic is polynomial rather than non-elementary. This suggests the exponential blowup is tied to the UNLIMITED REUSE structure of classical logic -- which is exactly the self-substitution mechanism.

**Complexity of normalization:** the precise growth rate of cut elimination depends on the logic. Pure propositional: polynomial. First-order: non-elementary. Second-order: non-elementary. Higher-order: non-elementary. The obstruction framework might predict these differences.

### Priority

The three domains in Parts 1-3 (binding, cut elimination, Curry-Howard) are immediate. The features in this Part 5 are longer-term -- they expand the program's reach but aren't needed for the next steps.

---

## Related

- [encoding-obstruction.md](encoding-obstruction.md) -- the core obstruction theory
- [self-representation.md](self-representation.md) -- self-reference and incompleteness
- [pvsnp/obstruction-independence.md](pvsnp/obstruction-independence.md) -- P vs NP independence argument
- [pvsnp/encoding-complexity.md](pvsnp/encoding-complexity.md) -- earlier P vs NP framing
- [pvsnp/barrier-analysis.md](pvsnp/barrier-analysis.md) -- existing P vs NP barriers
