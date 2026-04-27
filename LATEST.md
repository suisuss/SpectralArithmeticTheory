# LATEST: foundations conversation snapshot

**Date:** 2026-04-27

Comprehensive record of a conversation working from "is associativity a rewrite rule" down to "where do we lose information when encoding the P vs NP independence claim." Records the substantive content, the artifacts produced (issue #54, `direction/encoding-invariance-at-counting.md`), and the open questions that emerged.

This is a conversation snapshot, not a position document. Where the user and I converged, that is noted. Where positions remained open, the open question is recorded. No claims here are formally verified by the Lean corpus unless explicitly marked.

---

## Arc

The conversation moved through, in order:

1. Whether associativity is a rewrite rule (and what that question even means).
2. What components a formal mathematical language requires.
3. Mathematical-object definitions via data types ("attribution").
4. Arithmetic operationally grounded in "people" — addition, subtraction, multiplication, division.
5. Counting as the foundation of mathematics.
6. Nest/unnest as new operations; whether nested and non-nested forms can be "categorically the same."
7. Whether any formulation of counting exists that is not ordinal (nesting) or cardinal (bijection).
8. Assessment of the Rotation Calculus formulation in this repo.
9. Rewrite rules that preserve inputs vs. those that do not.
10. Base counting (Indian-Arabic positional notation).
11. Data structures implied by encodings and rewrite rules.
12. The user's actual line of inquiry: encoding-invariance.
13. Whether encoding-invariance applies at the level of counting itself or only above it.
14. The relation between a system's evaluation complexity and the solvability of problems stated in it.
15. Where information is lost when we encode the P vs NP independence claim and when we investigate tractability of NP problems.

Two artifacts were produced:

- **GitHub issue #54** — "research: does Rotation Calculus reduce to zipper-traversal with an accumulator predicate?"
- **`docs/theory/direction/encoding-invariance-at-counting.md`** — a positioning document on whether the universal encoding obstruction extends downward to counting itself.

---

## 1. Associativity as a rewrite rule

**Question:** Is associativity `(a·b)·c = a·(b·c)` a rewrite rule?

**Resolution:** Not by itself. Associativity is an *equation*; a rewrite rule is an *oriented* equation. To use associativity for rewriting you must pick an orientation (right-associate or left-associate). Each orientation alone is terminating and confluent, normalising to a canonical parenthesisation.

**Why associativity is the canonical "bad example" in rewriting theory:**

- Combined with commutativity, naive AC-rewriting fails to terminate. Knuth–Bendix completion does not handle AC theories without extension; AC-matching / AC-unification become required.
- Reaching canonical form is `Θ(n²)` for a flat `n`-element associative chain.
- In simp-style proof assistants (Lean, Coq), tagging `add_assoc` as a rewrite typically loops because other rules can rotate it back.

**Modern treatments:**

- *Rewriting modulo AC*: do not orient; treat associativity as a structural property of the term algebra. E-graphs and equality saturation operate this way.
- *Decision procedures*: `ring`, `ac_rfl`, `Mathlib.Tactic.Abel` normalise via dedicated algorithms rather than firing `add_assoc` as simp.
- *Definitional equality*: in n-ary or list-append presentations, associativity is `rfl`.
- *Coherence*: in weak monoidal categories, associativity is a natural isomorphism, not even an equation.

**Takeaway:** Associativity sits exactly on the boundary where "treat as rewrite rule" stops being the right abstraction. It is the motivating counterexample for rewriting theory, proof-assistant tactic design, and categorical coherence simultaneously.

---

## 2. Components of a formal mathematical language

The user proposed: symbol set, notation, rewrite rules, attribution, substitution.

**Pushback:**

- *Notation* is surface convention, not a foundational component. `a+b` vs. `+(a,b)` vs. `(+ a b)` is the same formal object.
- *Rewrite rules* are one *style* of inference rule (reduction-oriented), not the whole category.
- *Attribution* is non-standard terminology — turned out to mean inductive type definitions (see §3).

**Standard Hilbert-style decomposition:**

1. Alphabet (primitive symbols).
2. Formation rules / grammar — which strings are well-formed formulas.
3. Axioms — distinguished wffs taken as starting points.
4. Inference rules — modus ponens, generalisation, substitution, etc.
5. Proof — a defined notion of finite sequence justified by axioms or inference rules.
6. Semantics (optional) — domain, interpretation function, satisfaction relation.
7. Variable binding conventions — α-equivalence, capture-avoiding substitution.

The user's list missed: formation rules, axioms (as distinct from rewrite rules), and a notion of proof.

**Foundational tradition matters:** In type theory (Martin-Löf, CIC, HoTT), formation rules and inference rules fuse into the judgmental framework. In set-theoretic foundations, new objects enter via definitional extension rather than via inductive types. Choice of foundational tradition changes the decomposition.

---

## 3. "Attribution" as inductive type definitions

User clarified: *attribution* = defining mathematical objects via data types.

**What an inductive type declaration packages:**

When you write `inductive Nat | zero | succ (n : Nat)` you are simultaneously declaring:

1. A new type symbol (`Nat`).
2. New constructor symbols (`zero`, `succ`).
3. Formation rules.
4. An elimination principle (recursor).
5. Computation rules (rewrite rules for the recursor applied to constructors).
6. Implicit uniqueness: the only `Nat`s are those built from constructors.

So inductive types are not a primitive component but a *schema* that emits new alphabet, formation rules, and rewrite rules at once. Treating "attribution" as parallel to "rewrite rules" or "symbol set" is a category error — it is a meta-level schema that produces all of those.

**Foundational commitment:** First-class inductive types are characteristic of type-theoretic foundations. ZFC has no analogue; new objects there enter via definitional extension or set-theoretic construction.

**What the user's list still misses, even granting data types as primitive:**

- Elimination / recursion principles (the dual of constructors).
- Judgments and contexts (`Γ ⊢ a : A`).
- Universes (avoid Girard's paradox).
- Axioms not derivable from inductive types alone (funext, propext, choice, classical logic, quotients).
- The distinction between definitional and propositional equality.

---

## 4. Arithmetic operationally: addition, subtraction, multiplication, division on people

User proposed:
- `+` = add people
- `−` = remove people
- `/` = group people (clarified later: partitive — split into N groups)
- `×` = add groups

**Type asymmetries:**

- `+ : People × People → People` (total)
- `− : People × People → People` (partial — no negative people)
- `× : ??? × ??? → People` — what are the arguments? "3 groups of 4" makes one argument a count and the other a group size. These are different *kinds* of thing. Commutativity `3 × 4 = 4 × 3` is then a *theorem*, not a definition — the rectangle insight.
- `/ : People × ??? → Groups` — the partitive reading gives a count of people per group; quotitive reading gives a count of groups. Same number, different operation, different output type.

**Partiality is the deeper issue:**

- `3 − 5` undefined (no negative people).
- `7 / 3` undefined (no fractional people).
- `3 × 4 people` ill-typed if both arguments are people.

Demanding totality forces ontological extension: integers need debt, rationals need parts, reals need continuum. The "people" ontology grounds exactly ℕ, with restrictions.

**Hidden primitives:**

- *Zero* — what is "no people"? Required for totality of `+`.
- *Successor* — `+1` is the actual atom; `+` is recursively defined from it.
- *Bijection-equality* — "same count" presupposes cardinality.
- *Order* — "more / fewer" is hidden in the operational vocabulary.

**Set-theoretic correspondence:**

| Op | Set meaning |
|---|---|
| `+` | disjoint union |
| `−` | set difference (partial) |
| `×` | Cartesian product |
| `/` | quotient by equivalence |

This is the initial model of the natural-number semiring.

---

## 5. Counting as foundation

**User's position:** Counting (ℕ) is the foundation of mathematics. Even granting Gödel, we still have arithmetic.

**This is the Kronecker/Peano/Brouwer/Bishop position** — intuitionism / constructivism. "God made the integers; all else is the work of man." Legitimate foundational choice.

**But "counting" is not as primitive as it sounds.** It presupposes:

1. Discrete thinghood (ontological commitment to separable countable objects).
2. Zero (starting point).
3. Successor (the actual atom — `+1`).
4. Bijection-equality (cardinality at the meta-level).
5. **Induction** (the most important and most hidden — without it, "counting" is just finite enumeration; you cannot quantify over all counts, prove universals, or define functions by recursion).

**Induction is irreducible.** It cannot be derived from more primitive counting facts. If you say "counting is foundational," you are really saying "successor + induction is foundational." Peano axiomatised this; Dedekind characterised the structure up to isomorphism in second-order logic.

**Counting alone cannot build the rest.** Constructions of ℤ, ℚ, ℝ, ℂ all require *pairs* and *equivalence classes* — set theory or dependent types as a composition layer. ℕ alone does not suffice; ℕ + a pairing/collection mechanism does.

**Cardinal vs. ordinal:**

- *Cardinal* — "how many." Three-ness as a property of collections. Equality by bijection.
- *Ordinal* — "which one." First, second, third. Equality by order-isomorphism.

For ℕ they coincide. For infinite sets Cantor showed they diverge. Children and everyday speech bundle them; foundational accounts must keep them separated.

**The Gödel sting (relevant to the project):** Once you formalise ℕ as Peano arithmetic, Gödel says the formalisation is incomplete. Löwenheim–Skolem says first-order PA does not pin down which ℕ — non-standard models exist. The intuitive object is not identical to any formal axiomatisation. This is the territory the SpectralArithmetic obstruction work lives in.

---

## 6. Nest/unnest and "categorically the same"

**User's question:** Can a nested object and an object without nested objects be "categorically the same object"?

**Counting is already nesting.** In Peano, `3 = succ(succ(succ(0)))` — three nests of the successor constructor around zero. Numbers *are* nesting depth. Adding "nest" to ℕ is not introducing a new operation; it is renaming the primitive. "Unnest" is predecessor — partial, undefined at zero.

**"Categorically the same" — four senses, increasingly weak:**

1. *Literal equality.* `{a} ≠ {{a}}`. No nesting transform preserves this except identity.
2. *Isomorphism.* `(A × B) × C ≅ A × (B × C)`. `A → (B → C) ≅ (A × B) → C` (currying). The usual mathematical "same."
3. *Equivalence in a category.* Allows more identifications.
4. *Propositional equality in HoTT.* Univalence collapses isomorphism into equality at the level of propositions.

**Examples where nesting/unnesting preserve the object up to iso:**

- Associativity (tree shape differs, algebra element does not).
- Currying / uncurrying.
- List representations (`cons 1 (cons 2 (cons 3 nil))` vs. flat `[1, 2, 3]`).
- Church numerals (`λf x. f(f(f x))`) isomorphic to Peano's `succ(succ(succ 0))`.

In each case the nested and flat forms carry identical information; the isomorphism is explicit.

---

## 7. Counting that is neither nesting nor cardinality

**User's question:** Is there any formulation of counting that isn't ordinal/nesting or cardinal/bijection?

**Answer: no, structurally.**

ℕ has exactly two irreducible aspects:

- *Ordinal* (sequence-like): successor, iteration, nesting. Peano, Church numerals, inductive types, NNO, free monoids, rank.
- *Cardinal* (collection-like): bijection, equipollence. Frege/Russell, Hume's principle, Dedekind-infinite.

Every candidate alternative reduces to one or both:

- Church numerals: nesting in higher-order disguise.
- Natural numbers object: successor-based universal property.
- Free monoid on one generator: tally-mark nesting.
- Dedekind-infinite: cardinality.
- Euler characteristic, K-theory, species, measure: structured cardinalities.
- Tally / unary: nesting made visible.
- Surreal numbers: recursion = nesting.

**Why this is not accidental:**

- ℕ is the initial algebra of the functor `X ↦ 1 + X`. This characterisation is ordinal in flavour.
- ℕ is the unique-up-to-iso skeleton of the category of finite sets under bijection. This is cardinal in flavour.
- Both characterisations pick out the same object. Any third characterisation that succeeds in picking out ℕ must invoke this structure somehow.

**The one different register:** If you drop "formalisation" and move to phenomenology — counting as an agent's *capability* (Brouwer's two-oneness) — you get a different *philosophical* register. But the moment you formalise it, you land back on successor or cardinality. So it is a different *philosophy* of counting, not a different *formulation*.

**Practical upshot:** A search for a counting mechanism that is neither ordinal nesting nor cardinal bijection is, as far as anyone knows, a search for something that does not exist. The productive question is which face a given calculus emphasises and what it does with the other.

---

## 8. Rotation Calculus assessment

The user asked for a read on the RC formulation as documented in `docs/theory/computation/pvsnp/reconstituted/Rotation Calculus/`. An Explore agent summarised the docs. My assessment:

**Strengths.**

- Low-dimensional: three constructors (`ground`, `pair`, `observe`), one rewrite rule with two cases, parameterised constraint.
- Termination by construction: count of pair-constructors-under-`observe` strictly decreases.
- Trivial confluence: exactly one redex per term.
- Clean architectural separation: rule (structural, terminating) vs. constraint (controls decidability) vs. arrangement (combinatorial object).

**Problems the project's own assessment flags:**

1. **CSP equivalence (March 2026 finding).** RC with flat lists *is* Permutation CSP in different notation. Termination and confluence are "free" in any sequential constraint checker. The rotation framing buys presentation, not proof leverage.
2. **Generator fixed-point circularity.** The argument is tautological for all problems, not specifically hard ones.
3. **Implication for the paper.** The honest reframing is "minimal presentation of Permutation CSP in which the empirical width-trajectory observations on resolution become visible," not "novel framework for P vs NP."

**My added structural observation.** RC's `pair` + `observe` + rotation rule is essentially **Huet's zipper** (*The Zipper*, JFP 1997) in different notation:

- `observe` marks the focus.
- The right child of each pair is the accumulated context.
- `observe(pair(a, b)) → pair(b, observe(a))` is the standard zipper move-right.

If this reading holds, RC is zipper traversal with an accept/reject predicate. Filed as **issue #54** to determine whether RC contributes anything beyond zipper-traversal-with-accumulator-predicate (a standard PL construct), with two concrete resolution criteria (RC-level phenomenon not expressible by standard zipper-traversal, or a clean equivalence reduction).

---

## 9. Rewrite rules that preserve inputs vs. those that do not

**Distinction:** information-preserving (reversible, linear, non-erasing) vs. information-destroying (projecting, erasing, collapsing).

| Preserving | Non-preserving |
|---|---|
| Associativity reshuffle | Projection `fst(a, b) → a` |
| Commutativity | β-reduction with erasure `(λx. 1) y → 1` |
| Currying / uncurrying | Cut elimination (some presentations) |
| RC rotation in isolation | Any rule with weakening |
| Reversible computation, linear logic | Classical structural rules |

**Key facts:**

- Preserving rules are equations in disguise. Orientation becomes a choice about search direction, not semantics.
- Non-preserving rules make commitments. Once applied, you cannot recover the input from the output.
- *A rule can be preserving while the system containing it is not.* This is exactly the RC situation: the rotation rule is reversible (you can unrotate), but the constraint is a lossy predicate. The system is lossy even though the rule is not.

**Operational consequences:**

- Lossless rules play well with memoisation, parallelism, and equality saturation (e-graphs).
- Lossy rules do not — you cannot share a node representing "the output of a projection" without losing the ability to recover.

---

## 10. Base counting (Indian-Arabic positional)

**Positional notation is a compression of nesting.**

- Unary / Peano: `Θ(n)` symbols for the number `n`.
- Base-`b` positional: `Θ(log_b n)` symbols.

The exponential compression comes from one specific move: reusing a fixed digit alphabet at different positional weights. The position is a stealth exponent. Brahmagupta's real innovation (~628 CE) was the rule for zero as a placeholder — previous systems (Babylonian, Mayan) had zero symbols but not the full set of arithmetic rules involving zero.

**Two observations:**

1. **Positional notation is still nesting.** `347` unfolds as `((3·10 + 4)·10 + 7)`, a right-associated expression tree of depth `log_b(n)`. The depth is logarithmic rather than linear, but the tree is there.
2. **Algorithm complexity tracks the representation.** Addition is `O(log n)` positional, `O(n)` unary. Multiplication is `O((log n)²)` schoolbook, `O(log n · log log n)` Harvey–van der Hoeven (2019). These complexities exist *in the representation*, not in the numbers.

**Takeaway:** Base counting is not an alternative to nesting — it is nesting with a compression scheme that reuses a finite alphabet. The arithmetic asymmetry between unary and positional (children doing 10-digit multiplication, no one doing 10-stroke unary multiplication) is entirely an artifact of the encoding.

---

## 11. Data structures implied by encodings

**An encoding is a data structure, and a rewrite rule is a set of operations on it.** Different encodings of the same mathematical object force different operations to be cheap or expensive.

| Encoding | Implied data structure | Cheap | Expensive |
|---|---|---|---|
| Peano unary | Singly linked list | `succ`, `pred` | addition, comparison |
| Church numeral | Closure / higher-order function | iteration | equality, predecessor (Kleene trick) |
| Binary positional | Array of digits | arithmetic, comparison | `succ` with carries (amortised O(1)) |
| Skew binary (Okasaki) | Balanced tree of digits | `succ`, indexed access | some arithmetic |
| Cons-list of elements | Linked list with head/tail | head access, prepend | indexed access, concat |
| RC `pair` + `observe` | Zipper on a binary tree | move-focus, contextual read | random access |

**General principle.** Given a rewriting system, you can usually read off:

- The data structure it manipulates (from the term constructors).
- The invariants it maintains (from what the rules preserve).
- The complexity profile of intended operations (from how many rule applications a canonical task requires).

So *rewrite-rule design and data-structure design are the same activity.* Choosing Peano vs. binary vs. Church vs. zipper numerals is not choosing a different *number* — it is choosing a different *access pattern*.

---

## 12. What the user is probing for

I asked, the user confirmed: probing for information about both horns of an encoding-invariance question.

The through-line:

- "Is associativity a rewrite rule?" → can structural equality be separated from syntactic presentation?
- "What makes a formal language?" → minimum scaffolding, how much is notation artifact?
- "Counting as foundation" → commit to the most primitive object.
- "Any formulation of counting that isn't nesting or cardinality?" → is there a representation-free view of ℕ?
- "Rewrite rules that preserve inputs vs. not" → which operations commit you to an encoding?
- "Base counting" → compression of nesting, same information, different cost profile.
- "Data structures implied by encodings" → encoding *is* the data structure.

Every question reaches toward the same seam: **where does the encoding end and the mathematical content begin?** If the universal encoding obstruction (Part 2 thesis) is about encoding-invariance, the natural foundational question is whether that invariance bottoms out cleanly or whether the obstruction bites all the way down at counting.

---

## 13. Encoding-invariance at counting (artifact: direction doc)

The above led to a direction doc: `docs/theory/direction/encoding-invariance-at-counting.md`. Summary of the framing:

**The question.** Does the universal encoding obstruction apply downward to counting itself, or only above it (where counting serves as a substrate the obstruction presupposes)?

**Horn 1 (invariance holds at counting).** ℕ is structurally unique up to isomorphism. Every encoding of ℕ is a presentation of the same object. The obstruction applies to *theories over ℕ*; not to ℕ itself. Codebase evidence: `Core/Basic.lean`, `Core/Semiring.lean`, `Verification/PeanoTest.lean` derive Peano theorems from algebraic axioms independent of any specific numeral encoding.

**Horn 2 (invariance fails at counting).** "Counting" is an encoding choice masquerading as a primitive. Unary, positional, Church, and zipper numerals are not the same object at the level where complexity bites. The obstruction recurs at the counting layer. Codebase evidence: `addition-non-locality.md` documents that carry propagation forces stateful computation, i.e. arithmetic operations have different complexity profiles depending on encoding. The RC ≅ CSP ≅ zipper-traversal reduction chain is a pattern where apparent framework-level structure dissolves into notation under translation.

**What would settle it.**

- *Horn 1 route*: identify the minimum theory strength at which `EvalRewriteWitness` becomes non-trivial; show that strength strictly exceeds counting.
- *Horn 2 route*: construct a counting-level instance of `EvalRewriteWitness` (or its faithful analogue) and verify it in Lean.

**Scope discipline.** This is a thesis-framing question; not a recommendation to pursue as paper-critical. `focus.md` priorities (PAGodelSystem Phase 1, paper drafting) remain.

---

## 14. Evaluation complexity and solvability

**Conflation to disentangle.** The user said "the system you use, it has to be expressive enough to encode a problem, that system has its own evaluation complexity." Two axes are bundled:

- *Expressiveness* — what problems can be stated.
- *Evaluation complexity* — what running the rules costs.

Untyped λ-calculus is maximally expressive with minimal evaluation machinery. PRA is restrictively expressive but its evaluations are fast and total. They are separate axes but related: the hierarchy theorems (`TIME(f(n)) ⊊ TIME(f(n) log f(n))`) say arbitrary expressiveness comes at evaluation cost.

**Six precise senses in which evaluation complexity ↔ solvability:**

1. *Trivial upper bound.* The system cannot solve what it cannot evaluate within budget.
2. *Reasonable encoding equivalence.* P, NP, PSPACE are robust under polynomial-time encoding changes (Cobham–Edmonds). Unary is *not* reasonable — "unary SAT" is in P trivially because the input has been padded.
3. *Succinctness shifts complexity classes.* Adjacency-matrix 3-colorability is NP-complete; circuit-succinct 3-colorability is NEXP-complete (Papadimitriou–Yannakakis). Same problem, more compact encoding, exponentially harder class.
4. *Proof-theoretic strength is evaluation complexity.* The provability hierarchy (EFA ⊂ PRA ⊂ PA ⊂ Z₂ ⊂ ...) is the evaluation-complexity hierarchy in different costume.
5. *Natural proofs barrier* (Razborov–Rudich, 1997). The evaluation complexity of the proof technique itself binds what the technique can prove. A polynomial-time-checkable property cannot prove exponential lower bounds without breaking standard cryptographic assumptions. This is a sharp, formal link.
6. *The obstruction itself.* `EvalRewriteWitness` reads as: any system admitting all form-preserving semantics-preserving rewrites cannot be efficient; any efficient system must refuse some such rewrites. The form changes are encoding changes; their cost is unbounded across encodings; therefore completeness and efficiency are jointly impossible.

**One-sentence summary.** The evaluation complexity of a formal system is not separable from the solvability of problems stated in it — they are dual aspects of the same resource accounting.

**What this does not settle.** Even granting the duality, horn-1/horn-2 of the encoding-invariance question remains open. The duality is real; where it engages is still open.

---

## 15. Where information is lost in the P vs NP investigation

The user's sharpest framing: when we encode the P vs NP independence claim, are we using a language expressive enough or compressing it too much? Where are we losing information?

**Both losses are happening, in stackable layers.**

**The encoding pipeline, each stage lossy:**

1. Real computational problem → language (set of strings). Distributional structure, domain semantics, instance-level features all lost.
2. Language → decision problem. Optimisation, approximation, counting, search collapsed into yes/no. `#P ≠ FP` could be true while `P = NP` (not believed); the compression makes these look like one question.
3. Decision problem → polynomial/exponential boundary. Fine-grained complexity (SETH, ETH) reveals structure the cut hides.
4. Polynomial-time → Turing machines. Circuits, branching programs, algebraic models (Valiant's `VP` vs. `VNP`), arithmetic models all expose structure TMs hide.
5. Turing machines → Gödel codes. To state P ≠ NP inside PA, you encode TMs as numbers; the resulting formula is correct but has lost operational semantics.
6. PA statement → meta-theoretic claim. Independence is relative to the theory; PA-independent ≠ ZFC-independent.

**Formal certifications of over-compression (the barriers):**

- **Relativization** (Baker–Gill–Solovay 1975): oracles exist making P=NP and others making P≠NP. Diagonalisation-based techniques are blind.
- **Natural proofs** (Razborov–Rudich 1997): polynomial-time-checkable properties of hard functions yield poly-time distinguishers, breaking crypto.
- **Algebrization** (Aaronson–Wigderson 2008): extends relativization. Non-algebrising techniques required.

Each barrier is a formal proof that a class of compressions is too lossy.

**Under-expressiveness:**

- Average-case vs. worst-case. Cryptography needs average-case hardness; classical P vs. NP is worst-case.
- Instance structure. Real SAT has community structure, phase transitions, heuristic exploitability — all invisible in the asymptotic framing.
- Interactive / probabilistic models. `IP = PSPACE` (Shamir) shows what is gained by changing the model.

**For the obstruction framework specifically:**

1. *Unifying seven instances under one pattern.* `EvalRewriteWitness` captures form-changing semantics-preserving rewrite abstractly. Each instance has domain structure the pattern elides. Deliberate compression. The RC → CSP collapse is a data point that framework-level patterns can dissolve under translation.
2. *Proof-complexity reformulation.* Trades "circuits compute" for "proofs verify" — static for dynamic. Gains mathematical analysis of proof length; loses the operational aspect that distinguishes SAT solvers from proof systems in practice.
3. *Binary accept/reject constraint structure* (if RC-style framing bleeds into the obstruction): reducing problem structure to per-step predicates may compress non-local features (the carry propagation documented in `addition-non-locality.md`).

**Three criteria for the universal obstruction to be doing real work rather than renaming:**

1. *Sharpness.* Not every semantics-preserving rewrite satisfies the pattern. If satisfied trivially by any rewrite in any system, the pattern has no teeth.
2. *Discriminating power.* The pattern distinguishes obstruction-exhibiting systems from obstruction-free ones.
3. *Predictive.* The framework retrodicts a known barrier or predicts a new lower bound. Seven retroactively unified instances are weak evidence; an eighth instance predicted in advance would be strong evidence.

These criteria are testable. The most productive thing for the paper is to state explicitly which compressions are being made and give the test that would show each is a real unification rather than a renaming.

---

## Open questions left at the end

1. Does the universal encoding obstruction apply at the level of counting, or strictly above it? (Horn 1 vs horn 2 of the direction doc — concrete resolution criteria stated there.)
2. Is RC reducible to zipper-traversal-with-accumulator-predicate, or does it carry structure that does not reduce? (Issue #54 — concrete resolution criteria stated there.)
3. Where on the arithmetic hierarchy does `EvalRewriteWitness` first engage non-trivially? (Required for either horn-1 settlement or sharper framing of the obstruction's domain.)
4. Does the obstruction framework satisfy the three criteria above (sharpness, discriminating power, predictiveness)? Self-application of the project's own assessment standard.

---

## Artifacts produced

- **Issue #54** — `research`, `parked`. https://github.com/suisuss/SpectralArithmeticTheory/issues/54
- **`docs/theory/direction/encoding-invariance-at-counting.md`** — positioning doc on the horn-1/horn-2 question.
- **This file (`LATEST.md`)** — conversation snapshot.

All produced in worktree `.worktrees/docs-encoding-invariance-at-counting` on branch `docs/encoding-invariance-at-counting`. Nothing has been committed; nothing has been pushed.
