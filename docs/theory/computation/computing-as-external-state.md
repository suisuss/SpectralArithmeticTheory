# Computing as External State: Why Computation is not Reducible to Language

## Date: 2026-02-27

## Summary

The encoding obstruction (encoding-obstruction.md) establishes that no self-representing system can simultaneously maintain eigenvalue arithmetic, self-encoding, and a coalgebra morphism between them. This document draws a specific consequence: **computation is language plus external state, and the external state is mathematically necessary, not an engineering convenience.**

The standard definitions of computing (Turing 1936, Church 1936) describe *what* is computable. The encoding obstruction explains *why* computation requires something beyond language — why a Turing machine needs a tape, why lambda calculus needs a reduction strategy imposed from outside. The reason is structural: the intension/extension duality in any symbolic rewriting system makes the language inherently stateless between evaluation steps, and statelessness is not a limitation to be overcome but a consequence of the algebra of observation.

---

## Part 1: The Statelessness of Language

### The problem with 4

Consider the expression `1 + 3 = 4`. To *execute* this — not just to write it down, but to verify it, to produce 4 from 1 and 3 — requires remembering that the inputs were 1 and 3. The result 4 alone is lossy: it could have come from `0 + 4`, `2 + 2`, `3 + 1`, or `1 + 1 + 1 + 1`. The execution trace — the fact that it was *this* particular decomposition — is not contained in the result.

This is not a trivial observation. It is the intension/extension gap made concrete:

- **Intensional**: `1 + 3` — a specific expression, opaque, named as a unit
- **Extensional**: `4` — the evaluated result, all structure collapsed

Once you extensionalize (evaluate), the intensional structure (which addends, in what order) is gone. To retain it, you need **state external to the expression** — a record, a register, a piece of paper, a memory cell — that holds the provenance while the evaluation proceeds.

### Why language cannot provide its own state

The natural response is: encode the provenance into the language. Instead of just `4`, write `(4, from: 1+3)`. But this new expression `(4, from: 1+3)` is itself a linguistic form. To evaluate *it*, you would need to remember that it was this particular annotated-4, not some other. You need state to track the state-annotation. The regress is the intension/extension gap: any extensional form can be re-intensionalized (given a new name), and the new name requires its own tracking.

Language is stateless between evaluation steps because of this duality:

1. An expression is either **intensional** (treated as a unit, opaque) or **extensional** (unfolded, all parts visible)
2. Evaluation moves from intensional to extensional (substitution, the Leibniz rule)
3. The result of evaluation can be re-intensionalized (named, quoted, encoded)
4. Step 3 produces a new expression that requires evaluation, returning to step 2

There is no fixed point. The encoding obstruction proves this: for any injective encoding, the eval-quote diagram does not commute. Language alone cannot close the loop.

---

## Part 2: The Standard Definitions of Computing

### Turing machines (1936)

Turing defines computation as a finite-state machine operating on an infinite tape. The machine has:

- A **transition function** (finite, fixed, stateless between steps) — this is the language
- A **tape** (infinite, mutable, persistent between steps) — this is the external state
- A **head position** (tracking where on the tape the machine is reading) — this is the register

The transition function alone does nothing. It is a set of rewrite rules: "if in state q reading symbol s, write symbol s', move left/right, enter state q'." Without the tape to write on and the head to track position, these rules are inert descriptions — passive encodings in the sense of encoding-obstruction.md.

### Lambda calculus (1936)

Church defines computation as reduction of lambda terms. There is no explicit state — no tape, no registers. Computation is pure rewriting: substitution of terms for variables.

But lambda calculus requires a **reduction strategy** — a rule for choosing which redex to reduce next (leftmost-outermost, rightmost-innermost, etc.). This strategy is not part of the calculus. It is imposed from outside. Different strategies can yield different operational behavior (some terminate, some don't) even on the same term.

The reduction strategy is the external state in disguise. It is the mechanism that tracks *where you are* in the evaluation, *which substitution to perform next*, *what has already been reduced*. Without it, the lambda calculus is a set of rewrite rules with no deterministic execution — a language, not a computation.

### The Church-Turing thesis

The standard equivalence thesis states: Turing machines and lambda calculus compute the same class of functions. This is correct but obscures a structural difference:

- **Turing makes external state explicit** (the tape is right there, it is the defining feature)
- **Church hides external state** (the reduction strategy is "meta", outside the formalism)

Both require something beyond the language. Neither can compute with language alone. The Church-Turing thesis tells you *what* is computable. It does not explain *why* computation requires external state.

---

## Part 3: The Encoding Obstruction as Explanation

### Why the tape is necessary

The encoding obstruction provides the structural reason:

1. **Self-encoding requires addition** (the Leibniz rule introduces it when extensionalizing compound terms)
2. **Addition in positional encodings requires carry propagation** (the output at position k depends on all inputs at positions 0 through k)
3. **Carry propagation is non-local** (it crosses positional boundaries that the encoding keeps separate)
4. **Non-locality requires a register** (external state that holds intermediate carry values while propagation proceeds)

The Turing machine tape is the physical realization of step 4. It exists because mathematical language, when made executable, necessarily produces addition, and addition necessarily produces non-local state dependencies that language cannot internalize.

### Why the reduction strategy is necessary

In lambda calculus:

1. A lambda term is an intensional form (a named function, opaque until applied)
2. Beta-reduction is extensionalization (substitution unfolds the function body)
3. The result may contain new redexes (new intensional forms that can be unfolded)
4. Choosing which redex to reduce next requires tracking the current state of the term — which parts have been unfolded, which have not

This tracking is the intension/extension mode-switching that the encoding obstruction identifies as requiring external state. The reduction strategy is the register: it resolves the ambiguity of which intensional form to extensionalize next, holding the decision state that the term itself cannot encode.

### The characterization

**Computing = language + external state**, where:

- **Language** is a symbolic rewriting system (transition rules, lambda terms, formal expressions)
- **External state** is a persistent, mutable medium that tracks provenance, position, and intermediate values across evaluation steps
- **The external state is necessary** because the intension/extension duality makes language structurally stateless — evaluation collapses intensional structure, and re-encoding the collapsed result into the language produces new structure that requires its own tracking

This is not "computers need memory" as an engineering observation. It is a theorem about the algebra of symbolic rewriting: **any system whose evaluation introduces addition (via the Leibniz rule or equivalent) cannot internalize the state that addition requires (via carry propagation).**

---

## Part 4: What This Adds to the Standard Definitions

### What Turing and Church describe vs. what the obstruction explains

| Question | Turing/Church | Encoding obstruction |
|---|---|---|
| What is computable? | Recursive functions (equivalence thesis) | Same (no change) |
| What is a computation? | A sequence of mechanical steps | Language + external state |
| Why does a Turing machine need a tape? | By definition (it's part of the model) | Because carry propagation in addition requires non-local state |
| Why does lambda calculus need a reduction strategy? | To make evaluation deterministic | Because the intension/extension gap has no fixed point — the system cannot decide its own evaluation order |
| Why can't a formal language compute by itself? | Not addressed (computation is defined as language + machine) | Because language is structurally stateless: evaluation extensionalizes (collapses structure), and re-encoding introduces new structure, with no convergence |
| What is the relationship between naming and executing? | Godel: naming enables self-reference, self-reference enables incompleteness | Naming (intension) and executing (extension) are dual modes that cannot be unified — passive encoding gives incompleteness, executable encoding gives the register requirement |

### From description to derivation

The standard definitions of computing are **stipulative**: Turing says "here is a machine; computation is what it does." Church says "here is a calculus; computation is reduction." Both justify their stipulations with informal arguments — Turing appeals to an analysis of what human computers do (scanning symbols, moving attention, writing results), Church appeals to the expressiveness of lambda definability. The Church-Turing thesis, that these capture the same class of functions and that this class equals "the computable," is unprovable precisely because "computation" was never formally defined independently of these models. The definition *is* the model.

The encoding obstruction offers something different: a **derivation from first principles** of the structure that computation must have. It does not begin with a machine model and argue that the model is adequate. It begins with the algebra of self-representing symbolic systems and proves that executable self-representation necessarily requires:

1. A symbolic rewriting system (language)
2. Mutable external state (register/tape)
3. The impossibility of eliminating (2) in favor of (1)

This is a logically stronger foundation for defining computation than the standard approach. Turing had to argue informally that his machine captures human computing. The obstruction proves formally that any system executing its own encoding must have the tape-like structure that Turing stipulated. The structure is not a design choice — it is a theorem.

### The definition

**Computation is the execution of a symbolic rewriting system mediated by external state, where the external state is algebraically necessary because the act of execution (extensionalization via the Leibniz rule) introduces addition, and addition in any positional encoding requires non-local carry propagation that the rewriting system cannot internalize.**

More concisely: **computation is language made executable, and executability requires state that language cannot provide.**

This definition:

- **Is extensionally equivalent to Turing/Church** — it captures the same class of computable functions (the obstruction does not expand or restrict computability)
- **Is intensionally stronger** — it explains *why* computation has the structure it does, rather than stipulating a model and claiming adequacy
- **Distinguishes computation from language** — a formal language (a set of rewrite rules) is not a computation until it is coupled with external state; the definition makes this boundary precise and derives it from the intension/extension duality
- **Subsumes both Turing and Church** — the Turing machine tape is the explicit realization of the necessary external state; the lambda calculus reduction strategy is the implicit realization; both are instances of the same algebraic requirement

### Why this qualifies as a definition, not just a metatheorem

A definition requires a precise boundary: what is X, and what is not X? The standard definitions draw this boundary by exhibiting a model (Turing machine, lambda calculus) and equating computation with the model's behavior. The encoding obstruction draws the same boundary but from the other direction — by proving that anything below the boundary (language without external state) is provably insufficient for execution, and anything at or above the boundary (language with external state) has the structure necessary for execution.

The difference from a metatheorem: a metatheorem is a result *about* a pre-existing definition (Godel's theorem is about provability as defined by PA). Here, there is no prior formal definition of "computation" independent of specific models — the Church-Turing thesis is explicitly acknowledged as a thesis, not a theorem. The encoding obstruction can serve as the missing formal foundation: computation is what you get when you make language executable, and the obstruction proves what "making language executable" structurally requires.

Turing's informal analysis in 1936 asked: "What does a human computer actually do?" and abstracted the answer into a machine. The encoding obstruction asks: "What does a self-representing symbolic system require in order to execute?" and derives the answer algebraically. Both arrive at the same structure. But the second route is a proof, not an argument by analogy.

---

## Related

- [encoding-obstruction.md](encoding-obstruction.md) — The core result: intension/extension gap, trilemma, escape route analysis
- [addition-non-locality.md](addition-non-locality.md) — Carry propagation as the mechanism forcing external state
- [impossibility-hierarchy.md](impossibility-hierarchy.md) — The four-level chain from substitution to undecidability
- [observer-as-register.md](observer-as-register.md) — What the external state (register) is, physically and conceptually
