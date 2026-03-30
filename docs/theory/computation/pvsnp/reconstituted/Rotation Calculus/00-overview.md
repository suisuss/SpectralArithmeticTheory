# Rotation Calculus: A Language for Complexity

## Purpose

A formal language whose primitive structure makes complexity classes visible intrinsically — not as meta-theoretic properties analyzed from outside, but as structural features of terms and their normalization.

The language has one rewrite rule, one data structure, and a parameterized constraint. The complexity of a problem is determined by the relationship between the constraint and the space of arrangements. The halting problem is excluded by construction.

## Core Insight

Every formal language requires a rewrite rule — the mechanism that bridges encoding and computation, syntax and semantics, intensional and extensional. Without a rewrite rule, you have notation. With one, you have a language.

A rewrite rule is a pure function on syntax that simultaneously:
- **Observes** structure (pattern-matches to determine applicability)
- **Transforms** structure (replaces the matched pattern)
- **Carries** unobserved structure (passes unmatched subterms through)
- **Exposes** structure for future observation (repositions carried content)

The observation and the transformation are inseparable — the same event. Recognition is action. Passing through the rule is passing through a door: you're on one side, then the other. No intermediate state.

## Design Principles

1. **One self-feeding rule.** A single operation that produces its own input. Not a rule applied to data — data acting on data.

2. **Head-tape unification.** No permanent separation between processor and processed. Elements take turns being observed and carried. The ribosome model, not the Turing model.

3. **Intrinsic contractibility.** The question "does this contract to ground?" is expressible within the structure, not analyzed from outside.

4. **No symbol creation.** The rule rotates and repositions. It doesn't branch or expand. The same elements persist throughout — only their arrangement changes.

5. **Termination by construction.** The rule monotonically reduces nesting depth. Every computation terminates. Undecidability enters only through the constraint parameter, and only if you allow it.

## Documents

| Document | Contents |
|----------|----------|
| [01-syntax.md](01-syntax.md) | Terms, ground state, nesting as storage |
| [02-rewrite-rule.md](02-rewrite-rule.md) | The rotation rule, its properties, observation as rewriting |
| [03-constraints.md](03-constraints.md) | The constraint parameter, decidability levels, where the halting problem lives |
| [04-complexity.md](04-complexity.md) | Complexity classes as structural properties, P vs NP in the language |
| [05-universality.md](05-universality.md) | Encoding NP problems, the compiler question, relationship to existing formalisms |
