# Constraints

## The Constrained Rule

The base rule rotates unconditionally. Every structure contracts. There is no computational interest — the complexity is always linear in the size of the term.

Complexity enters through the constraint. The constrained rule:

```
observe(pair(a, b)) -> pair(b, observe(a))      if C(a, b)
observe(pair(a, b)) -> stuck                    if not C(a, b)
observe(ground)     -> ground
```

Where `C` is a predicate on pairs of terms — the **constraint parameter**.

The constraint is the only point where a binary decision occurs. The rule inspects `a` and `b`, asks the constraint, and either rotates or halts. This is where information is lost — the constraint maps the rich structure of `(a, b)` to a single bit.

## What the constraint means

The constraint says: "these two elements are compatible in this order." It's a local adjacency check. Can `a` be observed while `b` is being carried? Is this pair of neighbors allowed?

Different constraints yield different problems:

- **C(a, b) = true for all a, b:** No constraint. Everything contracts. Trivial.
- **C(a, b) = "a and b have compatible colors":** Graph coloring.
- **C(a, b) = "a doesn't conflict with the assignment implied by b":** SAT.
- **C(a, b) = "a fits in the remaining capacity described by b":** Knapsack.

The constraint is a parameter, not part of the language. The language is fixed — one rule, one data structure. The constraint is the input that specifies which problem you're talking about.

## Decidability levels

The power of the language depends entirely on what constraints are allowed.

### Level 0: No constraint

```
C(a, b) = true
```

Every structure contracts. Complexity is O(n) where n is the nesting depth. No interesting computation. This is pure traversal.

### Level 1: Finite/Boolean constraints

```
C(a, b) is a Boolean function on the labels of a and b
```

Elements carry labels from a finite alphabet. The constraint checks label compatibility. This is the domain of NP-complete problems:

- **SAT:** labels are variable assignments, constraint is clause satisfaction
- **Graph coloring:** labels are colors, constraint is inequality on adjacent nodes
- **Hamiltonian path:** labels are vertices, constraint is edge existence

The constraint always terminates (finite lookup). Every computation terminates. The only question is whether an arrangement exists where every rotation step satisfies the constraint. This question is NP-complete for appropriate constraint families.

### Level 2: Primitive recursive constraints

```
C(a, b) is a primitive recursive function
```

The constraint may perform bounded computation — counting, comparing, bounded search — but always terminates. This extends the range of expressible problems:

- **Subset sum:** the constraint tracks a running total
- **Integer programming:** the constraint checks linear inequalities
- **Bounded optimization:** the constraint compares against a threshold

Still total. Still terminating. Richer than Boolean but the halting problem remains excluded.

### Level 3: General recursive constraints

```
C(a, b) is an arbitrary computable function
```

The constraint itself might not terminate. A single rotation step could diverge because the constraint check never returns. This is where the halting problem enters — not through the rotation rule (which is structurally terminating) but through the constraint.

At this level the language is Turing-complete. Any computation can be encoded by choosing an appropriate general recursive constraint. But decidability is lost — you can no longer guarantee that asking "does this arrangement contract?" is even a well-posed question, because individual steps might not terminate.

### Summary

| Level | Constraint | Termination | Complexity class |
|-------|-----------|-------------|-----------------|
| 0 | None | Always, O(n) | Trivial |
| 1 | Finite/Boolean | Always | NP (arrangement search) |
| 2 | Primitive recursive | Always | Beyond NP, still decidable |
| 3 | General recursive | Not guaranteed | Turing-complete, undecidable |

## Where the halting problem lives

The halting problem is precisely the boundary between Level 2 and Level 3. It is the question: does the constraint terminate?

The rotation rule doesn't contribute to undecidability. It is total by construction — each step reduces nesting depth. Undecidability enters exclusively through the constraint parameter. This is a clean separation:

- **The rule** is structural, total, deterministic, confluent
- **The constraint** is the interface to computational content
- **The arrangement** is the combinatorial object whose existence is the NP question

The language isolates these three concerns. Current formal systems (lambda calculus, Turing machines, recursive function theory) entangle them — the rule, the data, and the halting question are all mixed together. Here they are separated by construction.

## The constraint as the observation's judgment

Recall from the coupling document: verification maps `Instance x Witness -> Bool`. The information loss is in the judgment — the projection to a two-element set.

In this language, the constraint IS that judgment. Each rotation step passes one element through the observation point. The constraint is the binary decision: pass or fail. The information about why `a` and `b` are (in)compatible is discarded — only the bit remains.

Verification: given a pre-arranged structure, run the rotations. Each step asks the constraint once. Linear in the number of elements. This is P.

Search: given the elements and the constraint, find an arrangement where every step passes. The space of arrangements is exponential. This is NP.

The constraint makes the connection to P vs NP explicit:

- **Without constraint:** no information loss, no complexity, everything contracts
- **With decidable constraint:** information loss at each step (the bit), complexity in the arrangement space, P vs NP question is native
- **With undecidable constraint:** information loss is unbounded (the constraint might never return a bit), halting problem is native

The constraint is the valve that controls how much information each observation step destroys. No valve, no complexity. Finite valve, NP. Infinite valve, undecidability.

## Constraints as terms

For the language to be self-contained, constraints should themselves be expressible as terms. A constraint `C(a, b)` would be a term that, when composed with `a` and `b`, contracts to `ground` (pass) or gets stuck (fail).

```
C = pair(rule_1, pair(rule_2, ... pair(rule_k, ground) ...))
```

The constraint is itself a nested structure. Checking the constraint is running the rotation on a composed term. The constraint is data. The check is computation. The same rule applies to both.

This makes the language fully reflexive — constraints are terms, checking constraints is rewriting, and the question "is this constraint decidable?" becomes "does the constraint term always reach normal form?" Which is itself a question about contractibility.

The hierarchy of constraint levels then becomes:

- **Level 1:** constraint terms that are flat lists (finite lookup)
- **Level 2:** constraint terms that are bounded nesting (primitive recursive)
- **Level 3:** constraint terms that may contain self-reference (general recursive)

And the meta-question — "which level is this constraint?" — is the complexity of the constraint's own normalization.
