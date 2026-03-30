# Complexity Classes as Structural Properties

## The Two Questions

For any structure with a decidable constraint, there are exactly two questions:

**Question 1 (Verification):** Given a specific arrangement, does it contract to ground?
- Run the rotation. Each step checks one constraint. Linear time.
- This is P.

**Question 2 (Search):** Does any arrangement exist that contracts to ground?
- The space of arrangements is exponential in the number of elements.
- This is NP.

The language makes P and NP visible as different questions about the same structure, not different classes of machines or different resource bounds on the same machine.

## Arrangement space

Given n elements `{e_1, e_2, ..., e_n}` and a constraint `C`, the arrangement space is all possible nestings of these elements into well-formed terms.

For flat lists (where elements are atomic — not themselves pairs), the arrangement space is the set of permutations: n! orderings. Each ordering determines which pairs of elements are adjacent during rotation, hence which constraint checks occur.

For trees (where elements may be pairs), the arrangement space is richer — it includes all binary tree shapes with n leaves. The number of such shapes is the Catalan number C(n), which grows exponentially.

The arrangement space IS the search space. It is not encoded, translated, or compiled into the search space. It is the search space, natively.

## What makes a problem hard

In this language, the difficulty of a problem is determined by two factors:

### 1. Constraint locality

A **local** constraint depends only on the labels of `a` and `b` — the two elements at the observation point. It doesn't need to see the rest of the structure. Checking it is O(1).

A **global** constraint depends on the relationship between the current element and everything already observed — a running state accumulated through previous rotations. Checking it requires inspecting the carried content.

Local constraints yield problems where each rotation step is independent. Global constraints yield problems where each step depends on history.

### 2. Constraint density

A **sparse** constraint rejects few arrangements. Most orderings contract. Finding one is easy — random sampling works.

A **dense** constraint rejects most arrangements. Almost no orderings contract. Finding one (if it exists) requires navigating a narrow path through exponential space.

NP-completeness arises when:
- The constraint is local (each check is cheap) but dense (almost everything fails)
- Or: the constraint is global (state accumulates) and moderately dense

The combination of cheap checking and hard finding is the P vs NP gap, expressed directly in the language's structure.

## Complexity as distance in arrangement space

Define the **distance** between two arrangements as the number of element swaps needed to transform one into the other. This gives the arrangement space the structure of the symmetric group S_n with the Cayley graph under transpositions.

The search problem is: starting from an arbitrary arrangement, find a path through the Cayley graph to a contracting arrangement. The constraint defines which vertices (arrangements) are contracting. The structure of these "good vertices" in the Cayley graph determines the difficulty:

- **If good vertices are dense and connected:** local search works. Walk the graph, improving constraint satisfaction at each step. Polynomial. P.
- **If good vertices are sparse and disconnected:** local search fails. You get trapped in basins. Finding a good vertex requires global knowledge of the graph. Exponential. NP-hard.

This is a geometric view of complexity. The constraint carves a landscape in arrangement space. P problems have smooth landscapes. NP problems have rugged landscapes. The language makes the landscape a first-class object.

## P in the language

A problem is in P when the arrangement can be constructed incrementally: place element 1, then element 2, ..., and at each step there's a polynomial-time way to choose the next element such that no constraint is violated.

In rotation terms: you can build the nesting from the inside out (or outside in), making one local choice at each level, and the constraint guarantees that local choices compose into a global solution.

This is the decomposability property from the coupling document. P problems are those where the arrangement decomposes into independent local decisions.

Formally: a constrained rotation problem is in P if there exists a polynomial-time function

```
next: (element, partial_arrangement) -> element
```

that extends any valid partial arrangement by one element while preserving constraint satisfaction. If such a function exists, you build the arrangement in n steps, each costing poly(n), total poly(n).

## NP in the language

A problem is in NP when:
1. The arrangement space is exponential
2. Checking a given arrangement is polynomial (rotate and check — linear)
3. No known polynomial `next` function exists

The witness is the arrangement itself. Literally the nesting order. The verifier runs the rotation. The search explores arrangement space.

NP-completeness means: if you could find contracting arrangements efficiently for this constraint, you could find them for any constraint. The constraint is "universal" in that it can simulate any other constraint's arrangement problem.

## The P vs NP question in the language

**P = NP** would mean: for every decidable constraint, if a contracting arrangement exists, it can be found in polynomial time. Equivalently: every constraint landscape has exploitable structure — no constraint is truly rugged.

**P != NP** would mean: there exist decidable constraints whose landscapes are genuinely rugged — where the only way to find a contracting arrangement (when one exists) is to explore an exponential portion of the space.

The language makes this question structural rather than machine-theoretic. It's not about Turing machines running in polynomial time. It's about the geometry of constraint landscapes in arrangement space.

## Observed and carried content revisited

At each rotation step:
- **Observed content:** the element `a` that passes through the observation point. Its label is read. The constraint is checked. Information about `a` is consumed (reduced to a bit: pass/fail).
- **Carried content:** the rest `b`. Untouched. Its internal structure persists. It will be available for future observations.

The total information in the term is conserved (the rule is reversible). But the constraint destroys information at each step (the bit). The accumulated information loss over all steps is what makes reconstruction (search) expensive.

If you recorded the constraint's input at each step — not just the bit, but the full `(a, b)` pair — you'd have the witness. The witness is the sequence of observations. Search is finding the sequence. Verification is replaying it.

The P vs NP gap is the gap between replaying a sequence of observations and finding the sequence in the first place.

## Connection to the spectral arithmetic framework

The eigenvalue/decomposition duality maps directly:

- **Eigenvalue:** the constraint check result (the bit). What obs reads. Cheap.
- **Decomposition:** the specific arrangement that produced that bit. What obs doesn't read. Expensive to recover.
- **Smuggled payload:** the carried content at each step. Present in the structure, invisible to the constraint.

The rotation rule is a simplified, discrete version of the Leibniz rule. Leibniz branches (doubles the term). Rotation doesn't branch (conserves term size). The complexity that Leibniz generates through branching, rotation generates through the arrangement space. The blowup is in the space of possible inputs, not in the output of a single step.

This is arguably cleaner. Leibniz mixes the rule's branching with the problem's difficulty. Rotation separates them: the rule is trivial (linear), the difficulty is entirely in the arrangement.
