# Universality

## The compiler question

Can every NP problem be expressed as a constrained rotation problem without exponential overhead in the translation?

If the translation from problem to `(elements, constraint, arrangement)` is itself polynomial, the language is a universal framework for NP. If the translation requires exponential work, we've just moved the complexity into the compiler and gained nothing.

## Encoding NP problems

### SAT

A Boolean formula in CNF with variables `x_1, ..., x_n` and clauses `c_1, ..., c_m`.

**Elements:** each element is a variable-assignment pair `(x_i, v_i)` where `v_i in {0, 1}`.

**Arrangement:** a nesting that places all variable assignments in sequence.

**Constraint:** `C(a, b)` checks that the assignment `a` doesn't violate any clause, given the assignments already carried in `b`.

More precisely: the carried content `b` accumulates the partial assignment. When element `a = (x_i, v_i)` is observed, the constraint checks: does extending the current partial assignment with `x_i = v_i` violate any clause that is now fully assigned?

**Verification:** rotate through the list. Each step extends the partial assignment and checks clause consistency. Linear in n.

**Search:** find an ordering (assignment) of elements such that all rotations pass. This is SAT.

The translation is polynomial: n elements (one per variable), m constraint clauses stored in the constraint predicate.

### Graph coloring

A graph G = (V, E) and k colors.

**Elements:** each element is a vertex-color pair `(v_i, color_i)`.

**Arrangement:** a nesting that places colored vertices in sequence.

**Constraint:** `C(a, b)` checks that the color of `a` differs from the color of any neighbor of `a` already placed in `b`.

**Verification:** linear. **Search:** exponential. **Translation:** polynomial.

### Hamiltonian path

A graph G = (V, E).

**Elements:** one element per vertex.

**Arrangement:** a nesting representing a proposed path.

**Constraint:** `C(a, b)` checks that there exists an edge from `a` to the most recently placed vertex in `b`.

**Verification:** linear (check each edge exists). **Search:** exponential (permutation space). **Translation:** polynomial.

### Subset sum

A set of integers `{s_1, ..., s_n}` and a target T.

**Elements:** each element is an integer `s_i` together with an include/exclude flag.

**Arrangement:** a nesting of all elements.

**Constraint:** `C(a, b)` maintains a running sum in the carried content. When the last element is observed, the constraint checks that the running sum equals T.

**Verification:** linear. **Search:** exponential. **Translation:** polynomial.

## The pattern

In every case:
- Elements are direct encodings of the problem's components (variables, vertices, integers)
- The arrangement IS the witness (assignment, coloring, path, subset selection)
- The constraint IS the problem specification (clause satisfaction, edge existence, sum target)
- The translation is polynomial — no blowup

The language doesn't simulate these problems. It expresses them natively. The arrangement space IS the search space. The rotation IS the verification. No indirection.

## NP-completeness of constrained rotation

**Claim:** The constrained rotation problem (given elements and a Boolean constraint, does a contracting arrangement exist?) is NP-complete.

**NP membership:** A contracting arrangement is a polynomial-size witness (the nesting). Checking it requires running the rotation — linear time. So the problem is in NP.

**NP-hardness:** SAT reduces to constrained rotation in polynomial time (as shown above). Since SAT is NP-complete, constrained rotation is NP-hard.

Therefore constrained rotation is NP-complete. The language captures NP exactly.

## Relationship to existing formalisms

### Lambda calculus

Lambda calculus has beta reduction as its rewrite rule. Beta reduction is more powerful than rotation — it can create new redexes, diverge, and encode arbitrary computation in the rule itself.

Rotation is weaker by design. It cannot diverge. It cannot create new structure. All computational power comes from the constraint, not the rule. This separation is the point — it isolates complexity in the arrangement rather than entangling it with the rule.

Lambda calculus encodes NP problems by encoding Turing machines that search solution spaces. The encoding is indirect — multiple levels of simulation. Rotation encodes NP problems directly — the arrangement IS the solution.

### Turing machines

Turing machines have a tape, a head, and a transition function. The transition function is the rewrite rule (current state + symbol -> new state + symbol + direction). The tape is the store.

In rotation: the nesting is the tape. The observation point is the head. The constraint is the transition function. But there's no separate head — the observation point is just wherever `observe` sits in the term. And the "tape" rotates through the head rather than the head moving along the tape.

The key difference: in a Turing machine, the head moves along the tape (spatial metaphor — the data is laid out, the processor traverses it). In rotation, the data moves through the observation point (temporal metaphor — the processor is fixed, the data flows through it). This is the ribosome architecture.

### Circuit complexity

Boolean circuits are DAGs of gates. Circuit complexity counts gates and depth.

In rotation: elements are inputs, the arrangement is the circuit wiring, the constraint is the gate function. But rotation is sequential (one observation at a time), while circuits are parallel (all gates at a depth level fire simultaneously).

Circuit depth corresponds to the nesting depth of the carried content (how much accumulated state the constraint must inspect). Circuit width corresponds to the number of elements at the same nesting level.

The rotation language could be extended to handle parallelism by allowing multiple `observe` markers, but this breaks the single-observation-point property and complicates the semantics. For now, the language is inherently sequential — which is appropriate for the P vs NP question (polynomial time is a sequential resource bound).

### Proof complexity

Proof systems have axioms, inference rules, and derivations. The length of the shortest proof of a tautology is the proof complexity.

In rotation: a proof is a specific arrangement that contracts to ground. The proof's length is the number of elements (the nesting depth). The question "does a short proof exist?" is the question "does a contracting arrangement with few elements exist?"

Proof complexity lower bounds (showing that certain tautologies require long proofs in certain systems) correspond to showing that certain constraints require many elements in any contracting arrangement. This is a direct structural correspondence — not a simulation.

## What the language doesn't do

The language captures NP problems but does not (in its current form) directly express:

- **Problems beyond NP:** PSPACE, EXP, etc. These would require allowing the constraint or the arrangement to be exponentially large, which defeats the polynomial-witness property.
- **Promise problems:** where the input is guaranteed to be yes or no (but not which). The language doesn't have a mechanism for promises.
- **Approximation:** the constraint is binary (pass/fail). There's no notion of "almost satisfying" a constraint.
- **Randomized computation:** the rotation is deterministic. There's no randomness.

These are deliberate limitations. The language is designed to talk about NP specifically — the structural heart of computational complexity. Extensions to broader classes would require additional machinery, which should be added carefully to avoid entangling what the base language cleanly separates.

## The atom

The universal composable unit is `pair` — the minimal container for "this and the rest." It's the cons cell, the codon, the bit-and-carry. Everything is built from it. The rule acts on it. The constraint evaluates it. The arrangement is a configuration of it.

`pair` plays the role of NAND (universal Boolean gate), SUBLEQ (universal instruction), Iota (universal combinator) — but for a different purpose. NAND computes. SUBLEQ executes. Iota constructs. `pair` arranges. And the claim is that arrangement, under constraint, is the fundamental unit from which complexity arises.

Ground state: `ground` — the `pair` that isn't. The fixed point of observation. The base case. The atom from which nothing can be extracted and to which everything contracts.

The language is: `pair`, `ground`, `observe`, one rule, one constraint. Everything else follows.
