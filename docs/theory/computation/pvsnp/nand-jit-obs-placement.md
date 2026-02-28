# NAND as obs(compose) and JIT Obs Placement

## Date: 2026-02-28

## Summary

NAND gates correspond directly to `obs(compose(a, b))` in the framework. A circuit built entirely from NANDs translates to a `nestedObsCompose` term -- obs at every level -- which normalizes in constant depth (2 passes) but has exponential term size. This reveals that the two proved normalization regimes are the eager/lazy extremes of a depth-width tradeoff. The open question: is there an intermediate "JIT" strategy that places obs at selected levels, achieving sublinear depth without exponential term size?

---

## Part 1: NAND = obs(compose)

### The Boolean restriction

In DynSemiring restricted to {f_0, f_1} = {0, 1}:

| Operation | DynSemiring | Boolean |
|-----------|-------------|---------|
| compose(a, b) | a * b | AND(a, b) |
| oplus(a, b) | a + b - a*b | OR(a, b) |
| obs(f_0) = z | eigenvalue 0 | output 0 |
| obs(f_1) = f_1 | eigenvalue 1 | output 1 |

NAND(a, b) = NOT(AND(a, b)). At the Boolean level, `obs(compose(a, b))` applies the Leibniz rule to AND(a,b), decomposing it into its derivative structure. While obs is not Boolean NOT, the structural role is analogous: `obs(compose(a, b))` "cracks open" the composition, just as NAND exposes the internal structure of AND.

More precisely: a NAND circuit of depth d translates to a term with obs wrapping compose at every gate. This is exactly the `nestedObsCompose` structure.

### NAND circuits ARE nestedObsCompose

A NAND circuit with gates g_1, ..., g_n, where each gate computes NAND of two inputs, translates to:

```
gate(a, b) = obs(compose(a, b))
```

A depth-d NAND circuit produces a depth-d nesting of obs(compose(...)):

```
obs(compose(obs(compose(a, b)), obs(compose(c, d))))
```

This is `nestedObsCompose`. The Lean formalization proves:

- **Normalization depth: exactly 2** for all nesting depths d >= 1 (`normDepth_nested_eq_two`)
- **Term size: >= 2^d** (`compounding_size_lower_bound`)

NAND circuits of any depth normalize in 2 passes of deepRewrite.

---

## Part 2: The Depth-Width Tradeoff

### Two extremes, both proved

| Strategy | Term structure | Depth (passes) | Width (term size) | Analogy |
|----------|---------------|-----------------|-------------------|---------|
| Eager (NAND / obs everywhere) | nestedObsCompose | 2 (constant) | >= 2^d (exponential) | Eager evaluation |
| Lazy (observe at end only) | obs(f0Chain k) | k-1 (linear) | polynomial per pass | Lazy evaluation |

The eager strategy resolves all obs simultaneously (deepRewrite goes bottom-up, all obs(compose) sites are visible from the start). The lazy strategy defers obs to the boundary, so each pass creates one new obs(compose) site that must wait for the next pass.

### This is the circuit complexity tradeoff

In circuit complexity, the depth-width tradeoff is fundamental:

- Shallow circuits (low depth) require exponentially many gates (high width)
- Deep circuits (high depth) can be narrow (low width)
- The tradeoff is: parallelism (depth) vs. total work (width/size)

The framework reproduces this tradeoff from the algebra:

- obs at every level = shallow normalization, exponential term size
- obs only at top = deep normalization, moderate term size
- The tradeoff is forced by the Leibniz rule's branching structure

---

## Part 3: JIT Obs Placement

### The idea

Instead of placing obs at every level (eager, exponential size) or only at the top (lazy, linear depth), place obs at strategically chosen intermediate levels. This is "just-in-time" observation: observe only when and where it's useful.

For a compose chain of k atoms, place obs at every j-th level:

```
obs(compose(a_1, compose(a_2, ... obs(compose(a_j, compose(a_{j+1}, ... ))) ... )))
```

This creates ceil(k/j) groups, each containing j atoms in a compose chain. Each group requires j-1 passes to normalize. But groups can potentially be processed in parallel (the obs boundaries separate them).

Expected normalization profile:

| Placement interval j | Groups | Passes per group | Total depth | Term size |
|----------------------|--------|-------------------|-------------|-----------|
| 1 (every level) | k | 0 | 2 | >= 2^k |
| 2 | k/2 | 1 | ~3 | moderate |
| log(k) | k/log(k) | log(k)-1 | ~log(k) | polynomial? |
| k (top only) | 1 | k-1 | k-1 | polynomial |

### The circularity

Optimal obs placement requires knowing which intermediate observations will produce clean eigenvalues (collapsing branches). But determining this requires knowing the result of the observation -- which is the computation you're trying to perform.

```
jitCompose(a, b) = if "obs here would simplify" then obs(compose(a, b))
                   else compose(a, b)
```

The predicate "obs here would simplify" depends on the eigenvalues of a and b, which depend on the specific DynSemiring instance (i.e., the specific assignment for SAT). This is circular: you need the answer to know where to observe, but you need to observe to get the answer.

### The certificate breaks the circularity

A certificate (satisfying assignment) provides exactly the information needed for optimal obs placement:

- For each literal: is it f_0 or z? (eigenvalue known)
- For each clause: does it contain a z? (compose with z collapses to z)
- For each inter-clause boundary: does obs here produce a primitive? (certificate says yes)

With the certificate, you can place obs at exactly the right levels to get constant-depth normalization with polynomial term size. Without it, you must either:

- Go eager (obs everywhere): constant depth, exponential size
- Go lazy (obs at top): linear depth, polynomial size
- Guess a JIT strategy: risk wrong placement, which may create more sites rather than fewer

---

## Part 4: What This Suggests

### The P vs NP structure in the depth-width plane

The framework maps P vs NP onto the depth-width tradeoff:

- **P = polynomial total work.** Either constant depth with polynomial width (efficient parallel), or polynomial depth with polynomial width (efficient sequential). The total work (depth * width) is polynomial.

- **NP-hard = no polynomial total work.** Every obs placement strategy either has exponential width (eager) or linear+ depth with per-pass cost that compounds (lazy). No intermediate strategy achieves polynomial total work without the certificate.

- **Certificate = optimal obs placement.** The certificate is the information that enables a JIT strategy with polynomial total work. It tells you exactly where obs produces clean eigenvalues, avoiding both exponential term size and sequential cascading.

### Formalizable next steps

1. **Define `partialObs j k`**: a compose chain of k atoms with obs placed at every j-th level. Prove normalization depth and term size as functions of j and k.

2. **Prove the tradeoff**: show that depth * term_size is lower-bounded by a function of k that is independent of j. This would formalize the claim that no obs placement achieves polynomial total work.

3. **Prove certificate optimality**: show that with a specific assignment (certificate), obs placement can be chosen to achieve polynomial total work.

---

## Part 5: Certificate Derived from Encoding Analysis

### The reframing

The standard framing treats the certificate as an external object -- a satisfying assignment given to us by an oracle or a lucky guess. But in the eigenvalue framework, the encoding IS the object of study. The term tree is fully visible before any obs fires. The question becomes: **can structural analysis of the encoding itself derive sufficient information for optimal obs placement?**

This shifts the framework from "certificate as input" to "certificate as output of analysis."

### The three-phase process

**Phase 1: Analyze.** Pattern-match on the Term tree. This is purely syntactic -- no obs needed, no Leibniz expansion, no normalization. The analysis extracts:

- Compose nesting depth and shape (how deep, left-nested vs right-nested vs balanced)
- Leaf distribution (where f_0, f_1, z appear in the tree)
- Shared sub-term identification (which sub-terms appear in multiple branches)
- Dependency structure (which compose groups share sub-terms with which other groups)

This is polynomial -- it's tree traversal with bookkeeping. The analysis produces a structural description of the encoding without evaluating it.

**Phase 2: Group.** Based on the structural analysis, partition the term into sub-terms that can be obs'd with minimal cross-group dependency:

- Independent sub-terms (no shared sub-terms) can be grouped separately
- Shared sub-terms create dependencies between groups -- place group boundaries to minimize cross-boundary sharing
- Each group is a compose sub-chain of bounded width

The grouping determines WHERE intermediate obs nodes will be placed. Good grouping = few cross-group dependencies = each group normalizes independently. Bad grouping = many cross-group dependencies = sequential cascading across groups.

**Phase 3: Decode/Unwrap.** Apply obs at group boundaries (the JIT placement), then normalize group by group:

- For each group: apply deepRewrite to resolve the obs(compose) sites within the group
- Propagate results across group boundaries: the eigenvalue output of one group feeds into adjacent groups
- Iterate until all groups are fully normalized

The certificate is not an input to this process -- it is the OUTPUT. The structural analysis determines the obs placement, the obs placement determines the normalization order, and the normalization produces the eigenvalues that would traditionally be called "the certificate."

### What SAT solvers actually do

This three-phase process maps directly onto modern SAT solver techniques:

| Framework phase | SAT solver analogue | Operation |
|-----------------|---------------------|-----------|
| Analyze: identify forced leaves | Unit propagation | Find clauses with single unassigned literal -- its value is forced |
| Analyze: identify shared sub-terms | Variable activity scoring (VSIDS) | Track which variables appear in many clauses -- high-activity variables create the most cross-group dependencies |
| Group: partition by dependency | Clause learning / conflict analysis | Discover which variable groups are tightly coupled and which are independent |
| Decode/Unwrap: obs at boundaries | Decision + BCP | Pick a variable (place obs), propagate forced consequences (normalize the group) |
| Propagate across groups | Implication graph | Eigenvalue from one group constrains adjacent groups |
| Iterate | DPLL/CDCL loop | Repeat until all groups resolved or contradiction found |

The CDCL algorithm IS the JIT obs placement strategy:
- It analyzes the encoding (formula) to identify structural features
- It groups variables by conflict-driven clause learning
- It places obs (makes decisions) based on the analysis
- It propagates (normalizes) and backtracks (undoes obs placement) when the placement creates contradictions

### Why this matters for P vs NP

The question is no longer "does a polynomial-time algorithm exist?" (an existential claim about all possible algorithms). It becomes: **does the structural analysis phase (polynomial-time tree traversal) extract enough information to determine an obs placement that achieves polynomial total normalization work?**

For 2-SAT: **yes.** The implication graph (a polynomial-time structural analysis) determines all forced obs placements. The grouping has no irreducible dependencies -- every shared variable creates a binary implication that resolves in one direction. The JIT strategy finds a certificate (or proves unsatisfiability) in polynomial time.

For 3-SAT: the structural analysis identifies dependencies, but some variables have no forced value -- their obs placement requires a CHOICE. Each choice creates a branching point. If the choice is wrong (leads to contradiction), backtracking undoes the obs and tries the other branch. The number of backtracks determines the total cost.

The P vs NP question in this framing: **for 3-SAT, does every structural analysis strategy require exponentially many backtracks (re-placements of obs) in the worst case?**

### What the framework adds beyond standard complexity theory

Standard complexity theory asks: does a polynomial-time algorithm exist? This is a black-box question about the space of all algorithms.

The framework asks: does polynomial-time structural analysis of the encoding yield sufficient obs placement information? This is a white-box question about the relationship between syntactic structure and normalization cost.

The advantage: the framework constrains WHAT the analysis can extract (structural features of the Term tree) and HOW the analysis helps (obs placement determines normalization regime). This gives a concrete handle for lower bounds: show that no polynomial-time tree traversal can determine an obs placement that avoids exponential total work.

The Leibniz uniqueness result (Part 1 of leibniz-uniqueness.md) already constrains the obs placement: each obs(compose) must expand to the full Leibniz product (both branches). The analysis can determine which branches WILL collapse (because a leaf is z), but only by tracing the dependency chain from leaves to the obs site. For deeply nested dependencies (3-SAT's constraint graph), this tracing may itself require exponential exploration.

---

## Related

- [leibniz-uniqueness.md](leibniz-uniqueness.md) -- Leibniz rule is forced, certificates as pruning
- [encoding-complexity.md](encoding-complexity.md) -- P vs NP as encoding execution problem
- [normalization-depth.md](normalization-depth.md) -- Normalization depth: constant vs linear regimes
- [convergence-and-complexity.md](convergence-and-complexity.md) -- Convergence rate as complexity measure
- [barrier-analysis.md](barrier-analysis.md) -- Barrier analysis for the encoding obstruction

- [leibniz-uniqueness.md](leibniz-uniqueness.md) -- Leibniz rule is forced, certificates as pruning
- [encoding-complexity.md](encoding-complexity.md) -- P vs NP as encoding execution problem
- [normalization-depth.md](normalization-depth.md) -- Normalization depth: constant vs linear regimes
- [convergence-and-complexity.md](convergence-and-complexity.md) -- Convergence rate as complexity measure
- [barrier-analysis.md](barrier-analysis.md) -- Barrier analysis for the encoding obstruction
