# Trees, Branching, and the Structure of Complexity

## 1. The Rewrite Rule as Lambda Expression

### Notation

The rotation rule has a minimal notation:

```
ρ⟨a, b⟩  ↦  ⟨b, ρa⟩
ρ•       ↦  •
```

Where `ρ` is rotation (observation), `⟨,⟩` is pairing, and `•` is ground. Two rules, one symbol for the operation.

### Lambda calculus encoding

Using Scott-encoded pairs (which support pattern matching):

```
ground  := λg.λp. g
pair a b := λg.λp. p a b
```

A term decides its own elimination. `ground` takes the ground-case handler. `pair a b` takes the pair-case handler and applies it to its components. The term IS its own dispatch.

The rotation rule:

```
ρ := Y(λr.λt. t • (λa.λb. pair b (r a)))
```

Where `Y` is the fixed-point combinator. Unpacking:

- `ρ` receives a term `t`
- It passes `t` two handlers: `•` for the ground case, and `λa.λb. pair b (r a)` for the pair case
- The pair handler takes the two components, puts `b` first, and recurses into `a`
- `Y` ties the knot so `r` refers to `ρ` itself

### Combinator form

In BCKW combinator notation:

```
ρ = Y(λr. C(B pair r))
```

Where:
- `B` is composition: `B f g x = f (g x)` — here `B pair r` means "pair after rotating"
- `C` is flip: `C f x y = f y x` — swaps so `b` comes before `r a`

The rotation rule is: **compose pairing with self-reference, then flip**. Three combinators and a fixed point.

### What the lambda encoding reveals

In lambda calculus, the term decides what happens to it. Observation isn't something done to a term from outside. The term `pair a b` receives the rotation function and applies it to its own components. The observation is the term opening itself.

This is the "passing through the door" — the term hands its contents to the observer. The observer (the inner `λa.λb.`) rearranges them. The term's own elimination form is the mechanism of observation. No external dispatch, no case statement from the metalanguage. The term participates in its own observation.

The notation `ρ⟨a, b⟩ ↦ ⟨b, ρa⟩` hides this. The lambda encoding reveals it: observation is self-elimination composed with rearrangement, at a fixed point.

### The fixed point is essential

Without `Y`, you'd need an external recursion mechanism. With it, the rule feeds itself — `r` inside refers to the whole rule. That's the self-feeding property: the rule produces its own input because it's defined as its own fixed point.

The ground state `ρ• = •` is where the recursion bottoms out. The term that can't be opened. The fixed point of observation itself.

---

## 2. Two Structural Dimensions of Trees

A flat list has one structural dimension: **order**. Given n elements, you choose a permutation. That's n! arrangements. The constraint checks adjacent pairs. The search space is the symmetric group S_n.

A tree has two structural dimensions: **shape** and **placement**. Given n elements, you first choose a binary tree shape (Catalan(n) options), then place elements at the leaves (n! options). The constraint checks at every internal node — every `pair` constructor. The search space is the product of the Catalan space and the symmetric group.

### The interaction between shape and placement

These two dimensions interact. The tree shape determines which pairs of elements are compared by the constraint.

In a flat list, element i is always compared with element i+1. The adjacency structure is fixed — it's always a path graph. The constraint fires on a predetermined set of pairs.

In a tree, the constraint fires on pairs determined by the tree shape:
- Balanced: `pair(pair(a,b), pair(c,d))` compares `{a,b}` at one level, `{c,d}` at another, and `{pair(a,b), pair(c,d)}` at the root
- Unbalanced: `pair(a, pair(b, pair(c, d)))` compares `{c,d}`, then `{b, pair(c,d)}`, then `{a, rest}`

Different groupings, different constraint checks. The tree shape is a **strategy for decomposing the problem**. Choosing a tree shape is choosing how to partition the elements into subproblems. Choosing the leaf placement is solving each subproblem. The two choices are coupled — a good partition depends on which elements are in each group.

### Trees as algorithms

This is exactly what divide-and-conquer algorithms do:
- Merge sort chooses a balanced partition and solves recursively
- Quicksort chooses a pivot (unbalanced partition) and solves recursively
- The tree shape IS the algorithm
- The leaf placement IS the solution

---

## 3. Subtree Independence and Factorization

### The key property: subtree independence

For flat lists, the search space is n! and its structure is simple — the symmetric group is well-understood. For trees, the search space is Catalan(n) x n!, but the structure is hierarchical. Hierarchical search spaces have a property that flat ones don't: **subtree independence**.

If the constraint is local — if checking `pair(a, b)` depends only on properties of `a` and `b`, not on their position in the larger tree — then subtrees can be solved independently. Solve the left subtree, solve the right subtree, check the root constraint. The search factorizes.

For a balanced tree of depth d with n = 2^d leaves: instead of searching n! arrangements, you search 2 x (n/2)! at each level, for d levels. That's roughly (n/2)!^2 x checking, which is exponentially smaller than n!. The tree structure reduces the effective search space by enabling factorization.

This is why tree decomposition is powerful in constraint satisfaction — **treewidth** bounds the factor by which the search space can be decomposed. Low treewidth means the problem factorizes well. High treewidth means it doesn't.

### Folds vs catamorphisms

When you verify a flat list arrangement, each constraint check sees the current element and the entire remaining list. The "remaining list" changes at each step — it's state that threads through the whole verification. The constraint checks are coupled through this shared state.

When you verify a tree arrangement, each constraint check at an internal node sees only its two children. The children's subtrees are separate. The constraint at the left subtree doesn't see the right subtree. There's no shared threading state — just local checks that compose upward.

The difference is exactly the difference between:
- A **fold** (sequential accumulation) — threads state, inherently sequential
- A **catamorphism** (recursive decomposition) — decomposes independently, inherently parallel

### P as efficient catamorphism

Problems in P have efficient catamorphisms — you can decompose them into independent subproblems, solve each, and combine. The combination step is polynomial. Merge sort: split, sort halves independently, merge. The tree structure IS the algorithm.

NP-complete problems resist catamorphism. For SAT: you can't split the variables into two groups, solve each independently, and combine. The clauses create dependencies between variables that cross any partition. No tree decomposition makes the subtrees independent. You're forced back to sequential search — a fold over the entire space.

---

## 4. Trees Are What Complexity Measures

### The claim

Trees aren't just fundamental to complexity — **trees are what complexity measures**. The complexity of a problem is the minimum depth of the shallowest tree that captures its decision structure.

- **P** is shallow trees (polynomial depth)
- **NP** is deep trees (exponential depth, or problems that resist tree decomposition entirely)

### Every computation branches

Every computation that makes a decision branches. An `if` statement has two paths. A pattern match has n paths. A recursive call on a subproblem creates a subtree of the computation. The trace of any computation is a tree — not because we choose to represent it that way, but because decision and decomposition are inherently branching operations.

A sequence is a degenerate tree. A flat list is a tree where every node has exactly one child. When we say a computation is "sequential" we mean its trace is a path — a tree of depth n and width 1. When we say it's "parallel" we mean its trace is a tree of depth log(n) and width n. The complexity difference between sequential and parallel is the difference between deep-narrow trees and shallow-wide trees. Same structure, different shape.

### The rotation rule on trees vs lists

On a flat list, the rule walks a path: observe one element, carry the rest, repeat. Linear depth, no branching.

On a tree, the rule descends into subtrees: observe a node, its left child is next, its right child is carried. The rule naturally follows the tree's branching structure.

The constraint at each node is a decision. Pass or fail. That's a branch in the meta-computation of verification.

For a flat list, the decisions are chained — each depends on the previous.

For a tree, the decisions at sibling subtrees are independent. Independent decisions can be made separately. Dependent decisions must be made in sequence.

### The fundamental distinction

**P is the class of problems where decisions can be organized into a tree of polynomial depth with independent subtrees. NP is the class where decisions are entangled — no tree organization makes them independent.**

### Treewidth as the measure

This is what treewidth measures. A constraint graph with treewidth k can be decomposed into a tree where each node involves at most k variables. If k is bounded, the catamorphism works — you solve bags of k variables independently and combine. Polynomial. If k grows with n, the decomposition fails. Exponential.

---

## 5. P vs NP as Tree Depth

### Restating the question

P vs NP, in tree terms:

**P = NP** would mean: for every NP problem, there exists a tree decomposition of polynomial depth where the subtrees are independent enough to solve the subproblems efficiently. Every constraint factorizes over some tree shape.

**P != NP** would mean: there exist constraints whose dependency structure resists all tree decompositions. No tree shape makes the subtrees independent. The decision structure is inherently deep/entangled.

### Certificates as paths through the tree

A certificate is a path through the exponential computation tree — it says "go left here, right there." Verification follows the path, checking each node. The path has polynomial length (the tree has polynomial depth along any root-to-leaf path, by the NP definition).

Search must find the path without knowing which branches to take. The branching IS the hardness.

### The Leibniz rule connection

The Leibniz rule in the spectral arithmetic framework:

```
obs(compose(a,b)) → compose(obs(a), b) ⊕ compose(a, obs(b))
```

This is a branching rule. One observation becomes two. The tree it generates is the computation tree. The depth of that tree is the complexity.

The rotation rule on flat lists doesn't branch — it's linear. On trees, it follows existing branches. The rule itself doesn't create complexity. The tree structure carries the complexity. The rule reveals it.

---

## 6. The Rotation Rule on Trees

### What the tree arrangement investigation showed

Using the same rotation rule `observe(pair(a,b)) → pair(b, observe(a))` on tree-structured terms:

1. **Same constraint, different behavior on trees vs flat lists.** A balanced partition constraint is vacuous on flat lists (the balance check never fires because the first element is always a leaf). On trees, it's substantive — only specific groupings pass.

2. **The search space is different.** Flat lists search over n! permutations. Trees search over Catalan(n) x n! (tree shapes x leaf placements). The 4-element example shows 120 total tree arrangements vs 24 flat permutations.

3. **Multi-level constraints work natively.** A deep balanced tree `((1,8),(5,4)) | ((2,7),(3,6))` passes checks at every level (18 vs 18, then 9 vs 9 at each subtree). This is a hierarchical decomposition problem — the constraint fires at every level of a chosen tree. Not expressible as flat-list CSP.

4. **The rotation rule is unchanged.** The same rule gains new power because `a` can be a compound subtree. The expressiveness comes from the data structure, not a new rule.

### The data structure matches the computation

The key observation: for tree arrangements, the verification structure matches the problem structure. If the problem is inherently hierarchical (balanced partitioning, recursive decomposition, divide-and-conquer), then the tree arrangement expresses it natively. The flat list forces every hierarchical problem into a sequential encoding, which destroys the factorization.

The rotation rule on trees is a **recursive verifier**. It checks the root, then recurses into subtrees.

On flat lists, it's a **sequential verifier**. The same rule, but the data structure determines whether verification exploits hierarchical structure.

---

## 7. Implications for the Formal Language

If complexity IS tree structure, then a formal language for complexity needs to talk about trees natively. Not lists that simulate trees. Not abstract measures of resource consumption. Trees — their depth, their branching factor, the independence of their subtrees, the factorizability of constraints over their nodes.

The rotation calculus on tree-structured terms is closer to this than the flat-list version, because the data structure matches the computational structure.

### What the language needs to formalize

1. **Tree depth as complexity measure.** The minimum depth tree over which a constraint factorizes = the problem's inherent complexity.

2. **Subtree independence as the tractability criterion.** A constraint is "easy" when it decomposes over subtrees. "Hard" when it entangles them.

3. **Treewidth as a structural parameter.** The minimum width of the bags in a tree decomposition = how much entanglement the constraint forces.

4. **The factorization gap.** The ratio between brute-force search (Catalan(n) x n!) and factorized search (product of subtree searches) = the computational advantage of finding the right tree shape.

### The open question

For NP-complete problems, does there exist a tree shape where the constraint factorizes? The hardness of a specific instance is the degree to which its constraint resists hierarchical decomposition — the degree to which no tree shape makes the subtrees independent.

This is a concrete, structural characterization of hardness. Not "how many steps does a machine take" but **"how well does this constraint factorize over tree shapes."**

---

## 8. The Hierarchy

Putting it together:

| Level | Structure | Search space | Verification | Factorization |
|-------|-----------|-------------|--------------|---------------|
| Flat list | Path (degenerate tree) | n! permutations | Sequential fold | None — checks are chained |
| Tree | Binary tree | Catalan(n) x n! | Recursive catamorphism | Subtree independence |
| Bounded treewidth | Tree with bounded bags | Polynomial | Catamorphism with bounded state | Partial — bags have bounded coupling |
| Unbounded treewidth | Graph (no tree structure) | Exponential | Sequential over the graph | None — full entanglement |

P lives at "bounded treewidth" — the constraint has enough tree structure to factorize efficiently. NP-complete lives at "unbounded treewidth" — the constraint's dependency graph resists all tree decompositions.

The rotation calculus, by operating directly on tree-structured terms, makes this hierarchy a property of the terms themselves rather than a meta-theoretic analysis. The tree is not an external tool applied to analyze the problem. The tree IS the problem, the algorithm, and the solution simultaneously.
