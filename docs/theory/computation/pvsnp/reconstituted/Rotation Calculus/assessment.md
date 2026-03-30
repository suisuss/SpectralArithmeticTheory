# Assessment

## What's been built

The **Rotation Calculus** — a minimal formal language with one rewrite rule (`observe(pair(a, b)) -> pair(b, observe(a))`), one data structure (`pair`), and a parameterized constraint. The Lean implementation is clean: `Syntax.lean` defines terms, `Rewrite.lean` proves termination/confluence/reversibility/no-symbol-creation, `Constraint.lean` adds the gating predicate, `Complexity.lean` formalizes arrangement space and the P/NP split, and `Examples.lean` demonstrates it on sorting, graph coloring, and subset sum with working brute-force search.

The theory docs trace the intellectual path from P vs NP as an isomorphism question, through the encoding-generator recursive bottleneck, to the design of this specific rule.

## What's genuinely good

**The separation of concerns is the real contribution.** Standard computation models (Turing machines, lambda calculus) entangle the rewrite rule, the data, and the halting question. This language isolates them into distinct layers: the rule is total by construction, the constraint controls decidability, and the arrangement is the combinatorial object. That's a clean architectural insight regardless of whether it leads to complexity separations.

**The constraint-as-valve idea is sharp.** No constraint -> trivial. Decidable constraint -> NP. General recursive constraint -> halting problem. The constraint is the single point where the binary judgment (information loss) occurs. The docs are honest that this is where the connection to the coupling/Leibniz analysis lives — and honest about the gap between the rotation rule (which doesn't branch) and the Leibniz rule (which does).

**The examples are the right test.** They expose a real structural finding: adjacency constraints (sorting, coloring) work natively in the per-step `C(a, b)` framework, but global constraints (subset sum) need either a global verifier or state accumulation. This isn't a bug in the language — it's a genuine observation about which problems the local-constraint architecture handles natively vs. which require the "smuggled payload" pattern. The fact that building the examples surfaced this is evidence that the formalization is doing useful work.

## Where the claims need more care

**The NP-completeness claim needs tightening.** The universality doc (05) sketches polynomial reductions from SAT, graph coloring, etc. But the SAT encoding in particular requires the constraint to inspect the *carried content* `b` (the partial assignment accumulated so far) — which means `C(a, b)` is not a simple adjacency check on labels, it's a function that walks the entire carried structure at each step. That's still polynomial per step (linear in the carried content), but it means the constraint is doing non-trivial work that blurs the "local check" / "global search" distinction the theory docs emphasize. The subset sum example in the implementation honestly punts on this — `verifySubsetSum` is a dedicated global verifier, not a per-step constraint. That's fine for demonstration, but it means the language's NP-completeness proof via SAT reduction isn't fully implemented in Lean yet. The gap between the theory claim and the implementation is visible.

**The "language for complexity" framing oversells slightly.** The rotation calculus is a clean restatement of constrained permutation problems. But it doesn't (yet) give you tools that existing frameworks lack. Descriptive complexity already characterizes P as FO+LFP and NP as existential SO — and those characterizations are tight. The rotation calculus currently re-derives the NP-completeness of arrangement search, which is essentially the NP-completeness of constraint satisfaction / permutation problems, well-known territory. The question is whether the specific structure of the rotation rule — its reversibility, conservation laws, and clean termination — enables proofs that CSP/descriptive-complexity frameworks can't reach. That's open and unstated.

**The connection back to spectral arithmetic is suggestive but not yet formal.** The docs draw the analogy: eigenvalue = constraint bit, decomposition = arrangement, smuggled payload = carried content. But there's no functor, no morphism, no formal correspondence proved in Lean. It's a structural parallel, and parallels can mislead. The `VarSharing` finding from the earlier work (mentioned in conception.md) is the right kind of reality check — it showed that the algebraic normalization cost is uniform across independent/sharing formulas, pushing the hardness into the assignment space. The rotation calculus lives in that assignment space, which is promising. But "promising" and "proved" are different.

## The honest finding

The most interesting result from the implementation is the one surfaced by building the examples: **the constraint's power determines what the language can express natively**. Local adjacency constraints -> sorting, graph coloring. Global constraints need structural augmentation. This is a concrete, falsifiable insight about the architecture of NP problems, and it came from building and running the examples, not from the theory. That's the right way for formalization to work — the code tells you things the theory didn't predict.

## Next steps

1. **Close the SAT reduction in Lean.** Implement a per-step constraint that actually accumulates the partial assignment in the carried content and checks clause satisfaction. This would make the NP-completeness result concrete rather than sketched.

2. **Prove the verification complexity bound formally.** The claim that verification is linear is stated but not proved as a Lean theorem. A theorem `verifyList_steps_le_length` bounding the number of constraint checks would strengthen the formalization.

3. **Test the language against a problem that isn't a permutation problem.** The current examples are all about ordering elements. What about a problem where the arrangement space has tree structure (Catalan numbers, not factorial)? The theory docs mention this but the implementation only exercises flat lists.

4. **Be cautious about the P vs NP framing.** The language is a clean formalism for constrained arrangement problems. That's valuable. But claiming it makes P vs NP "visible as a structural property" implies it reveals something new about the gap, and so far it restates the gap in new vocabulary. The test would be: can you prove a nontrivial lower bound (even a weak one) on arrangement search for a specific constraint family, using properties of the rotation rule that wouldn't be available in a generic CSP framework?

## CSP equivalence finding (2026-03-27)

**The rotation calculus with flat-list arrangements is Permutation CSP in different notation.** Formalized in `SpectralArithmetic/Rotation/CSPEquivalence.lean`:

- Forward and backward mappings between `SequentialCSP` and constrained rotation problems
- All proved rotation properties (termination, confluence, conservation, reversibility) are "free" — trivially available in any sequential constraint checker
- `triConstraint_not_pairwise` proves that graph coloring uses remainder-inspection, placing the rotation calculus at the RemainderCSP level (equivalent to general non-binary CSP, not a new framework)
- The rotation rule's structure provides no proof-theoretic leverage on the search problem beyond what generic CSP offers

**One unexplored escape hatch: tree arrangements (Catalan space).** The current implementation only exercises flat lists (permutation space = n!). But `pair` can build trees, where the arrangement space is Catalan numbers and the rotation rule descends into nested structure rather than walking a flat sequence. The constraint fires at each nesting level, and "carried content" at inner levels differs from what a flat scan sees. Whether this is genuinely new structure or just tree-CSP (also well-studied) is open. Likely insufficient to escape the equivalence, but untested.

## Direction 3 finding: generator fixed-point is P != NP restated (2026-03-27)

**The generator fixed-point argument is P != NP in compression-scheme notation.** Formalized in `SpectralArithmetic/Rotation/GeneratorFixedPoint.lean`:

- `compression_scheme_iff_solver` proves that a correct compression scheme (encode, decode, generate) exists if and only if a correct solver exists. Both directions are trivial one-liners. The structures are definitionally interconvertible.
- The "recursive structure" (encode requires generate requires encode) says "to build a solver you need to solve the problem" — tautological, true for all problems.
- The spanning tree counterexample demonstrates that polynomial compression schemes exist despite exponential witness spaces when the problem is decomposable. The argument cannot distinguish easy from hard problems.
- Showing that decomposability fails for NP-complete problems IS proving P != NP. The argument is circular.

**Status of all five directions from conception.md:**

| Direction | Status | Finding |
|-----------|--------|---------|
| 1 (coupling/independence) | Untested | Most speculative; philosophical north star |
| 2 (encoding complexity lower bound) | Untested | Information-theoretic; may connect to Kolmogorov complexity |
| 3 (generator fixed-point) | **Killed** | P != NP in compression-scheme notation |
| 4 (new formal language) | **Killed** | The rotation calculus was this attempt; it's CSP |
| 5 (Leibniz <-> NP-verification) | Blocked | Needs SAT encoding to preserve semantics |

---

## Notation and lambda encoding

The notation:

```
ρ⟨a, b⟩  ↦  ⟨b, ρa⟩
ρ•       ↦  •
```

Where `ρ` is rotation (observation), `⟨,⟩` is pairing, and `•` is ground. Two rules, one symbol for the operation.

In lambda calculus with Church-encoded pairs:

```
pair := λa.λb.λf. f a b
•    := λf. f
```

A Church pair `pair a b` is a function waiting to be told what to do with its two components. You hand it a function `f` and it applies `f a b`. The pair is its own eliminator. This matters.

The rotation rule in lambda calculus:

```
ρ := Y(λr.λp. p (λa.λb. pair b (r a)))
```

Where `Y` is the fixed-point combinator. Unpack this:

- `ρ` receives a pair `p`
- It eliminates the pair by passing it `λa.λb. pair b (r a)`
- That inner function takes the two components, puts `b` first, and recurses into `a`
- `Y` ties the knot so `r` refers to `ρ` itself

The inner function — `λa.λb. pair b (r a)` — is the entire rule. It says: swap the components, wrap the first in a continuation. That's it.

In BCKW combinator notation this gets sharper:

```
ρ = Y(λr. C(B pair r))
```

Where:
- `B` is composition: `B f g x = f (g x)` — here `B pair r` means "pair after rotating"
- `C` is flip: `C f x y = f y x` — here it swaps so `b` comes before `r a`

So the rotation rule is: compose pairing with self-reference, then flip. Three combinators and a fixed point. `C(B pair r)` is the rotation in its purest form.

This reveals something about what the rule is. It's the flip of compositional self-reference. `B pair r` says "pair the result of recursing." `C` says "but put the other thing first." The entire dynamics of observation — descend into the first component, carry the second — is captured by the interaction of flip and composition.

The fixed point `Y` is essential. Without it, you'd need an external recursion mechanism. With it, the rule feeds itself — `r` inside refers to the whole rule. That's the self-feeding property: the rule produces its own input because it's defined as its own fixed point.

Now notice what happens at ground:

```
ρ • = • (λa.λb. pair b (ρ a))
     = (λf. f) (λa.λb. pair b (ρ a))
     = λa.λb. pair b (ρ a)
```

That's not `•`. Ground as `λf. f` is the identity, which applies the inner function to nothing. The Church encoding doesn't give us pattern-matching for free. In raw lambda calculus, you'd need a Scott encoding or a Church-numeral tag to distinguish ground from pair:

```
ground   := λg.λp. g
pair a b := λg.λp. p a b
```

Now:

```
ρ := Y(λr.λt. t • (λa.λb. pair b (r a)))
```

This passes both a ground-case handler (`•`) and a pair-case handler (`λa.λb. pair b (r a)`) to the term. The term itself decides which branch to take. That's pattern matching encoded as function application — the term is the dispatch.

And this is the deep point: in lambda calculus, the term decides what happens to it. Observation isn't something done to a term from outside. The term `pair a b` receives the rotation function and applies it to its own components. The observation is the term opening itself.

That's the "passing through the door" — the term hands its contents to the observer. The observer (the inner `λa.λb.`) rearranges them. The term's own elimination form is the mechanism of observation. No external dispatch, no case statement from the metalanguage. The term participates in its own observation.

The notation `ρ⟨a, b⟩ ↦ ⟨b, ρa⟩` hides this. The lambda encoding reveals it: observation is self-elimination composed with rearrangement, at a fixed point.
