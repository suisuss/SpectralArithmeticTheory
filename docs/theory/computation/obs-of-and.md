# Observation of AND: A Research Program

## The Metatheoretic Nature of P vs NP

Every major structural insight about P vs NP has been metatheoretic — a statement about proof techniques, not a direct proof:

| Result | Year | What it says | Level |
|--------|------|-------------|-------|
| Relativization | 1975 | Black-box proofs can't resolve P vs NP | Meta: constrains proof technique |
| Natural proofs | 1997 | Large constructive combinatorial proofs can't prove circuit lower bounds | Meta: constrains proof technique |
| Algebrization | 2009 | Arithmetize-and-relativize proofs can't resolve P vs NP | Meta: constrains proof technique |

The direct results (IP = PSPACE, circuit lower bounds for AC0, monotone circuit lower bounds) all work within specific models and prove specific separations — but none resolve P vs NP. They succeed precisely where the barriers permit, and stop precisely where the barriers block.

A resolution of P vs NP must simultaneously be:
- Non-relativizing (can't treat computation as black box)
- Non-naturalizing (can't use large constructive truth-table properties)
- Non-algebrizing (can't just arithmetize and relativize)

Constructing such a proof requires understanding *why* each barrier exists and deliberately transcending all three. This is inherently metatheoretic — you must reason about the structure of proofs, not just about computations.

The derivation barrier proposed in [derivation-barrier.md](derivation-barrier.md) would add a fourth constraint: non-derivation-based. Any proof must also avoid relying on derivation-based algebraic observation over commutative algebras.

---

## The Core Insight: Observation vs Computation

There is a fundamental distinction between:

1. **Computing AND**: Given inputs a, b in {0,1}, output a * b. This is trivial — one multiplication, constant time.

2. **Observing AND**: Given an algebraic term representing AND(a,b), apply an observation operator and measure the resulting term structure. This is where indistinguishability arises.

The DynSemiring result says: when you represent AND as compose and apply obs (a derivation), the resulting term structure cannot distinguish satisfying from unsatisfying assignments under any scalar measure. You can compute AND, but you cannot *observe the process of computing AND* through a derivation and extract satisfiability.

This distinction — between what you can compute and what you can observe about computation — is the gap that the derivation barrier exploits.

### Why this matters

P vs NP is not asking "can you compute AND?" It's asking "can you efficiently determine whether a composition of ANDs, ORs, and NOTs is satisfiable?" The key word is *determine* — it's an observational question about a compositional structure.

Any algorithm that solves SAT must, at some level:
1. Represent the boolean formula (encoding)
2. Perform operations on the representation (execution)
3. Extract the answer from the result (observation)

Steps 1 and 2 are the computation. Step 3 is the observation. The derivation barrier says: if step 3 uses a derivation on a commutative algebra, and the answer is extracted via scalar measures, then step 3 fails.

---

## Obs of AND: The Formal Target

### What we know

In the DynSemiring term algebra, AND is represented as compose (multiplication). When obs is applied:

```
obs(compose(a, b)) = oplus(compose(obs(a), b), compose(a, obs(b)))
```

This is the Leibniz rule — the product rule of differentiation applied to AND. It decomposes the observation of a product into a sum of two terms, each involving the observation of one factor.

The key properties:
- **Proliferation**: One AND becomes two terms (oplus creates a sum)
- **Commutativity**: compose(a,b) = compose(b,a), so argument order is invisible
- **Annihilation**: obs(f_0) = z — TRUE is killed by observation
- **Eigenstate**: obs(f_1) = f_1 — the FALSE-encoding generator is fixed

Together, these ensure that after iterated obs application, the term structure depends only on symmetric properties of the input (like the count of true variables), never on which specific variables are true — which is exactly the information needed to determine satisfiability.

### What we need to prove

**Theorem (Obs-of-AND indistinguishability)**: Let (A, ., D, +) be a commutative differential algebra. Let e be the multiplicative identity and g an eigenstate of D (D(g) = lambda . g). Define:

- TRUE = e (identity element)
- FALSE = any element with D-image proportional to itself
- AND(a,b) = a . b (multiplication)

Then for any SAT formula phi, any encoding of phi's variables as TRUE/FALSE, and any scalar measure mu that is additive over +, the value mu(D^n(encode(phi))) depends only on the multiset of variable assignments, not on which variables are assigned which values.

**Corollary**: Since SAT and UNSAT assignments can share the same multiset statistics (e.g., same number of TRUE variables), mu cannot separate SAT from UNSAT.

### What this would establish

If the theorem holds for the abstract class of commutative differential algebras (not just the DynSemiring), then:

1. It's not about one specific algebra — it's about the *structure* of derivations
2. Any approach that represents AND as multiplication in a commutative algebra and observes via derivation is blocked
3. The barrier is determined by three things: the algebraic representation of AND, the Leibniz rule, and commutativity

### The OR and NOT question

AND alone doesn't produce SAT — you also need OR and NOT. In the current encodings:

**DynSemiring (Church encoding)**:
- OR(p,q) = p TRUE q = compose(compose(p, TRUE), q) — nested composition
- NOT(p) = p FALSE TRUE = compose(compose(p, FALSE), TRUE) — nested composition
- Everything reduces to compose. OR and NOT are derived from AND + variable selection.

**Polynomial arithmetization**:
- AND(a,b) = a * b (multiplication)
- OR(a,b) = a + b - a * b (addition and multiplication)
- NOT(x) = 1 - x (subtraction)
- OR introduces addition directly, not through composition.

The polynomial result (count1 separates) shows that AND-as-multiplication + OR-as-addition does NOT produce total indistinguishability. What matters is the observation mechanism: polynomial constant folding preserves leaf values, while obs/Leibniz transforms them.

So the obs-of-AND theorem must account for how OR and NOT are encoded. In Church-encoded form (everything is compose), the theorem is about obs of nested compose — which IS the Leibniz rule applied iteratively. In polynomial form, OR introduces addition, which obs handles differently.

The cleanest approach: prove the theorem for the Church encoding where everything is compose, since that's where total indistinguishability was observed.

---

## The Research Program

### Phase 1: Abstract the DynSemiring result

**Goal**: Identify exactly which axioms of the DynSemiring are used in the indistinguishability proof, and show they're consequences of the abstract commutative differential algebra axioms.

**Method**: Re-examine the Lean proofs of SAT indistinguishability. Each `native_decide` proof computes a specific value. The underlying mechanism is:
- obsRewrite applies Leibniz to decompose compose into oplus
- iterDeepRewrite applies this at increasing depth
- The resulting term is measured by counting node types

What properties of obsRewrite/iterDeepRewrite are essential? Which are accidental to the specific encoding?

**Deliverable**: A minimal set of abstract axioms from which indistinguishability follows.

### Phase 2: Prove for the abstract class

**Goal**: Prove the obs-of-AND theorem for all commutative differential algebras satisfying the minimal axioms from Phase 1.

**Method**: Work abstractly in Lean. Define a typeclass for commutative differential algebras with eigenstate. Prove that for any instance, the iterative application of the derivation to Church-encoded boolean formulas produces terms whose scalar measures depend only on the multiset of variable assignments.

**Key challenge**: The current proofs use `native_decide` on concrete terms. An abstract proof would need structural induction over the term algebra, which is substantially harder.

**Deliverable**: A Lean theorem parameterized over the algebra, not specific to the DynSemiring.

### Phase 3: Characterize the encoding freedom

**Goal**: Determine whether the indistinguishability holds for ALL encodings of booleans, or only for eigenvalue-compatible encodings (TRUE = identity, FALSE = eigenstate).

**Method**: Systematically test alternative encodings:
- TRUE = g^2, FALSE = g^3 (higher eigenstates)
- TRUE = e + g, FALSE = e - g (superpositions)
- TRUE and FALSE as non-eigenstates

If indistinguishability holds for all encodings: the barrier is about the algebra, not the encoding. If it breaks for some encoding: the barrier has an escape route, and the encoding constraint must be part of the theorem statement.

**Deliverable**: Either a universal theorem (all encodings) or a precise characterization of which encodings are covered.

### Phase 4: Relate to existing barriers

**Goal**: Determine whether the derivation barrier is independent of relativization, natural proofs, and algebrization.

**Method**:
- Show a concrete example of a technique that algebrizes but is NOT derivation-based (exists trivially: polynomial identity testing)
- Show a concrete example of a technique that IS derivation-based but does not algebrize (this is the hard direction — requires understanding algebrization at a technical level)
- If both examples exist: the barriers are independent
- If every derivation-based technique algebrizes: the derivation barrier is subsumed

**Deliverable**: A formal relationship between the derivation barrier and algebrization.

### Phase 5: The metatheoretic synthesis

**Goal**: If the derivation barrier is independent: add it to the list of constraints that any P vs NP proof must satisfy. Map the remaining "allowed" proof space — what techniques survive all four barriers simultaneously?

**Method**: Characterize the intersection of non-relativizing, non-naturalizing, non-algebrizing, and non-derivation-based techniques. Identify whether any known approach lives in this intersection.

**Deliverable**: A map of the constrained proof landscape for P vs NP.

---

## Why This Might Work

The existing barriers each exploit a specific symmetry:
- Relativization: oracle symmetry (oracles can simulate anything)
- Natural proofs: pseudorandom symmetry (hard functions look random)
- Algebrization: algebraic extension symmetry (low-degree extensions preserve algebraic properties)

The derivation barrier exploits **Leibniz symmetry**: the product rule treats both factors symmetrically (D(ab) = D(a)b + aD(b) is symmetric in the roles of "differentiated" and "preserved"), and commutativity ensures ab = ba. This double symmetry erases the directional information that encodes which-variables-are-true.

This is a different symmetry from the other three. Relativization is about input/output symmetry. Natural proofs are about statistical symmetry. Algebrization is about polynomial-extension symmetry. Leibniz symmetry is about the product rule's symmetric treatment of factors in a commutative algebra.

If these symmetries are genuinely independent, then the derivation barrier contributes new information to the P vs NP landscape.

## Why This Might Not Work

**The scope might be too narrow.** Commutative differential algebras with eigenstate-compatible encodings and additive scalar measures is a very specific setting. If the barrier only rules out approaches that nobody would have tried anyway, it's technically correct but practically irrelevant.

**The encoding freedom might kill it.** If there exists a clever encoding of booleans into a commutative differential algebra such that some scalar measure of derivation-normalized terms separates SAT from UNSAT, the barrier fails. The encoding is the weakest link — it's where a counterexample would likely live.

**It might be subsumed.** If every derivation-based observation technique turns out to algebrize, then algebrization already covers this and the derivation barrier adds nothing new. The independence question (Phase 4) is critical.

**The metatheoretic approach has no track record of resolving P vs NP.** Barriers constrain the search space but don't produce solutions. Adding a fourth barrier to three existing ones might further constrain the space without bringing a resolution closer. The value depends on whether the remaining space contains viable approaches.
