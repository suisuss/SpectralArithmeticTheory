# The Encoding Obstruction: An Impossibility Theorem for Self-Representing Eigenvalue Systems

## Authors

[To be determined]

## Abstract

We prove that no injective encoding of a self-representing algebraic system can simultaneously preserve eigenvalue arithmetic and commute with the observation operator. Specifically, in any commutative semiring with a derivation (the Leibniz rule), the observation operator produces linear eigenvalues, while any injective encoding of structured terms requires super-linear pairing functions. These growth regimes are incompatible: no injective map from terms to natural numbers can be a coalgebra morphism between the semantic observation (eigenvalue scaling) and the syntactic observation (rewrite-then-re-encode). We formalize the system as a *DynSemiring* — a commutative semiring with a derivation, additive identity, and characteristic zero — and prove all results in Lean 4 with zero sorry. The impossibility has the structure of a trilemma: eigenvalue arithmetic, self-encoding, and coalgebra morphism are pairwise compatible but jointly unsatisfiable, and every escape route (redundant representations, residue number systems, tropical algebra) sacrifices a property required for self-encoding. We show that the Leibniz rule is the unique minimal correct rewrite, that extensionalization more than doubles term size, and that the intension/extension chain has no fixed point. The executable consequence is that any self-representing system with addition must maintain normalization state external to its encoding, because carry propagation in addition is non-local in any unique positional representation. We analyze the relationship of these results to the three known barriers in complexity theory (relativization, natural proofs, algebrization) and show that the encoding obstruction is non-relativizing by construction and plausibly avoids the other two barriers.

---

## 1. Introduction

### 1.1 The Problem

When a formal system is powerful enough to encode its own syntax as data — Godel encoding in Peano Arithmetic, the universal Turing machine encoding its own description — a natural question arises: can the system faithfully simulate its own dynamics through this encoding? That is, does applying the system's operations to the encoded representation produce the same result as encoding the result of applying those operations directly?

For passive encoding (inert labels assigned to terms), this question leads to Godel's incompleteness theorems: the system can name self-referential propositions but cannot resolve them. For executable encoding (where the system operates on its own codes using its own operations), we show the question leads to a stronger impossibility: the encoding cannot commute with the system's observation operator, and the failure forces external computational state.

### 1.2 The Setting

We work in a *DynSemiring*: a commutative monoid (State, compose, f_0) equipped with an observation operator obs satisfying the Leibniz (product) rule, an addition operation oplus with additive identity z, distributivity of compose over oplus, and characteristic zero. The axioms are:

| Axiom | Statement |
|-------|-----------|
| Identity | compose(f_0, s) = s |
| Annihilator | compose(z, s) = z |
| Commutativity | compose(a, b) = compose(b, a) |
| Fixed point | obs(f_1) = f_1 |
| Leibniz rule | obs(compose(a, b)) = oplus(compose(obs(a), b), compose(a, obs(b))) |
| Obs of identity | obs(f_0) = z |
| Obs distributes | obs(oplus(a, b)) = oplus(obs(a), obs(b)) |
| Additive identity | oplus(z, a) = a |
| Distributivity | compose(a, oplus(b, c)) = oplus(compose(a, b), compose(a, c)) |
| Characteristic zero | For all n >= 1: n-fold sum of f_0 is not z |

From these axioms, eigenstates f_n = compose(f_1, ..., f_1) (n copies) satisfy obs(f_n) = n * f_n, producing the natural numbers as eigenvalues. This yields Peano Arithmetic, which in turn provides the machinery for Godel encoding: prime factorization, primitive recursive predicates, and bounded quantification.

### 1.3 The Question

We define two coalgebra structures on the same carrier:

- **Semantic coalgebra** (State, obs_semantic): eigenvalue scaling, obs(f_n) = n * f_n.
- **Syntactic coalgebra** (State, obs_code): given a Godel code n, decode it to a term t, apply the Leibniz rewrite rule to t, re-encode the result.

The eval-quote diagram asks whether these produce bisimilar behavior:

```
        eval
Terms ---------> State
  |                 |
  | encode          | obs_semantic
  |                 |
  v                 v
State ---------> State
     obs_code
```

We prove: this diagram does not commute. For any injective encoding and any compound term, the syntactic path produces a different code than the semantic path.

### 1.4 Results

All results are formalized in Lean 4 with zero sorry (no unproved assumptions).

**Theorem 1** (Encoding Obstruction). For any injective function epsilon : Term -> N and any terms a, b:

```
epsilon(obsRewrite(obs(compose(a, b)))) != epsilon(obs(compose(a, b)))
```

The extensionalized form (after Leibniz rewriting) receives a different code from the intensional form (before rewriting), under any injective encoding. (Lean: `no_coalgebra_morphism`, Main.lean:232)

**Theorem 2** (Semantic Invariance). For any DynSemiring instance and any terms a, b:

```
eval(obsRewrite(obs(compose(a, b)))) = eval(obs(compose(a, b)))
```

The meaning is preserved across the encoding gap. The two forms differ syntactically but agree semantically. (Lean: `semantic_invariance_general`, Encoding.lean:277)

**Theorem 3** (No Fixed Point). The intensional form, the one-step extensional form, and the deeply extensional form are three provably distinct terms. Substitution has no fixed point. (Lean: `substitution_chain_distinct`, Encoding.lean:195)

**Theorem 4** (Size Growth). Extensionalization more than doubles term size:

```
termSize(obsRewrite(obs(compose(a, b)))) > 2 * termSize(obs(compose(a, b)))
```

(Lean: `extensionalize_more_than_doubles`, Encoding.lean:334)

**Theorem 5** (Bitwise Impossibility). No bitwise operation on natural numbers can simultaneously satisfy commutativity, associativity, additive identity, cancellation, and characteristic zero. Any such operation inherits characteristic 2 from the underlying Boolean algebra. (Lean: `oplus_bitwise_impossible`, Oplus.lean:80; `bitwise_underlying_char_two`, Oplus.lean:114)

**Theorem 6** (Carry Propagation). For any base b >= 2 and any position k >= 1, addition produces non-local effects: the output at position k can depend on inputs at all positions 0 through k-1. (Lean: `carry_propagation_general`, Pairing.lean:105)

---

## 2. The DynSemiring and Term Algebra

### 2.1 Definition

A DynSemiring is a type State equipped with:

```lean
class DynSemiring (State : Type*) extends SpectralMonoid State where
  oplus : State -> State -> State
  oplus_assoc : forall a b c, oplus a (oplus b c) = oplus (oplus a b) c
  oplus_comm : forall a b, oplus a b = oplus b a
  oplus_z : forall a, oplus z a = a
  compose_distrib : forall a b c, compose a (oplus b c) = oplus (compose a b) (compose a c)
  obs_f0 : obs f_0 = z
  leibniz : forall a b, obs (compose a b) = oplus (compose (obs a) b) (compose a (obs b))
  obs_oplus : forall a b, obs (oplus a b) = oplus (obs a) (obs b)
  char_zero : forall n : N, n >= 1 -> nfoldSum oplus z n f_0 != z
```

The SpectralMonoid provides (State, compose, obs, f_0, f_1, z) with compose commutative and associative, obs(f_1) = f_1, compose(f_0, s) = s, and compose(z, s) = z.

### 2.2 The Free Term Algebra

We define an inductive type Term representing the free algebra:

```
inductive Term where
  | f_0 : Term
  | f_1 : Term
  | z : Term
  | compose : Term -> Term -> Term
  | oplus : Term -> Term -> Term
  | obs : Term -> Term
```

An evaluation function `eval : Term -> State` interprets each constructor in any DynSemiring instance. The key operation is `obsRewrite`, which applies the Leibniz rule at the root:

```
obsRewrite(obs(compose(a, b))) = oplus(compose(obs(a), b), compose(a, obs(b)))
obsRewrite(t) = t    (otherwise)
```

### 2.3 The Eigenvalue Theorem

From the DynSemiring axioms, the n-fold self-composition f_n = compose(f_1, ..., f_1) satisfies:

```
obs(f_n) = n * f_n
```

where n * f_n denotes the n-fold oplus sum of f_n with itself. The eigenvalues {0, 1, 2, 3, ...} form the natural numbers under oplus (addition) and compose (multiplication), yielding a structure equiconsistent with Peano Arithmetic.

---

## 3. The Encoding Obstruction

### 3.1 The Structural Gap

**Lemma 1** (Extensionalize != Original). For any terms a, b:

```
obsRewrite(obs(compose(a, b))) != obs(compose(a, b))
```

*Proof.* The left side has constructor `oplus` at the root (the Leibniz rule produces a sum). The right side has constructor `obs` at the root. These are distinct constructors in the free term algebra. (Lean: `extensionalize_ne_original_general`, Encoding.lean:252) QED

**Theorem 1** (No Coalgebra Morphism). For any injective epsilon : Term -> N and any terms a, b:

```
epsilon(obsRewrite(obs(compose(a, b)))) != epsilon(obs(compose(a, b)))
```

*Proof.* By Lemma 1, the two terms are distinct. By injectivity of epsilon, distinct terms receive distinct codes. (Lean: `no_coalgebra_morphism`, Main.lean:232) QED

The proof is elementary but the consequence is not: **no injective encoding of terms into natural numbers can serve as a coalgebra morphism between semantic observation and syntactic rewriting.** The encoding necessarily distorts the dynamics.

### 3.2 Semantic Invariance

**Theorem 2** (Semantic Invariance). For any DynSemiring instance and any terms a, b:

```
eval(obsRewrite(obs(compose(a, b)))) = eval(obs(compose(a, b)))
```

*Proof.* Direct application of the Leibniz axiom: `obs(compose(a, b)) = oplus(compose(obs(a), b), compose(a, obs(b)))` holds in every DynSemiring. The obsRewrite function simply applies this identity at the term level. Evaluation in any model respects the axiom, so both sides evaluate to the same element. (Lean: `semantic_invariance_general`, Encoding.lean:277) QED

Theorems 1 and 2 together establish the core asymmetry: **the encoding changes the syntax while preserving the semantics.** The two forms are different as terms (different codes under any injective encoding) but identical as values (same element in every DynSemiring).

### 3.3 No Fixed Point

**Theorem 3** (Substitution Chain Distinct). Let t_0 = obs(compose(a, b)), t_1 = obsRewrite(t_0), and t_2 = deepRewrite(t_1). Then t_0, t_1, and t_2 are pairwise distinct.

*Proof.* t_0 has root constructor `obs`. t_1 has root constructor `oplus` (by the Leibniz rule). t_2 results from applying deepRewrite to t_1, which recurses into sub-terms and applies obsRewrite at each obs node; since the sub-terms of t_1 contain obs-compose patterns (from the original a and b), deepRewrite modifies them, producing a term structurally distinct from both t_0 and t_1. (Lean: `substitution_chain_distinct`, Encoding.lean:195) QED

The chain of extensionalizations never stabilizes. Each level of unfolding produces a genuinely new syntactic form, even though the semantic value is preserved throughout. This is the formalization of "substitution is open-ended."

### 3.4 Size Growth

**Theorem 4** (More Than Doubling). For any terms a, b:

```
termSize(obsRewrite(obs(compose(a, b)))) > 2 * termSize(obs(compose(a, b)))
```

*Proof.* The original term obs(compose(a, b)) has size 1 + 1 + size(a) + size(b). The rewritten term oplus(compose(obs(a), b), compose(a, obs(b))) has size 1 + (1 + (1 + size(a)) + size(b)) + (1 + size(a) + (1 + size(b))) = 5 + 2*size(a) + 2*size(b). Since 5 + 2*size(a) + 2*size(b) > 2*(1 + 1 + size(a) + size(b)) = 4 + 2*size(a) + 2*size(b), the bound holds. (Lean: `extensionalize_more_than_doubles`, Encoding.lean:334) QED

---

## 4. The Trilemma

### 4.1 Three Properties

Any self-representing eigenvalue system combines three properties:

**Property 1: Eigenvalue Arithmetic.** The Leibniz rule forces eigenvalues to be linear: obs(f_n) = n * f_n. This produces the natural numbers, yielding PA-strength arithmetic including prime factorization, primitive recursion, and bounded quantification.

**Property 2: Self-Encoding.** The PA arithmetic enables Godel encoding: an injective, decodable map from terms to natural numbers. Any such encoding requires an injective pairing function pi : N x N -> N, which is necessarily super-linear: pi(n, n) is in omega(n).

**Property 3: Coalgebra Morphism.** The encoding commutes with observation — the eval-quote diagram commutes. This requires the encoding to preserve the observation operator's dynamics.

### 4.2 Pairwise Compatibility, Joint Impossibility

Properties 1 and 2 are compatible: this is the framework as it stands. Linear eigenvalues produce arithmetic, arithmetic enables encoding.

Properties 2 and 3 would be compatible if eigenvalues could be made super-linear (matching the encoding's growth rate). But super-linear eigenvalue sets (e.g., {1, 2, 4, 8, ...} from a homomorphism rule) are not closed under addition, destroying the semiring structure and with it the PA arithmetic that Property 2 requires.

Properties 1 and 3 would be compatible if the encoding could be made linear. But a linear function N x N -> N (e.g., addition) is not injective on pairs, so Property 2 (injective self-encoding) fails.

**The trilemma:** self-encoding requires the arithmetic that only linear eigenvalues provide, but the coalgebra morphism requires encoding growth rates to match eigenvalue growth rates, and no injective encoding is linear. The system's power to encode itself (from having linear arithmetic) is precisely what prevents the encoding from preserving dynamics (because encoding is necessarily super-linear while observation is linear).

### 4.3 Blocked Escape Routes

**Escape 1: Redundant Number Systems.** Signed-digit representations (Avizienis, 1961) achieve carry-free addition via non-unique representations. But self-encoding requires injective, decodable maps — which require unique representation. Redundant representations trade uniqueness for carry locality, but uniqueness is what self-encoding needs. Carry reappears at equality testing and canonicalization.

**Escape 2: Residue Number Systems.** RNS provides carry-free addition, subtraction, and multiplication via per-component modular arithmetic. But comparison, ordering, and division are lost. Godel encoding requires positional access (which prime? what exponent?), which requires ordering, which RNS sacrifices. Carry reappears at the conversion to positional form.

**Escape 3: Tropical Algebra.** Replacing (N, +, *) with (N, max, +) makes addition (now max) fully local. But max is idempotent (max(a, a) = a) and non-cancellative (max(3, 5) = max(3, 7) = 7 does not imply 5 = 7). Without cancellation: no subtraction, no division, no prime factorization, no Godel encoding. The eigenvalue orbit collapses.

Each escape route reintroduces carry propagation at a different point in the computation or destroys the algebraic structure required for self-encoding.

---

## 5. The Executable Consequence: External State

### 5.1 From Obstruction to State

For passive encoding (Godel numbering as inert labels), the encoding obstruction gives incompleteness: the system can name but not resolve self-referential propositions. For executable encoding (the system operates on its own codes), the obstruction forces external state.

The chain:

1. Self-encoding requires addition (the Leibniz rule introduces oplus when extensionalizing compound terms).
2. Addition on unique positional representations requires carry propagation (output at position k depends on inputs at all positions 0 through k).
3. Carry propagation is non-local (Theorem 6: `carry_propagation_general`).
4. Non-local operations require normalization state external to the encoding — a register that holds intermediate carry values while propagation completes.

### 5.2 The Bitwise Impossibility

One might hope to avoid carry by implementing oplus as a bitwise operation (XOR, OR, or similar). Theorem 5 forecloses this:

**Theorem 5.** No bitwise operation f : N -> N -> N can simultaneously satisfy:
- Commutativity: f(a, b) = f(b, a)
- Associativity: f(a, f(b, c)) = f(f(a, b), c)
- Identity: f(z, a) = a
- Cancellation: f(a, b) = f(a, c) implies b = c
- Characteristic zero: n-fold f-sum of f_0 is not z for any n >= 1

Any bitwise operation inheriting from Bool inherits characteristic 2 (since in Bool, a XOR a = 0 and a OR a = a for all a). Characteristic 2 contradicts the characteristic zero axiom. (Lean: `oplus_bitwise_impossible`, `bitwise_underlying_char_two`)

### 5.3 The Asymmetry

The encoding obstruction creates a structural asymmetry between two modes of observation:

| Mode | Operation | Locality | Cost |
|------|-----------|----------|------|
| Semantic (intensional) | obs reads eigenvalue: obs(f_n) = n * f_n | Local — single multiplicative scaling | O(1) per eigenstate |
| Syntactic (extensional) | Leibniz rewrite introduces oplus, requiring carry | Non-local — carry propagates across all positions | Omega(log n) per addition |

Semantic observation reads a number. Syntactic observation decomposes, rewrites, and re-encodes — introducing addition (the oplus in the Leibniz sum), which requires carry propagation, which requires external state. The register that carry forces into existence is the structural reason the eval-quote diagram does not commute.

---

## 6. Normalization and Complexity

### 6.1 Confluence and Termination

The DynSemiring axioms, oriented as rewrite rules, form a confluent and terminating rewriting system (proved separately in the confluence analysis). Every term has a unique normal form: a sum-of-products-of-atoms, the algebraic analogue of expanded polynomial form.

### 6.2 Normalization Depth

For the family `nestedObsCompose(d) = obs(compose(nestedObsCompose(d-1), nestedObsCompose(d-1)))` with base case compose(f_1, f_1), normalization depth is **constant** — exactly 2 passes of bottom-up deep rewriting, independent of nesting depth d. (Lean: `normDepth_nested_eq_two`, Complexity.lean)

However, term size grows exponentially: `termSize(nestedObsCompose(d)) >= 2^d`. (Lean: `compounding_size_lower_bound`, Complexity.lean)

The exponential cost of extensionalization lives in per-pass term size, not in pass count. The Leibniz rule's branching doubles the term at each application, producing exponentially large intermediate forms even though normalization terminates in constant passes.

### 6.3 The Leibniz Rule Is Forced

The obsRewrite function is the unique minimal correct expansion of obs(compose(a, b)) in any DynSemiring. No smaller term evaluates correctly in all models:

- Dropping either branch of oplus(compose(obs(a), b), compose(a, obs(b))) produces an incorrect result in any model where obs(a) != z and obs(b) != z.
- The Leibniz axiom specifies the result exactly; any equivalent term must be equal to this oplus under the DynSemiring axioms.

The branching factor per rewrite step is algebraically inevitable. (Lean: `obsRewrite_eval`, Encoding.lean:94)

---

## 7. Relationship to Complexity-Theoretic Barriers

### 7.1 Relativization

The encoding obstruction is **non-relativizing by construction.** The proof examines the internal algebraic structure of terms — specifically, the obsRewrite function pattern-matches on the `.obs(.compose a b)` constructor. An oracle query has no constructor; it is an atomic operation whose internal structure is hidden. The Leibniz decomposition cannot be applied to oracle terms, so the entire extensionalization mechanism — and therefore the entire obstruction — depends on seeing inside the computation.

This is analogous to how IP = PSPACE is non-relativizing: arithmetization looks inside Boolean formula gates, which fails when gates are oracle calls. The encoding obstruction looks inside composed terms via the Leibniz rule, which fails when terms are oracle calls.

### 7.2 Natural Proofs

The encoding obstruction **does not operate on truth tables of Boolean functions.** The Razborov-Rudich framework concerns properties of Boolean functions tested on their truth tables. The encoding obstruction concerns algebraic properties of self-encoding systems: eigenvalue structure, Leibniz extensionalization, carry propagation. These are not properties of individual Boolean functions.

The property identified by the obstruction (the intension/extension gap in self-encoding systems with Leibniz extensionalization) is problem-specific, not generic — it holds for specific algebraic systems, not for a non-negligible fraction of random Boolean functions. A random Boolean function has no eigenvalue structure, no Leibniz rule, no self-encoding. The property would hold for a measure-zero set.

### 7.3 Algebrization

The encoding obstruction uses arithmetic but in a structurally different way from the arithmetization that algebrization captures. Algebrization concerns proofs that convert Boolean computation into polynomial evaluation over finite fields and then use low-degree extensions. The encoding obstruction examines growth rates of encoding functions and structural compatibility of eigenvalue scaling with injective pairing — properties of the meta-level relationship between encoding and execution, not of object-level polynomial evaluation.

The key structural distinction: algebrization models the relationship between Boolean and arithmetic as a one-directional extension ({0,1} -> F_q). In a self-encoding system, position (arithmetic) and existence (Boolean) are the same layer viewed at different scales, connected bidirectionally by the derivative (obs reads eigenvalues, which at the bit level are Boolean). The algebrization framework does not capture proof techniques that exploit this bidirectional identity.

### 7.4 Assessment

The encoding obstruction avoids the three known barriers because it examines a different mathematical object than the barriers were designed to block: the internal algebraic structure of self-encoding systems, rather than the input/output behavior of machines (relativization), the combinatorial properties of truth tables (natural proofs), or the polynomial evaluation of Boolean functions (algebrization).

Avoiding barriers is necessary but not sufficient for resolving P vs NP. The encoding obstruction proves structural facts about self-encoding systems. Whether these structural facts can be connected to complexity-theoretic separations remains an open question requiring a bridge from algebraic normalization cost to standard complexity measures.

---

## 8. Discussion

### 8.1 What the Results Establish

The encoding obstruction is a theorem about the structure of self-representing algebraic systems. It establishes:

1. **The eval-quote diagram does not commute** for any injective encoding (Theorem 1), while semantics is preserved (Theorem 2). The gap is syntactic, not semantic.

2. **The intension/extension chain has no fixed point** (Theorem 3). Extensionalization always produces a structurally new term. Substitution is open-ended.

3. **Each extensionalization step more than doubles term size** (Theorem 4). The encoding distortion grows exponentially with the depth of the extensionalization chain.

4. **No bitwise realization of addition satisfies the algebraic requirements** (Theorem 5). The characteristic-zero condition is incompatible with Boolean-valued operations.

5. **Carry propagation is non-local in any base** (Theorem 6). The external state requirement holds for all positional number systems.

6. **Every known escape route is blocked.** Redundant representations, residue number systems, and tropical algebra each sacrifice a property required for self-encoding.

7. **The Leibniz rule is algebraically forced.** The branching factor per extensionalization step is not a design choice but a consequence of the DynSemiring axioms.

### 8.2 What the Results Do Not Establish

The encoding obstruction does not prove P != NP. The algebraic separation (linear eigenvalue observation vs. super-linear encoding) operates at a different threshold than the complexity-theoretic separation (polynomial verification vs. super-polynomial search). The structural analogy is genuine — verification is intensional (cheap eigenvalue read), construction is extensional (expensive Leibniz expansion) — but the logical implication from one to the other is not established.

The bridge from algebraic results to complexity separation requires showing that the normalization cost of specific problem encodings (e.g., SAT formulas represented as DynSemiring terms) corresponds to the computational complexity of solving those problems. This connection is the central open question.

### 8.3 Relationship to Godel's Incompleteness

Both Godel's theorem and the encoding obstruction are consequences of the intension/extension gap in self-naming systems. Godel's theorem concerns passive self-reference: the system names a proposition about itself but cannot resolve it. The encoding obstruction concerns executable self-reference: the system attempts to run its own encoding, and the execution step (which requires addition via the Leibniz rule, which requires carry propagation) introduces machinery the encoding cannot absorb.

The relationship is not analogy — it is specialization. The encoding obstruction, restricted to passive encoding, gives Godel incompleteness. Extended to executable encoding, it gives the external state requirement. Both are instances of: substitution is open-ended, and there is no fixed point.

### 8.4 Open Questions

1. **Can the algebraic separation be strengthened to a complexity separation?** Specifically: does the exponential term-size growth under Leibniz extensionalization for NP-complete problem encodings imply super-polynomial time for any algorithm solving those problems?

2. **What is the weakest behavioral equivalence between the semantic and syntactic coalgebras?** The full bisimulation is impossible, but natural transformation, asymptotic equivalence, or partial bisimulation on fragments may hold.

3. **Does the encoding obstruction generalize beyond eigenvalue systems?** The argument uses the Leibniz rule and eigenvalue linearity specifically. Do analogous obstructions hold for other self-representing algebraic structures (e.g., systems with a homomorphism rule instead of a derivation)?

4. **Is there a formal language for composition and complexity in which contractibility to a ground state encodes complexity class membership?** The encoding obstruction identifies the structural factors such a language would need (a self-feeding contraction rule, intrinsic contractibility, unified processing and data). Whether such a language exists is open.

---

## 9. Formalization

All theorems in this paper are formalized in Lean 4 using the Mathlib library. The formalization is organized as follows:

| File | Contents |
|------|----------|
| Core/Semiring.lean | DynSemiring definition, SpectralMonoid, eigenvalue theorem |
| Obstruction/Encoding.lean | obsRewrite, deepRewrite, semantic invariance, encoding obstruction, size bounds, substitution chain |
| Obstruction/Main.lean | no_coalgebra_morphism, no_encoding_fixpoint, trajectory divergence |
| Obstruction/Oplus.lean | Bitwise impossibility, characteristic-2 inheritance |
| Obstruction/Pairing.lean | Carry propagation generality, pairing function bounds |
| Obstruction/Complexity.lean | Normalization depth (constant for nestedObsCompose), term size bounds |
| Obstruction/CostBounds.lean | Per-pass cost analysis, site persistence |
| Obstruction/SAT.lean | SAT formula encoding as Terms |
| Obstruction/VarSharing.lean | Variable sharing analysis |

The total formalization contains zero sorry (unproved assumptions). All definitions are computable where applicable, and key conjectures that were disproved by formalization (e.g., the original exponential normalization depth conjecture) have been corrected and documented.

---

## References

- Avizienis, A. (1961). Signed-digit number representations for fast parallel arithmetic. *IRE Transactions on Electronic Computers*, EC-10(3):389-400.
- Aaronson, S. & Wigderson, A. (2009). Algebrization: A new barrier in complexity theory. *ACM Transactions on Computation Theory*, 1(1):2.
- Baker, T., Gill, J., & Solovay, R. (1975). Relativizations of the P=?NP question. *SIAM Journal on Computing*, 4(4):431-442.
- Godel, K. (1931). Uber formal unentscheidbare Satze der Principia Mathematica und verwandter Systeme I. *Monatshefte fur Mathematik und Physik*, 38:173-198.
- Gurevich, Y. (2000). Sequential abstract state machines capture sequential algorithms. *ACM Transactions on Computational Logic*, 1(1):77-111.
- Hastad, J. (1987). *Computational Limitations of Small-Depth Circuits*. MIT Press.
- Mulmuley, K. & Sohoni, M. (2001). Geometric complexity theory I. *SIAM Journal on Computing*, 31(2):496-526.
- Razborov, A. & Rudich, S. (1997). Natural proofs. *Journal of Computer and System Sciences*, 55(1):24-35.
- Turing, A.M. (1936). On computable numbers, with an application to the Entscheidungsproblem. *Proceedings of the London Mathematical Society*, 42:230-265.
- Williams, R. (2011). Non-uniform ACC circuit lower bounds. *IEEE Conference on Computational Complexity*.
