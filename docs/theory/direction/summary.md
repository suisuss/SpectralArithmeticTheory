# Spectral Arithmetic: Postgraduate Summary

## Date: 2026-02-14

---

You take the ODE f' = f, f(0) = 1 and ask: what if this isn't a fact about a particular function, but the *definition* of the multiplicative unit in a commutative semiring with a derivation?

The construction works like this. You have four primitives — a carrier (State), a binary operation (compose), a unary operator (obs), and a second binary operation (⊕). You axiomatize: obs(f₁) = f₁ (the unit is a fixed point of observation), compose(f₀, s) = s (there's an identity), and obs satisfies the Leibniz rule over compose with respect to ⊕. That Leibniz rule is doing the heavy lifting — it's the abstract content of the product rule, and from it you *derive* the eigenvalue equation obs(fₙ) = n · fₙ as a theorem rather than observing it as a fact about eⁿˣ.

So natural numbers are eigenvalues of obs. Successor is compose with f₁. You verify all five Peano axioms as theorems and prove equiconsistency: Con(A1-A8) ↔ Con(PA). Then you extend incrementally — additive inverses give you ℤ (integral domain), roots give you ℚ (ℚ-algebra), Cauchy completion gives you ℝ, a quarter-turn operator j with j² = -1 gives you ℂ. Twenty-one axioms total, each extension adding the minimal commitments needed. The eigenvalue theorem extends at every level: obs(f_w) = w · f_w for w ∈ ℂ.

For set theory: sets are predicates (characteristic functions), membership is predicate application. Five of nine ZF axioms fall out automatically from this interpretation. The remaining four (infinity, powerset, union, replacement) require three new axioms — the same ontological commitments ZF makes, restated in process language. Foundation is free because states and predicates live in different types, so self-membership is a type error. You get equiconsistency: Con(ZF) ↔ Con(A1-F3), proved in both directions. The forward model is the group algebra ℝ[(ℝ,+)] with compose as convolution.

The framework is PA-strong, so Gödel encoding is available. You encode the framework's own syntax as eigenstates via prime factorization and define computation as an arithmetic predicate — Computes(⌜T₁⌝, ⌜T₂⌝) says there's a finite derivation from T₁ to T₂. Incompleteness follows internally. The eigenstates have a triple identity: each one is simultaneously a number (its eigenvalue), a process (composable, observable), and a code (the Gödel number of some term). In standard PA, Gödel numbers are passive data — they require external functions to decode and manipulate. Here, the codes are eigenstates that already carry algebraic structure (composable, observable). This is a design choice, not a theorem about relative strength.

The equational axioms are confluent and terminating when oriented as rewrite rules — proved via lexicographic termination measure and critical pair analysis. Every closed term has a unique normal form (sum-of-products-of-atoms).

What it *doesn't* have is a proof that the internally-derived discrete dynamics close into a self-referential loop with obs. The conjecture is that ValidStep (one rewrite step on Gödel codes) relates to obs the way finite differences relate to differentiation — discrete converging to continuous. Three obstacles block the proof: the abstract framework is x-free so you can't define Δ_h without choosing a representation, the Gödel encoding isn't a homomorphism so arithmetic on codes doesn't correspond to algebra on states, and the "2" from binary branching in syntax trees is a different mathematical fact from the "2" that's the eigenbase of the finite difference operator. It's a suggestive structural parallel, not a theorem.

So the honest summary: it's an alternative algebraic presentation (coalgebraic in flavour — bisimulation gives you extensional equality for free) that reproduces PA and ZF at equiconsistent strength, with genuine self-representation and a clean number tower from ℕ through ℂ in one algebraic space. The interesting structural fact is that the Peano axioms fall out of differential algebra — they are consequences of the Leibniz rule, not independent postulates. The open question is whether the self-referential loop (discrete dynamics converging to obs) has a theorem behind it or is just a suggestive parallel.

---

## Related

- [self-representation](../computation/self-representation.md)
- [confluence](../computation/confluence.md)
