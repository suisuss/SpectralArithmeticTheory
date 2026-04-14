# Spectral Arithmetic: Postgraduate Overview

## Date: 2026-02-14

## The Problem

Standard mathematics founds arithmetic on the Peano axioms and set theory on ZF — both taken as starting points. Meanwhile, differential algebra studies commutative rings with derivations, and the eigenvalue structure of such derivations is well understood. The question: can Peano arithmetic be *derived* from differential-algebraic structure rather than axiomatized independently?

## The Construction

Start with a coalgebraic structure: a type `State`, a binary composition `compose`, a unary observation operator `obs`, and an additive operation `⊕`. Axiomatize obs as a derivation (Leibniz rule over compose), require a fixed point `obs(f₁) = f₁`, and impose characteristic zero.

## What Falls Out

**Natural numbers.** The fixed point f₁ generates an orbit under composition: f₀, f₁, f₂, ... These are your natural numbers. obs reads off *which number* a state represents — `obs(fₙ) = n · fₙ` is a provable theorem (the eigenvalue equation), not an axiom.

**Peano arithmetic.** All five Peano axioms are theorems. The system is PA-equiconsistent.

**The number tower.** Extend by adjoining inverses (ℤ), roots (ℚ), Cauchy completion (ℝ), and a quarter-turn operator j with j² = -1 (ℂ). Each extension adds 1-5 axioms. You get the full number tower in one algebraic space rather than four separate constructions.

**Set theory.** Define sets as predicates (characteristic functions), membership as predicate application. 5 of 9 ZF axioms fall out automatically from the predicate interpretation. The remaining 4 require 3 new axioms (completed infinity, comprehension, replacement) — the same commitments ZF makes, restated in process-native language. The system is ZF-equiconsistent.

**Foundation for free.** Foundation (no set is a member of itself) follows from type stratification (states ≠ predicates) rather than requiring an axiom.

## The Algebraic Structure

A commutative differential ring (semiring at ℕ, integral domain at ℤ, ℚ-algebra at ℚ, complete ℝ-algebra at ℝ, with the quarter-turn extending to ℂ). The obs operator is a derivation in the ring-theoretic sense. If you work in the analytic model, obs = d/dx and the eigenstates are the exponentials eⁿˣ. But the abstract framework is representation-independent — the 21 axioms never mention x.

## The Rewriting System

Confluent and terminating (proved via lexicographic measure on obs-compound depth, compose-over-⊕ count, and term size; confluence via critical pair analysis). Every well-formed term has a unique normal form: a sum-of-products-of-atoms, the process-algebraic analogue of expanded polynomial form.

## Self-Representation

Since the system is PA-equiconsistent, it supports Gödel encoding of its own syntax. Every eigenstate is simultaneously a number (eigenvalue), a process (composable, observable), and a code (Gödel number of a term). Syntactic predicates, computation, and incompleteness are all definable internally using only existing primitives.

## The Open Conjecture

The internally-derived discrete dynamics (rewrite steps on Gödel codes, branching factor 2) may converge to obs (continuous, eigenbase e) in a way that closes a self-referential loop. If true, this would mean the framework's self-encoding *forces* the analytic representation — self-reference would constrain which representations are canonical. Currently unproved; the main obstacles are that the abstract framework is x-free (so finite differences aren't directly definable) and the Gödel encoding is syntactic, not a homomorphism.

The conjecture is the difference between "we designed a foundation that looks computational" and "computation is what foundations look like when they examine themselves."

## By the Numbers

- **21 axioms**, 4 primitives (State, compose, obs, ⊕)
- Covers ℕ through ℂ plus ZF-level set theory
- PA-equiconsistent and ZF-equiconsistent
- Confluent, terminating rewriting system with unique normal forms

## What This Is (and Isn't)

This is a representation theorem: Peano arithmetic can be represented inside a commutative semiring with a Leibniz derivation. It is equiconsistent with PA and ZF — it proves the same theorems, not more. The contribution is the algebraic presentation: arithmetic emerging from differential structure rather than being axiomatized directly, with a progressive axiom layering where assumptions at one level become theorems at the next. The open conjecture about self-reference constraining representation is the most original open question.

---

## Related

- [axioms](../axioms.md)
- [self-representation](../computation/self-representation.md)
- [confluence](../computation/confluence.md)
