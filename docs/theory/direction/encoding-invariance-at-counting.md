# Encoding invariance at counting

**Date:** 2026-04-21

Positioning document. A thesis-framing question, not a result: **does the universal encoding obstruction bite at the level of counting itself, or only above it?** This doc states the question, maps the two horns, and names criteria that would settle either direction. No claim is made here that the question is resolved.

---

## The question

The Part 2 thesis formalises a *form-changing, semantics-preserving rewrite* (`EvalRewriteWitness`) as the obstruction mechanism — a transformation that preserves a formula's evaluation while changing its syntactic shape, and that any complete proof system must make impossible at some point. Seven machine-checked instances instantiate this at PA, halting, beta, cut elimination, resolution, diagonal, and term algebras. The thesis asserts that the obstruction is **encoding-invariant**: it does not depend on which syntactic presentation of the underlying theory you pick.

The foundational question this doc isolates:

> Does encoding-invariance extend *downward* to the structure that all these encodings share — counting itself — or does it start strictly *above* counting, with counting serving as a substrate that the obstruction presupposes rather than constrains?

Two things can be true:

1. The obstruction is a statement about encoded theories, and counting (ℕ, successor, finite cardinality) is the pre-theoretic ground on which encodings are defined. Counting is *below* the obstruction's domain. The obstruction does not apply to it.
2. Counting is itself an encoding choice (unary vs. positional vs. Church vs. zipper), different encodings have different complexity profiles, and the obstruction — or something analogous — applies at this layer too.

The thesis's formal content as it stands is compatible with either reading. Which one is correct shapes the paper's foundational narrative and the future-work direction.

---

## Why it matters for the thesis

- **If horn 1 (invariance holds at counting):** the obstruction story is cleaner — there is a well-defined floor below which the obstruction does not reach, and the paper can present counting as a shared pre-theoretic substrate. The "universal" in "universal encoding obstruction" refers to universality across *encodings of theories over ℕ*, not across *encodings of ℕ*.

- **If horn 2 (invariance fails at counting):** the thesis has a deeper claim to make, and also a deeper vulnerability. The obstruction would apply recursively — any attempt to formalise ℕ via a specific encoding would exhibit the same form/semantics tension. This strengthens the universality claim philosophically but requires demonstrating the obstruction at the counting level, not just the theory-over-counting level. The paper's scope expands.

- The March 2026 RC finding (Rotation Calculus ≅ Permutation CSP up to notation) is a *data point for horn 2* at the framework level: the appearance of novelty dissolved under an encoding translation. Issue #54 asks the analogous question vs. zipper-traversal. If framework-level novelty is routinely an encoding artifact, that weakens confidence that the Part 2 obstruction itself is encoding-invariant without explicit demonstration.

---

## Horn 1: invariance holds at counting

**Claim.** Counting is structurally unique up to isomorphism. Every encoding of ℕ (unary, positional base-b, Church, zipper, skew-binary, NNO) is a presentation of the same object. The obstruction applies to encoded *theories over ℕ*; it does not apply to ℕ itself, because ℕ has no non-trivial alternative to be obstructed.

**Evidence in the codebase for this reading:**

- `Core/Basic.lean` and `Core/Semiring.lean` derive Peano P1–P5 from a small set of eigenvalue axioms. The construction is independent of any specific numeral encoding — it works at the algebraic/categorical level.
- `Verification/PeanoTest.lean` exhibits PA1–PA9 as theorems over the abstract structure, not as statements about a chosen representation of digits.
- `docs/theory/pa-equiconsistency.md` argues equiconsistency at the axiomatic level, one layer above any encoding.
- The initial-algebra characterisation of ℕ (initial `1 + X` algebra, natural-numbers object in a topos, free monoid on one generator) converges on the same object from multiple categorical angles. This is a classical result, not project-specific, but it supports the horn.

**What would strengthen horn 1:** a theorem, formal or informal, stating "`EvalRewriteWitness` requires a theory strictly richer than ℕ for its form/semantics tension to be non-trivial." Concretely: identify the minimum arithmetic strength (e.g., Robinson Q, PA, PA + something) below which the obstruction is vacuous or trivially satisfied.

**What would weaken horn 1:** an instance of `EvalRewriteWitness` at the counting layer itself — e.g., a form-changing semantics-preserving rewrite between two encodings of ℕ that cannot be admitted by any complete "proof system" for counting.

---

## Horn 2: invariance fails at counting

**Claim.** "Counting" is an encoding choice masquerading as a primitive. Unary, positional, Church, and zipper numerals are not the same object at the level where complexity bites. The obstruction — or a closely analogous structural tension — recurs at the counting layer.

**Evidence for this reading:**

- The unary→positional gap is exponential: `Θ(n)` symbols vs. `Θ(log n)`. Arithmetic algorithm complexity (addition, multiplication, equality test) changes accordingly. If the obstruction is about complexity-relevant structure, this gap is already encoding-sensitive.
- Kolmogorov complexity: the description length of a natural number depends on the encoding. No encoding-free definition of "how complex is the number n" exists.
- Church numerals expose cardinal/ordinal divergence at the representational level: `pred` is expensive (the Kleene trick), `succ` and iteration are cheap. The *same* ℕ has operationally asymmetric presentations.
- `docs/theory/computation/addition-non-locality.md` documents that carry propagation forces stateful computation — i.e., that arithmetic operations have different complexity profiles depending on how the operands are encoded.
- The RC ≅ CSP ≅ zipper-traversal chain of reductions is a pattern: apparent framework-level structure dissolves into notation under translation. If that pattern holds generally, encoding-invariance is the exception, not the rule.
- `docs/theory/computation/framework-independence.md` (per the README index) argues for independence at the framework level. Whether this extends to counting is precisely the question here.

**What would strengthen horn 2:** construct a formal counterpart of `EvalRewriteWitness` at the counting layer — a rewrite between two numeral encodings that (i) preserves every cardinal-level predicate (equality of count, ordering), (ii) changes complexity-relevant form (encoding length, operation cost), and (iii) cannot be admitted by any resource-bounded "counting system." If such a construction exists, the obstruction applies to counting.

**What would weaken horn 2:** a theorem that all encodings of ℕ are related by a complexity-preserving translation at some level of resource bound. This is false in the strict complexity-theoretic sense (unary is not polynomially related to binary for additive problems), but could hold at a coarser level relevant to the obstruction.

---

## What would settle it

Neither horn is currently disproved by the formal corpus. Settling the question requires either:

- **Horn 1 route**: identify the minimum theory strength at which `EvalRewriteWitness` becomes non-trivial, and show that strength strictly exceeds "counting." This is a project in calibration — where on the arithmetic hierarchy does the obstruction first engage?
- **Horn 2 route**: construct a counting-level instance of `EvalRewriteWitness` (or its faithful analogue) and verify it in Lean. This is a construction project — exhibit a rewrite at the numeral-encoding layer that satisfies the obstruction's structural pattern.

Until one of these routes produces a result, the paper should be explicit that the "universal" in "universal encoding obstruction" refers to universality across *seven instantiations over theories of arithmetic strength PA and above*, and leave the question of whether the obstruction extends to counting itself as acknowledged open.

---

## Relation to other direction docs

- [focus.md](focus.md) — the paper-critical work is discharging the 20 named axioms, not resolving this question. This doc exists so the question is recorded; it is **not** a recommendation to pursue it as a deliverable.
- [pvsnp-assessment.md](pvsnp-assessment.md) — P vs NP independence is deferred to future directions. The counting-layer question is similarly deferred but is foundational rather than complexity-theoretic.
- [novelty.md](novelty.md) — the intensional/extensional framing is one layer above counting. Whether that framing reaches down to the counting layer is exactly the horn-1/horn-2 question.

## Pointers to supporting material

- `docs/theory/computation/encoding-obstruction.md` — core obstruction theory.
- `docs/theory/computation/framework-independence.md` — framework-level independence.
- `docs/theory/computation/pvsnp/normalization-preserves-structure.md` — normalisation as structure-preserving rewrite.
- `docs/theory/computation/addition-non-locality.md` — carry propagation forces state; evidence for horn 2.
- `docs/theory/computation/pvsnp/reconstituted/Rotation Calculus/assessment.md` — the March 2026 CSP equivalence admission.
- GitHub issue #54 — RC vs. zipper-traversal; an analogous encoding-collapse question at the framework level.
- `SpectralArithmetic/Core/Basic.lean`, `Core/Semiring.lean`, `Verification/PeanoTest.lean` — evidence for horn 1 (abstract derivation independent of specific numeral encoding).
- `SpectralArithmetic/Obstruction/` — seven `EvalRewriteWitness` instances, all at theory strength ≥ PA; none at counting level.
