# P vs NP Literacy: Learning Path

## Date: 2026-03-24

## Purpose

Build formal mastery of P vs NP and surrounding complexity theory to close the gap between structural intuition and rigorous formalization. The goal is not to learn algorithms but to acquire the precise language in which the generator argument, coupling argument, and contractibility framing can be stated — and to see exactly where they are novel vs where they overlap with existing results.

---

## Phase 1: Core Complexity Theory (2-3 weeks)

### Arora & Barak — *Computational Complexity: A Modern Approach*

Free draft available online. This is the reference text.

**Chapters to read:**

| Chapter | Topic | Why it matters for this research |
|---------|-------|--------------------------------|
| 1 | The computational model (Turing machines, circuits) | Formalizes what "computation" means — compare with the framework's "computation = language + external state" |
| 2 | NP and NP-completeness | The formal definitions behind everything — Cook-Levin, reductions, the verification/search distinction |
| 3 | Diagonalization | The technique behind time hierarchy theorems — connects to the coupling/diagonal argument |
| 4 | Space complexity | NL, PSPACE, Savitch's theorem — different resource, same structural questions |
| 5 | The polynomial hierarchy | PH, oracle machines, the relativization structure — formalizes the "levels" of quantifier alternation |
| 6 | Boolean circuits | Non-uniform computation, circuit families — this is where lower bound proofs actually happen |
| 14 | Circuit lower bounds | The actual proved results (parity not in AC0, etc.) — what works and why it's limited |
| 23 | Proofs and barriers | Relativization, natural proofs, algebrization — the formal versions of the barriers already analyzed in barrier-analysis.md |

**How to read:** Read for structure, not exercises. The goal is to internalize the definitions and proof strategies. When a theorem proof uses diagonalization, note it — when it uses a counting argument, note it. The proof technique taxonomy matters more than individual results.

---

## Phase 2: The Barrier Results (1 week)

Read these in order. Each builds on the previous.

### 1. Relativization

**Paper:** Baker, Gill, Solovay (1975). *Relativizations of the P=?NP Question.* SIAM Journal on Computing, 4(4):431-442.

The original paper is readable. The key result: there exist oracles A and B such that P^A = NP^A and P^B != NP^B. Any proof of P != NP must use properties of computation that oracle access destroys.

**What to get from it:** The formal definition of relativization. How oracle Turing machines work. Why "treating computation as a black box" is formalized as "the proof relativizes." Compare with the encoding obstruction's non-relativization argument (barrier-analysis.md, Part 1).

### 2. Natural Proofs

**First read:** Aaronson's survey/blog treatment of natural proofs (search "Aaronson natural proofs" — he has multiple accessible expositions).

**Then the paper:** Razborov, Rudich (1997). *Natural Proofs.* Journal of Computer and System Sciences, 55(1):24-35.

The key result: if pseudorandom functions computable by polynomial-size circuits exist, then no "natural" combinatorial property can prove circuit lower bounds against P/poly. A natural property must be constructive (testable in poly time on truth tables) and large (satisfied by a non-negligible fraction of functions).

**What to get from it:** The formal definitions of constructivity and largeness. Why generic combinatorial arguments are self-defeating. Compare with the encoding obstruction's problem-specific structure (barrier-analysis.md, Part 2).

### 3. Algebrization

**Paper:** Aaronson, Wigderson (2009). *Algebrization: A New Barrier in Complexity Theory.* ACM Transactions on Computation Theory, 1(1):2.

The key result: there exist algebraic oracles in both directions for P vs NP. Any proof must use techniques that go beyond arithmetization + relativization. IP = PSPACE algebrizes; a proof of P != NP cannot.

**What to get from it:** The formal definition of low-degree extensions and algebraic oracles. The distinction between "using arithmetic" (which the encoding obstruction does) and "arithmetizing Boolean functions" (which algebrization captures). Compare with the position-existence argument in barrier-analysis.md, Part 3 and Part 7.

---

## Phase 3: Descriptive Complexity (2 weeks)

### Immerman — *Descriptive Complexity*

This is the field closest to the "formal language for complexity" goal. It characterizes complexity classes by the logical resources needed to express problems.

**Key results:**

| Complexity class | Logical characterization | What it means |
|-----------------|------------------------|---------------|
| P | FO + LFP (first-order logic + least fixed point) | A problem is in P iff it can be expressed with first-order quantifiers plus a fixed-point operator |
| NP | ESO (existential second-order logic) | A problem is in NP iff it can be expressed as "there exist relations such that a first-order property holds" — Fagin's theorem |
| NL | FO + TC (first-order + transitive closure) | Nondeterministic logspace = reachability queries |
| PH | SO (full second-order logic) | The polynomial hierarchy = alternating quantifiers over relations |

**Why this matters for this research:**

- The gap between P and NP is precisely the gap between FO+LFP and ESO — between "definable with fixed points" and "definable with existential second-order quantification"
- The fixed-point operator in P's characterization is directly relevant to the generator fixed-point argument
- The existential quantifier in NP's characterization IS the search — "there exists a witness" is what makes verification cheap and search hard
- Descriptive complexity gives the formal language for talking about what complexity classes ARE, logically — not just what problems they contain

**How to read:** Focus on chapters covering Fagin's theorem, Immerman-Vardi theorem (P = FO+LFP on ordered structures), and the logical characterization of the polynomial hierarchy. The model theory background in early chapters may be needed depending on familiarity.

---

## Phase 4: Category Theory and Proof Theory (ongoing)

These two run in parallel, providing the formal tools for the category-theoretic intuitions (adjunctions, functors, Curry-Howard) that are already present but imprecisely stated.

### Awodey — *Category Theory*

Clean introduction, doesn't assume heavy algebra background. Covers categories, functors, natural transformations, adjunctions, limits, colimits, Yoneda lemma.

**Priority sections:**
- Adjunctions (formalizes the search/verification relationship as an adjunction)
- Limits and colimits (formalizes what "ground state" and "contractibility" mean categorically)
- Yoneda lemma (formalizes the relationship between an object and what it looks like from outside — connects to the eigenvalue/decomposition duality)

### Sorensen & Urzyczyn — *Lectures on the Curry-Howard Isomorphism*

Formalizes the proofs-as-programs correspondence. Covers simply typed lambda calculus, System F, dependent types, and their logical counterparts.

**Priority sections:**
- Simply typed lambda calculus and intuitionistic propositional logic (the base correspondence)
- System F and second-order logic (connects to the ESO characterization of NP)
- Normalization theorems (connects to the confluence/termination results in the framework)

**Why both together:** Awodey gives the structural vocabulary (functors, adjunctions). Sorensen & Urzyczyn give the computational content (proofs = programs). Together they formalize the Curry-Howard-Lambek triple: proofs = programs = morphisms in a category. This is the foundation for stating the Leibniz-verification isomorphism (research direction 5) precisely.

---

## What to Skip

| Resource | Why to skip |
|----------|------------|
| Sipser, *Introduction to the Theory of Computation* | Below current level — covers basics already understood |
| Algorithm textbooks (CLRS, etc.) | Optimization of specific algorithms is not the goal |
| Complexity zoo taxonomy | Reference material, not learning material — look things up as needed |
| Papadimitriou, *Computational Complexity* (1994) | Superseded by Arora & Barak for modern treatment |
| Heavy algebra prerequisites for category theory | Awodey is self-contained enough; add algebra only if specific constructions require it |

---

## How This Connects to Current Research

| Learning target | Research connection |
|----------------|-------------------|
| Formal P/NP/coNP definitions (A&B ch 2) | Precise statement of what the generator argument claims |
| Diagonalization (A&B ch 3) | The coupling argument IS a diagonalization — learning the formal technique will clarify what's needed to make it rigorous |
| Circuit lower bounds (A&B ch 6, 14) | The Leibniz branching factor and normalization depth are circuit-like measures — learning actual circuit lower bound techniques will show whether these can be connected |
| Barrier results (Phase 2) | The barrier analysis in barrier-analysis.md can be made rigorous — confirm or correct the assessments |
| Descriptive complexity (Phase 3) | The "formal language for composition and complexity" goal is exactly what descriptive complexity studies — Immerman will show what's been done and where the open space is |
| Curry-Howard (Phase 4) | Formalizes the proofs-as-programs-as-morphisms triple that the universal proof structure requires |
| Adjunctions (Phase 4) | Formalizes the search/verification relationship categorically — needed for research direction 5 |

---

## Milestones

1. **Can state Cook-Levin theorem precisely and explain why the reduction works** — confirms Phase 1 core understanding
2. **Can explain why each barrier blocks specific proof techniques, with formal definitions** — confirms Phase 2
3. **Can state Fagin's theorem and explain the FO+LFP characterization of P** — confirms Phase 3
4. **Can construct a simple adjunction and explain what the unit/counit do** — confirms Phase 4 category theory
5. **Can state the generator argument in the language of descriptive complexity** — confirms integration

---

## Related

- [encoding-generator-coupling.md](encoding-generator-coupling.md) -- The research directions this learning supports
- [assessment-and-focus.md](assessment-and-focus.md) -- Assessment of current work and gaps
- [../barrier-analysis.md](../barrier-analysis.md) -- Barrier analysis to be formalized after Phase 2
- [../encoding-complexity.md](../encoding-complexity.md) -- P vs NP as encoding execution
- [../../self-representation.md](../../self-representation.md) -- Godel encoding and self-representation
