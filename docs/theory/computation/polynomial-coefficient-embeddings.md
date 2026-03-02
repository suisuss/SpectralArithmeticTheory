# Polynomial Coefficient Embeddings: The Design Space for Deterministic SAT

## The Setup

Every CNF clause can be represented as a multilinear polynomial over {0,1}^n:

```
(x₀ ∨ x₁)     →  1 - (1-x₀)(1-x₁)  =  x₀ + x₁ - x₀x₁
(¬x₀ ∨ x₂)    →  1 - x₀(1-x₂)      =  1 - x₀ + x₀x₂
(¬x₁ ∨ ¬x₂)   →  1 - x₁x₂
```

Each clause polynomial evaluates to 1 when the clause is satisfied, 0 when violated. The formula polynomial is the product of clause polynomials: it equals 1 on SAT assignments, 0 on UNSAT.

In the monomial basis {1, x₀, x₁, x₀x₁, x₂, x₀x₂, x₁x₂, x₀x₁x₂}, each clause becomes a **coefficient vector**:

```
C₁: [0, 1, 1, -1, 0, 0, 0, 0]
C₂: [1, -1, 0, 0, 0, 1, 0, 0]
C₃: [1, 0, 0, 0, 0, 0, -1, 0]
```

A k-clause over n variables has at most C(n,0) + C(n,1) + ... + C(n,k) = O(n^k) monomials. For fixed k, each coefficient vector is **polynomial size and fully decodable** — you can reconstruct the exact clause from its coefficients.

---

## The Multiplication Problem

AND of clauses corresponds to polynomial multiplication:

```
formula(x) = C₁(x) · C₂(x) · C₃(x)
```

The product of m degree-k polynomials has degree mk. Its coefficient vector lives in a space of dimension O(n^{mk}). For m = O(n) clauses, this is exponential.

Satisfiability reduces to: is the product polynomial nonzero on {0,1}^n? But constructing the product explicitly is exponential-time.

This is the **Nullstellensatz proof system**. The clause polynomials are generators of an ideal I. The formula is unsatisfiable iff 1 ∈ I + ⟨x₁² - x₁, ..., xₙ² - xₙ⟩. Checking this at degree d is a linear algebra problem of dimension O(n^d). Ben-Sasson and Wigderson proved hard instances require d = Ω(n), giving exponential dimension.

---

## The Key Insight: Don't Multiply

The degree blowup comes from forming the product. What if you never do that?

Keep the clause polynomials as a **collection** of coefficient vectors — a matrix A ∈ Z^{m × D} where D = O(n^k) and each row is a clause's coefficient vector. This representation is:

- **Polynomial size**: O(m · n^k) entries
- **Lossless**: every clause is fully recoverable from its coefficient vector
- **Decodable**: the coefficient vector determines the clause uniquely

The question becomes: **is there a polynomial-time computable property of the collection A that determines satisfiability?**

---

## What Works for Special Cases

### XOR-SAT (P)

Clause polynomials are degree 1 (linear):
- x₀ ⊕ x₁ ⊕ x₂ = 1  →  polynomial: x₀ + x₁ + x₂ - 2x₀x₁ - 2x₀x₂ - 2x₁x₂ + 4x₀x₁x₂

Actually, working over GF(2), XOR is just addition:
- x₀ ⊕ x₁ ⊕ x₂ = 1  →  x₀ + x₁ + x₂ = 1 (mod 2)

The coefficient vectors are rows of a matrix over GF(2). AND of XOR clauses = system of linear equations. Satisfiability = rank condition on the augmented matrix. **Polynomial time via Gaussian elimination.**

Key property: AND of linear constraints remains linear. No degree blowup.

### 2-SAT (P)

Clause polynomials are degree 2:
- (x₀ ∨ x₁)  →  x₀ + x₁ - x₀x₁

The implication graph encodes pairwise interactions between literals. Each 2-clause (a ∨ b) generates two implications: ¬a → b and ¬b → a. Satisfiability = no variable and its negation in the same strongly connected component.

The implication graph **is** a structured summary of the clause coefficient vectors' overlap structure. Satisfiability is a graph property (SCC analysis) computable in linear time.

### Horn-SAT (P)

Horn clauses have at most one positive literal. Their polynomials have a monotonicity structure that enables unit propagation — iterative linear operations on the coefficient vectors that determine satisfiability in linear time.

### Bounded treewidth (P)

When the clause-variable incidence graph has bounded treewidth w, the interaction between clauses decomposes along a tree. The product polynomial can be computed along the tree decomposition with intermediate results of size O(n^w). For bounded w, this is polynomial. This is equivalent to polynomial-size tensor networks.

### The Pattern

Every tractable SAT fragment has a polynomial-time computable property of the clause coefficient vectors that determines satisfiability. The property always exploits some structural restriction on how clauses interact:

| Fragment | Interaction structure | Method | Time |
|----------|----------------------|--------|------|
| XOR-SAT | Linear (degree 1) | Gaussian elimination | O(n³) |
| 2-SAT | Implication graph | SCC analysis | O(n+m) |
| Horn-SAT | Monotone propagation | Unit propagation | O(n+m) |
| Treewidth w | Tree decomposition | Dynamic programming | O(n^{w+1}) |
| General k-SAT | Unrestricted | ??? | NP-hard |

---

## The Design Space: Five Approaches

### Approach 1: Clause Interaction Matrix

Compute an algebraic interaction score between each pair of clauses from their coefficient vectors. Build a weighted graph G where edge (i,j) encodes how clauses Cᵢ and Cⱼ constrain each other through shared variables.

**Concrete construction**: For clauses Cᵢ, Cⱼ with coefficient vectors vᵢ, vⱼ, define:
- Support overlap: which monomials appear in both
- Variable overlap: which variables appear in both clauses
- Tension: do shared variables appear with conflicting polarities?
- Algebraic inner product: vᵢ · vⱼ in the monomial basis

2-SAT's implication graph is exactly this — a specific clause interaction graph where satisfiability reduces to SCC analysis. The question: is there a richer interaction graph for 3-SAT where satisfiability is still a graph property?

**What's known**: Resolution width lower bounds (Ben-Sasson, Wigderson 2001) show that for random 3-SAT near the threshold, any tree-like resolution proof requires exponential size. This implies that pairwise clause interactions are insufficient — you need to reason about interactions among triples, quadruples, etc. The interaction "graph" would need to be a hypergraph, and its analysis would be at least as expensive as the original problem.

### Approach 2: Iterative Projection

Start with the full solution space {0,1}^n. Process each clause one at a time. At each step, maintain a polynomial-size summary of the remaining feasible region. The summary must be:
- Computable from the previous summary + the new clause's coefficient vector
- Faithful: it correctly distinguishes empty from nonempty feasible regions

This is what DPLL/CDCL solvers do, with the summary being a partial assignment + learned clauses. The problem: the set of learned clauses can grow exponentially (CDCL proof complexity lower bounds).

**What would a better summary look like?** Some options:
- A low-rank approximation of the feasible region's indicator polynomial
- A moment vector: expected values of low-degree monomials over the feasible region
- A spectral summary: eigenvalues of a constraint matrix updated at each step

The Sherali-Adams and Lasserre hierarchies implement the moment vector approach. At level d, you maintain all moments up to degree d, which is O(n^d) numbers. At level n, this is exact (and exponential). For hard instances, Ω(n) levels are needed (Grigoriev 2001, Schoenebeck 2008).

### Approach 3: Algebraic Invariants of the Ideal

The clause polynomials {p₁, ..., pₘ} together with the Boolean axioms {xᵢ² - xᵢ} generate an ideal I in the polynomial ring. The formula is satisfiable iff the variety V(I) is nonempty.

Algebraic invariants of I — the Hilbert function, the dimension of V(I), the degree of V(I) — encode satisfiability information. If you could compute any of these from the generators in polynomial time, you'd decide SAT.

**What's known**: Computing the Hilbert function of a general ideal is EXPSPACE-hard (Mayr, Meyer 1982). For Boolean ideals (with the xᵢ² - xᵢ relations), the variety is always finite (subset of {0,1}^n), so dimension is always 0 and degree equals the number of satisfying assignments. Computing the degree is #P-hard (counting solutions).

However, distinguishing "degree = 0" (UNSAT) from "degree ≥ 1" (SAT) might be easier than computing the exact degree. This is the decision vs counting gap. No polynomial-time method is known for this distinction in general.

### Approach 4: Spectral Analysis of the Coefficient Matrix

Stack the clause coefficient vectors as rows of a matrix A ∈ Z^{m × D} where D = O(n^k). The column space, null space, and singular values of A encode how clauses interact through the monomial basis.

**Concrete properties**:
- rank(A): how many independent constraints the clauses impose
- Null space of A: monomials that are "invisible" to all clauses
- Singular value distribution: the "spectral complexity" of the constraint system
- A^T A (Gram matrix in monomial space): monomial interaction structure

For XOR-SAT, A is a matrix over GF(2) and rank directly determines satisfiability. For general CNF, the relationship between rank/spectrum and satisfiability is unclear.

**Experimental direction**: For the test formulas with known satisfiability, compute A and its spectral properties. Check whether any spectral threshold separates SAT from UNSAT formulas. This is testable in the existing Lean framework by constructing A from the clause polynomials and computing rank/trace/diagonal.

### Approach 5: Structured Evaluation Schemes

Instead of evaluating the product polynomial at random points (Shamir), evaluate at a polynomial number of carefully chosen deterministic points. The points would be chosen based on the formula structure (the clause coefficient vectors) to maximize information extraction.

This is the derandomization question: can we replace the random oracle in IP = PSPACE with a deterministic construction?

**What's known**: Nisan-Wigderson (1994) showed that derandomization of BPP follows from circuit lower bounds. If E = DTIME(2^{O(n)}) has exponential circuit complexity, then BPP = P. This doesn't directly apply to IP protocols, but it suggests that sufficiently strong circuit lower bounds would yield deterministic point-selection strategies.

**Concrete construction**: Use the formula's incidence structure to select evaluation points. For example:
- Evaluate each clause polynomial at all n unit vectors eᵢ — this gives the "sensitivity" of each clause to each variable
- Evaluate at pairwise interaction points eᵢ + eⱼ — this captures two-variable interactions
- Continue to higher-order interactions until satisfiability is determined

This produces O(n^k) evaluation points, each revealing degree-k interactions. The question: does this polynomial number of evaluations determine satisfiability?

---

## Connection to the Derivation Barrier

The derivation barrier (formalized in `derivation-barrier.md`) identifies scalar observation through a derivation as insufficient for separating SAT from UNSAT. The polynomial coefficient approach reframes this:

- **Scalar observation** = evaluating the product polynomial at a single point (or taking a single linear functional of the coefficient vector). The derivation barrier shows this fails.

- **Vector observation** = evaluating at multiple points or taking multiple linear functionals. The depth profile (verified in `DepthProfile.lean`) shows that O(1) evaluation points suffice for the 3-variable formula.

- **Full polynomial** = the entire coefficient vector. This trivially determines satisfiability but is exponential-size.

The question is: **what is the minimum number of "evaluation points" (linear functionals of the coefficient vector) needed to determine satisfiability, as a function of formula size?**

If this number is polynomial: P = NP.
If this number is necessarily exponential: P ≠ NP.
If this number is polynomial with randomized choices: IP = PSPACE (known).

---

## Connection to Verified Results

### Incidence matrix as degree-1 truncation

The incidence matrix M ∈ Z^{m×n} from `VectorEmbed.lean` is exactly the degree-1 part of the coefficient matrix A. Each row records the linear coefficients of a clause polynomial, ignoring constant and higher-degree terms:

```
C₁: x₀ + x₁ - x₀x₁  →  degree-1 part: [1, 1, 0]  (= incidence row)
C₂: 1 - x₀ + x₀x₂    →  degree-1 part: [-1, 0, 1]  (= incidence row)
C₃: 1 - x₁x₂          →  degree-1 part: [0, -1, -1] (= incidence row... wait)
```

For C₃ = 1 - x₁x₂: the degree-1 part is actually [0, 0, 0] (no linear terms). The incidence matrix records literal polarities, which is related but not identical to the polynomial's degree-1 coefficients when negated variables are involved.

More precisely: the incidence matrix encodes the linear part of the **clause function written as an affine function of the signed variables yᵢ = 2xᵢ - 1**. The polynomial coefficient matrix works in the {0,1} basis. These are related by a change of basis.

### Rank-dimension results

For phi (3-clause, 3-var):
- Incidence matrix rank: 2
- Depth profile min separating dimension: 2
- Polynomial coefficient matrix A (full, 3 × 8): rank ≤ 3

For phi4chain (4-clause, 4-var):
- Incidence matrix rank: 3
- Depth profile min separating dimension: 2 (rank-dimension conjecture refuted)
- The depth profile captures a DIFFERENT invariant than incidence rank

The refutation of the rank-dimension conjecture (`DepthProfile4.lean`) shows that the DynSemiring normalization process extracts information along different axes than the linear algebra of the incidence matrix. The depth profile is sensitive to (x₀, truecount(x₁,x₂,x₃)) — an asymmetric decomposition determined by the encoding structure, not the formula's linear algebra.

---

## The Wall

Every approach above either:
1. Works for a restricted fragment (XOR, 2-SAT, Horn, bounded treewidth) and breaks for general 3-SAT
2. Works for general 3-SAT but requires exponential resources for hard instances
3. Works with randomness (IP = PSPACE) but not deterministically

The known impossibility results:
- **Nullstellensatz degree lower bounds**: hard instances need degree Ω(n) (Ben-Sasson, Wigderson)
- **Sherali-Adams/Lasserre lower bounds**: hard instances need Ω(n) levels (Grigoriev, Schoenebeck)
- **Extended formulation lower bounds**: any linear program for SAT has exponential size (Fiorini et al.)
- **Resolution width lower bounds**: random 3-SAT near threshold requires exponential-length proofs

These results don't rule out ALL polynomial-time approaches — they rule out specific proof systems and relaxation hierarchies. A fundamentally different approach (not captured by any of these lower bounds) remains possible.

**What would need to be true**: A polynomial-time SAT algorithm would need to exploit global structure of the clause coefficient matrix that is invisible to:
- Degree-bounded ideal membership tests (evades Nullstellensatz)
- Moment-based relaxations (evades Lasserre)
- Linear extensions (evades Fiorini et al.)
- Tree-like reasoning (evades resolution)

The gap between "these specific approaches fail" and "all approaches fail" is exactly the P vs NP question.

---

## Experimental Next Steps

1. **Construct the full coefficient matrix A** for the test formulas in Lean. Each clause becomes a row in the monomial basis. Compare rank(A) with incidence rank and depth profile dimension.

2. **Test Approach 4** (spectral analysis): compute singular values of A for SAT vs UNSAT formulas. Check whether any spectral property separates.

3. **Test Approach 1** (clause interaction): compute pairwise algebraic inner products vᵢ · vⱼ for the test formulas. Build the interaction graph. Check whether graph properties (connectivity, spectral gap) correlate with satisfiability.

4. **Test Approach 5** (structured evaluation): evaluate clause polynomials at unit vectors and pairwise points. Check whether the evaluation table determines satisfiability without forming the product.
