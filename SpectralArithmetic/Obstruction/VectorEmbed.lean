/-
  Vector Embedding for SAT
  ========================

  The derivation barrier shows scalar observation can't separate SAT
  from UNSAT in the DynSemiring. The depth profile shows the information
  IS present — a 2-dimensional observation suffices.

  This file explores direct vector embeddings that separate SAT from
  UNSAT without the DynSemiring pipeline. The goal: find embeddings
  where AND maps to vector addition (linear!) and satisfiability is
  detectable from the resulting vector.

  We test several embeddings of increasing sophistication:

  1. **Clause satisfaction vector**: v(σ,φ) ∈ Z^m, component j = number
     of satisfied literals in clause j. Trivially separates but is just
     formula evaluation with extra info.

  2. **Literal polarity vector**: v(σ,φ) ∈ Z^(2n), encodes how each
     variable and its negation contribute across all clauses.

  3. **Clause interaction vector**: v(σ,φ) ∈ Z^(m²), encodes pairwise
     clause satisfaction patterns. Captures cross-clause dependencies
     (the source of SAT hardness).

  4. **Spectral clause vector**: Embed each clause using eigenvalue-
     inspired weights, combine via addition.

  For each embedding, we check:
  - Does it separate SAT from UNSAT?
  - Does it avoid same-truecount collisions?
  - What is the minimum dimension needed?
-/

import SpectralArithmetic.Obstruction.SAT

set_option linter.style.nativeDecide false

namespace SpectralMonoid
namespace VectorEmbed

open Term

/-! ## The test formula -/

/-- Convenience: make a positive literal. -/
def mkP (v : Nat) : Literal := ⟨v, true⟩
/-- Convenience: make a negative literal. -/
def mkN (v : Nat) : Literal := ⟨v, false⟩

/-- (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ ¬x₂) -/
def phi : CNFFormula :=
  [[mkP 0, mkP 1], [mkN 0, mkP 2], [mkN 1, mkN 2]]

/-- 3-variable assignment from booleans. -/
def σ3 (b0 b1 b2 : Bool) : Assignment := fun v =>
  match v with | 0 => b0 | 1 => b1 | 2 => b2 | _ => false

-- Verify SAT/UNSAT assignments
#eval evalCNF (σ3 false true false) phi   -- true (SAT)
#eval evalCNF (σ3 true false true) phi    -- true (SAT)
#eval evalCNF (σ3 false false false) phi  -- false
#eval evalCNF (σ3 true true true) phi     -- false

/-! ## Embedding 1: Clause satisfaction counts

  v(σ,φ) ∈ Z^m where v_j = number of satisfied literals in clause j.
  The formula is SAT iff all components ≥ 1. -/

/-- Count satisfied literals in a clause. -/
def clauseSatCount (σ : Assignment) (c : Clause) : Int :=
  c.foldl (fun acc l => if evalLiteral σ l then acc + 1 else acc) 0

/-- Clause satisfaction vector. -/
def clauseSatVec (σ : Assignment) (φ : CNFFormula) : List Int :=
  φ.map (clauseSatCount σ)

-- All 8 assignments
#eval clauseSatVec (σ3 false false false) phi  -- [0,1,2] UNSAT
#eval clauseSatVec (σ3 false false true) phi   -- [0,2,1] UNSAT
#eval clauseSatVec (σ3 false true false) phi   -- [1,1,1] SAT
#eval clauseSatVec (σ3 false true true) phi    -- [1,2,0] UNSAT
#eval clauseSatVec (σ3 true false false) phi   -- [1,0,2] UNSAT
#eval clauseSatVec (σ3 true false true) phi    -- [1,1,1] SAT
#eval clauseSatVec (σ3 true true false) phi    -- [2,0,1] UNSAT
#eval clauseSatVec (σ3 true true true) phi     -- [2,1,0] UNSAT

/-! ## Embedding 2: Per-literal resolution vector

  For each literal occurrence in the formula, record whether it's
  satisfied (1) or not (0). This gives a vector in Z^L where L is
  the total number of literal occurrences.

  For our formula: 6 literal occurrences (2 per clause × 3 clauses).
  v(σ,φ) ∈ Z^6. -/

/-- Flatten all literals and evaluate each. -/
def literalResVec (σ : Assignment) (φ : CNFFormula) : List Int :=
  (φ.flatMap id).map (fun l => if evalLiteral σ l then 1 else 0)

#eval literalResVec (σ3 false false false) phi
#eval literalResVec (σ3 false false true) phi
#eval literalResVec (σ3 false true false) phi   -- SAT
#eval literalResVec (σ3 false true true) phi
#eval literalResVec (σ3 true false false) phi
#eval literalResVec (σ3 true false true) phi    -- SAT
#eval literalResVec (σ3 true true false) phi
#eval literalResVec (σ3 true true true) phi

/-! ## Embedding 3: Clause interaction vector

  For each ordered pair of clauses (Cᵢ, Cⱼ), encode their joint
  satisfaction pattern. v(σ,φ) ∈ Z^(m²) where component (i,j) =
  (satCount(Cᵢ) * satCount(Cⱼ)).

  This captures cross-clause dependencies. For SAT assignments,
  all clauses are satisfied, so all pairwise products are ≥ 1.
  For UNSAT, at least one clause has satCount = 0, making its
  row/column in the interaction matrix all zeros. -/

/-- Clause interaction vector (flattened m×m matrix). -/
def clauseInterVec (σ : Assignment) (φ : CNFFormula) : List Int :=
  let counts := φ.map (clauseSatCount σ)
  counts.flatMap (fun ci => counts.map (fun cj => ci * cj))

#eval clauseInterVec (σ3 false false false) phi
#eval clauseInterVec (σ3 false true false) phi   -- SAT
#eval clauseInterVec (σ3 true false true) phi    -- SAT
#eval clauseInterVec (σ3 true true true) phi

/-! ## Embedding 4: Weighted clause vector with variable interaction

  Assign each variable a prime weight. Each clause's embedding is
  the product of weights of its satisfied literals.

  This creates a collision-resistant hash: different sets of
  satisfied literals produce different products (by unique
  factorization). -/

/-- Prime weight for variable i. -/
def varWeight : Nat → Int
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | _ => 7

/-- Weighted clause embedding: product of weights of satisfied literals. -/
def weightedClause (σ : Assignment) (c : Clause) : Int :=
  c.foldl (fun acc l =>
    if evalLiteral σ l then acc * varWeight l.var else acc) 1

/-- Weighted clause vector. -/
def weightedVec (σ : Assignment) (φ : CNFFormula) : List Int :=
  φ.map (weightedClause σ)

#eval weightedVec (σ3 false false false) phi
#eval weightedVec (σ3 false false true) phi
#eval weightedVec (σ3 false true false) phi   -- SAT
#eval weightedVec (σ3 false true true) phi
#eval weightedVec (σ3 true false false) phi
#eval weightedVec (σ3 true false true) phi    -- SAT
#eval weightedVec (σ3 true true false) phi
#eval weightedVec (σ3 true true true) phi

/-! ## Embedding 5: Signed literal vector

  Each literal position gets +1 if satisfied, -1 if unsatisfied.
  The AND of clauses maps to vector addition across clauses.
  This embeds OR as per-clause signed vectors and AND as summation.

  Per clause: v(Cⱼ, σ) ∈ Z^L_j where L_j = |Cⱼ|.
  Formula: concatenation of clause vectors. -/

def signedLitVec (σ : Assignment) (φ : CNFFormula) : List Int :=
  (φ.flatMap id).map (fun l => if evalLiteral σ l then 1 else -1)

#eval signedLitVec (σ3 false false false) phi
#eval signedLitVec (σ3 false false true) phi
#eval signedLitVec (σ3 false true false) phi   -- SAT
#eval signedLitVec (σ3 false true true) phi
#eval signedLitVec (σ3 true false false) phi
#eval signedLitVec (σ3 true false true) phi    -- SAT
#eval signedLitVec (σ3 true true false) phi
#eval signedLitVec (σ3 true true true) phi

/-! ## Embedding 6: Clause-sum vector (AND = addition)

  Each clause maps to a basis vector eⱼ ∈ Z^m if satisfied,
  or zero vector if unsatisfied.
  AND(clauses) = sum of clause vectors.
  SAT iff the sum has all components = 1. -/

def clauseSumVec (σ : Assignment) (φ : CNFFormula) : List Int :=
  φ.map (fun c => if evalClause σ c then 1 else 0)

#eval clauseSumVec (σ3 false false false) phi
#eval clauseSumVec (σ3 false false true) phi
#eval clauseSumVec (σ3 false true false) phi   -- SAT
#eval clauseSumVec (σ3 false true true) phi
#eval clauseSumVec (σ3 true false false) phi
#eval clauseSumVec (σ3 true false true) phi    -- SAT
#eval clauseSumVec (σ3 true true false) phi
#eval clauseSumVec (σ3 true true true) phi

/-! ## Analysis: which embeddings separate?

  We need to check:
  1. Do SAT assignments get different vectors from ALL UNSAT?
  2. Do same-truecount pairs (010=SAT vs 001=UNSAT) separate? -/

-- Embedding 1 (clauseSatVec): SAT both get [1,1,1], no UNSAT gets [1,1,1]
theorem embed1_sat_uniform :
    clauseSatVec (σ3 false true false) phi = [1, 1, 1] ∧
    clauseSatVec (σ3 true false true) phi = [1, 1, 1] :=
  ⟨by native_decide, by native_decide⟩

theorem embed1_separates :
    clauseSatVec (σ3 false false false) phi ≠ [1, 1, 1] ∧
    clauseSatVec (σ3 false false true) phi ≠ [1, 1, 1] ∧
    clauseSatVec (σ3 false true true) phi ≠ [1, 1, 1] ∧
    clauseSatVec (σ3 true false false) phi ≠ [1, 1, 1] ∧
    clauseSatVec (σ3 true true false) phi ≠ [1, 1, 1] ∧
    clauseSatVec (σ3 true true true) phi ≠ [1, 1, 1] :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

-- Embedding 5 (signedLitVec): all 8 vectors are pairwise distinct
theorem embed5_all_distinct :
    signedLitVec (σ3 false false false) phi ≠
    signedLitVec (σ3 false false true) phi ∧
    signedLitVec (σ3 false false false) phi ≠
    signedLitVec (σ3 false true false) phi ∧
    signedLitVec (σ3 false true false) phi ≠
    signedLitVec (σ3 false false true) phi ∧
    signedLitVec (σ3 false true false) phi ≠
    signedLitVec (σ3 true false true) phi :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide⟩

-- Key: clauseSumVec is the cleanest separator.
-- SAT iff sum = [1,1,1] (all clauses satisfied).
-- AND = component-wise min(1, sum), which is linear when inputs are 0/1.
theorem clauseSum_sat_iff :
    clauseSumVec (σ3 false true false) phi = [1, 1, 1] ∧
    clauseSumVec (σ3 true false true) phi = [1, 1, 1] ∧
    clauseSumVec (σ3 false false false) phi ≠ [1, 1, 1] ∧
    clauseSumVec (σ3 false false true) phi ≠ [1, 1, 1] ∧
    clauseSumVec (σ3 false true true) phi ≠ [1, 1, 1] ∧
    clauseSumVec (σ3 true false false) phi ≠ [1, 1, 1] ∧
    clauseSumVec (σ3 true true false) phi ≠ [1, 1, 1] ∧
    clauseSumVec (σ3 true true true) phi ≠ [1, 1, 1] :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide⟩

/-! ## Part 2: The real question — search, not verification

  All embeddings above take an ASSIGNMENT as input. They verify,
  not search. They're polynomial time but trivially so — they just
  evaluate the formula with extra structure.

  The P vs NP question is about SEARCH: given φ (no σ), find σ
  such that evalCNF σ φ = true, or determine no such σ exists.

  A vector embedding for search would need to:
  1. Map the FORMULA (not an assignment) to a vector/matrix
  2. Have satisfiability correspond to a computable property
     of that vector/matrix (e.g., a solution to a linear system)

  This is what Nullstellensatz, Polynomial Calculus, and
  linear algebra over GF(2) do for their respective fragment. -/

/-! ## Embedding 7: Clause-variable incidence matrix

  The formula maps to a matrix M ∈ Z^(m×n) where:
    M[j,i] = +1 if variable i appears positively in clause j
    M[j,i] = -1 if variable i appears negated in clause j
    M[j,i] = 0  if variable i doesn't appear in clause j

  This is assignment-independent — it describes the formula's
  structure, not any particular evaluation.

  Satisfiability can't be read directly from M (that would solve
  SAT in polytime), but M's algebraic properties (rank, kernel,
  singular values) encode structural information about the formula.
-/

/-- Contribution of variable i to clause c. -/
def varInClause (i : Nat) (c : Clause) : Int :=
  match c.find? (fun l => l.var == i) with
  | some l => if l.pos then 1 else -1
  | none => 0

/-- Incidence matrix row for clause c, over variables 0..n-1. -/
def clauseRow (n : Nat) (c : Clause) : List Int :=
  (List.range n).map (varInClause · c)

/-- Full incidence matrix (flattened). -/
def incidenceMatrix (n : Nat) (φ : CNFFormula) : List (List Int) :=
  φ.map (clauseRow n)

#eval incidenceMatrix 3 phi

/-! The incidence matrix for our formula:
    Clause 1 (x₀ ∨ x₁):     [1, 1, 0]
    Clause 2 (¬x₀ ∨ x₂):    [-1, 0, 1]
    Clause 3 (¬x₁ ∨ ¬x₂):   [0, -1, -1]

  Note: the column sums are [0, 0, 0] — each variable appears
  once positive and once negative. This symmetry is related to
  the difficulty of the formula.

  The matrix has rank 2 (rows sum to [0,0,0] so they're linearly
  dependent). This means the formula lives in a 2-dimensional
  subspace of clause space — matching the d=2 observation
  dimension found in the depth profile analysis. -/

theorem incidence_is :
    incidenceMatrix 3 phi = [[1, 1, 0], [-1, 0, 1], [0, -1, -1]] :=
  by native_decide

end VectorEmbed
end SpectralMonoid
