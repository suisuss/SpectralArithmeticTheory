# Plan: Subdivide the Coupled Case — CoupledAnalysis.lean

## Context

The JIT pipeline (JIT.lean) classifies terms into base cases, with `coupled` as the catch-all for `obs(compose(C₁, C₂))` where C₁ and C₂ share structural sub-terms. We set out to subdivide `coupled` into "weakly coupled" (tractable) vs "strongly coupled" (hard).

**Critical empirical finding from exploration**: For every concrete example tested — shallow/deep sharing, single/multiple shared sub-terms, adversarial nesting — coupled and independent terms produce **identical normalization depth and term size at every pass**. The `deepRewrite` function processes each `obs(compose)` site independently regardless of whether sub-terms are shared.

**What this means**: The coupled/indep distinction is a **phantom category** at the individual term level. Coupling only matters across the assignment space — it's about how many assignments a solver must explore, not about the cost of normalizing any single assignment's term.

**The right subdivision** is therefore not about term-level structural properties, but about the **constraint graph** of the formula being encoded. This is the graph-theoretic structure that determines SAT hardness:
- Tree-structured constraints → polynomial (like 2-SAT)
- Bounded treewidth → fixed-parameter tractable
- Unbounded treewidth → 3-SAT hardness

## What to Build: `SpectralArithmetic/Obstruction/CoupledAnalysis.lean`

### Step 1: Prove the Coupling Invariance Theorem

The key negative result: coupling doesn't affect individual term normalization.

```lean
-- For concrete paired examples, prove normalization equivalence
theorem coupled_indep_same_depth_d1 : ...  -- depth 2 = depth 2
theorem coupled_indep_same_depth_d2 : ...  -- depth 3 = depth 3
theorem coupled_indep_same_depth_d3 : ...  -- depth 4 = depth 4
theorem coupled_indep_same_size_d1 : ...   -- sizes match at every pass
```

This establishes that `sharesStructure` detects a property irrelevant to single-term normalization cost.

### Step 2: Constraint Graph Analysis (Formula-Level)

Move from term-level to formula-level analysis. Define the variable-clause incidence graph and structural properties.

```lean
/-- The constraint graph of a CNF formula: variables as nodes,
    edges between variables that co-occur in a clause. -/
def constraintGraph (φ : CNFFormula) : List (Nat × Nat)

/-- Degree of a variable in the constraint graph. -/
def varDegree (φ : CNFFormula) (v : Nat) : Nat

/-- Maximum variable degree in the formula. -/
def maxDegree (φ : CNFFormula) : Nat

/-- Coupling density: ratio of shared variable pairs to total clause pairs. -/
def couplingDensity (φ : CNFFormula) : Nat  -- numerator of fraction
```

### Step 3: Coupling Subdivision at the Formula Level

```lean
/-- Coupling structure classification for a CNF formula. -/
inductive CouplingType where
  | independent : CouplingType    -- no shared variables (product structure)
  | treelike    : CouplingType    -- each variable in ≤ 2 clauses (2-SAT-like)
  | bounded     : Nat → CouplingType  -- bounded max degree
  | dense       : CouplingType    -- unbounded degree (3-SAT territory)
  deriving Repr, DecidableEq

/-- Classify a formula's coupling structure. -/
def classifyCoupling (φ : CNFFormula) : CouplingType
```

### Step 4: Assignment Space Analysis

The cost that coupling affects: how many assignments must be checked.

```lean
/-- For independent formulas, satisfiability decomposes:
    the formula is satisfiable iff each clause is independently satisfiable. -/
theorem independent_decomposition (φ : CNFFormula)
    (h : isIndependent φ = true) : ...

/-- For tree-structured formulas, variable dependencies form a tree.
    Satisfiability is decidable by tree traversal (linear in |φ|). -/
-- This connects to why 2-SAT is in P.

/-- Dense coupling: the number of distinct terms across assignments
    can grow exponentially with the number of shared variables. -/
def distinctTermCount (φ : CNFFormula) : Nat  -- count distinct formulaToTerm outputs
```

### Step 5: Concrete Examples and Tests

```lean
-- Tree-like formula: (x₀∧x₁) ∧ (x₁∧x₂) ∧ (x₂∧x₃) — chain structure
def treelike3 : CNFFormula := ...

-- Dense formula: (x₀∧x₁∧x₂) ∧ (x₀∧x₁∧x₃) ∧ (x₀∧x₂∧x₃) — x₀ in every clause
def dense3 : CNFFormula := ...

-- Classification tests
#eval classifyCoupling indep2x2      -- independent
#eval classifyCoupling share2x2      -- treelike
#eval classifyCoupling treelike3     -- treelike
#eval classifyCoupling dense3        -- dense

-- The invariance: same normalization per assignment
-- but different numbers of "interesting" assignments
```

### Step 6: Document the Phantom Category Finding

Update `BaseCase.coupled` in JIT.lean:
- Change the doc comment to note that coupling is a formula-level (assignment-space) property, not a term-level property
- The `coupled` sentinel depth of 0 is actually wrong in a different way than expected: it's not "unknown" — it's "same as indep for any concrete term"

## Files to Modify

| File | Change |
|------|--------|
| `SpectralArithmetic/Obstruction/CoupledAnalysis.lean` | **New**: coupling invariance, constraint graph, formula-level subdivision |
| `SpectralArithmetic/Obstruction/JIT.lean` | Update `coupled` doc comments to reflect phantom finding |
| `SpectralArithmetic.lean` | Add import |
| `docs/theory/computation/pvsnp/nand-jit-obs-placement.md` | Update coupled case section with findings |

## Verification

1. `lake build` — zero errors, zero sorry
2. Coupling invariance theorems pass `by decide`
3. `classifyCoupling` correctly classifies all test formulas
4. `#eval` tests demonstrate same normalization cost across coupling types for fixed assignments

## What This Means for the Three Paths

The empirical finding clarifies the three paths forward:

1. **Approximation**: SAT solver heuristics are about navigating the assignment space efficiently, not about per-term normalization cost. The framework models this as: "which assignment produces a term where z appears at strategic positions?"

2. **Fundamental theorem**: Would need to show that constraint graph structure determines assignment space exploration cost. For tree-structured constraints, this is known (2-SAT is in P). The framework could formalize this as: tree-like coupling → polynomial number of "distinct" normalization patterns across assignments.

3. **Impossibility**: Would need to show that dense coupling forces exponential assignment space exploration. The framework's contribution: the normalization cost per assignment is polynomial (compose chain depth), but the NUMBER of assignments that must be tested is the hard part. This is the counting/search problem, not the normalization problem.
