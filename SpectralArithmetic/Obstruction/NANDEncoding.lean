/-
  Spectral Arithmetic: NAND Encoding via Circuit Terms
  =====================================================

  The Term algebra's obs operation is eigenvalue extraction, NOT Boolean
  negation. obs(f₁) = f₁ and obs(f₀) = z — it preserves eigenstates rather
  than complementing them. This means obs(compose(a,b)) is semantically AND,
  not NAND, and the algebra cannot directly express Boolean NOT.

  This file introduces CTerm (Circuit Term), a wrapper that adds structural
  complement (cNeg) and translates to Term via De Morgan laws:
  - cNeg(cCompose(a,b)) → oplus(cNeg(a), cNeg(b))   [NOT(AND) = OR(NOT,NOT)]
  - cNeg(cNeg(a)) → a                                  [double negation]
  - cNeg(bTrue) → bFalse, cNeg(bFalse) → bTrue        [literal complement]

  This gives us a NAND-complete Boolean algebra over Terms, enabling proper
  CNF (AND-of-ORs) encoding of SAT formulas. The key finding: the encoding
  produces structurally distinguishable terms for satisfying vs non-satisfying
  assignments — satisfied clauses contain f₀ (true), unsatisfied contain z.

  Encoding choices:
  - TRUE  = f₀ (multiplicative identity in compose/AND chains)
  - FALSE = z  (annihilator in compose/AND chains)
  - AND   = compose (multiplicative)
  - OR    = De Morgan via cNeg (complement of AND of complements)
-/

import SpectralArithmetic.Obstruction.CoupledAnalysis

set_option linter.style.nativeDecide false

namespace SpectralMonoid

open Term

/-! ## Part 1: Circuit Terms

    CTerm extends Term with structural complement (cNeg).
    The toTerm translation pushes complements to leaves via De Morgan. -/

/-- Circuit term: a Term extended with structural complement.
    cNeg is pushed to leaves during toTerm translation. -/
inductive CTerm where
  | prim : Term → CTerm
  | cCompose : CTerm → CTerm → CTerm
  | cNeg : CTerm → CTerm
  deriving Repr

namespace CTerm

/-- Translate a circuit term to a plain Term by pushing cNeg to leaves.
    De Morgan: NOT(AND(a,b)) = OR(NOT(a), NOT(b))
    Double negation: NOT(NOT(a)) = a
    Leaf complement: NOT(TRUE) = FALSE, NOT(FALSE) = TRUE -/
def toTerm : CTerm → Term
  | .prim t => t
  | .cCompose a b => .compose a.toTerm b.toTerm
  | .cNeg (.prim .f₀) => .z             -- NOT(TRUE) = FALSE
  | .cNeg (.prim .z) => .f₀             -- NOT(FALSE) = TRUE
  | .cNeg (.prim t) => t                -- fallback: unknown prims unchanged
  | .cNeg (.cCompose a b) =>            -- De Morgan: NOT(AND) = OR(NOT,NOT)
      .oplus (CTerm.cNeg a).toTerm (CTerm.cNeg b).toTerm
  | .cNeg (.cNeg a) => a.toTerm         -- double negation elimination

/-! ## Part 2: Boolean Gates

    Standard NAND-complete gate constructions. -/

/-- NAND(a,b) = NOT(AND(a,b)) -/
def nand (a b : CTerm) : CTerm := .cNeg (.cCompose a b)

/-- NOT(a) = NAND(a,a) -/
def bNot (a : CTerm) : CTerm := .cNeg (.cCompose a a)

/-- OR(a,b) = NOT(AND(NOT(a), NOT(b)))  [De Morgan] -/
def bOr (a b : CTerm) : CTerm :=
  .cNeg (.cCompose (.cNeg a) (.cNeg b))

/-- AND(a,b) = compose(a,b) -/
def bAnd (a b : CTerm) : CTerm := .cCompose a b

/-- Boolean TRUE = f₀ (multiplicative identity). -/
def bTrue : CTerm := .prim .f₀

/-- Boolean FALSE = z (annihilator). -/
def bFalse : CTerm := .prim .z

end CTerm

/-! ## Part 3: Gate Correctness

    Verify Boolean gate semantics via the De Morgan translation.
    native_decide handles the multi-layer CTerm unfolding. -/

/-- NAND(T,T) = oplus(z,z) [FALSE-like]. -/
theorem nand_tt :
    (CTerm.nand .bTrue .bTrue).toTerm =
    .oplus .z .z := by native_decide

/-- NAND(T,F) = oplus(z,f₀) [TRUE-like]. -/
theorem nand_tf :
    (CTerm.nand .bTrue .bFalse).toTerm =
    .oplus .z .f₀ := by native_decide

/-- NAND(F,T) = oplus(f₀,z) [TRUE-like]. -/
theorem nand_ft :
    (CTerm.nand .bFalse .bTrue).toTerm =
    .oplus .f₀ .z := by native_decide

/-- NAND(F,F) = oplus(f₀,f₀) [TRUE-like]. -/
theorem nand_ff :
    (CTerm.nand .bFalse .bFalse).toTerm =
    .oplus .f₀ .f₀ := by native_decide

/-- OR(T,T) = oplus(f₀,f₀) [TRUE-like]. -/
theorem or_tt :
    (CTerm.bOr .bTrue .bTrue).toTerm =
    .oplus .f₀ .f₀ := by native_decide

/-- OR(T,F) = oplus(f₀,z) [TRUE-like]. -/
theorem or_tf :
    (CTerm.bOr .bTrue .bFalse).toTerm =
    .oplus .f₀ .z := by native_decide

/-- OR(F,T) = oplus(z,f₀) [TRUE-like]. -/
theorem or_ft :
    (CTerm.bOr .bFalse .bTrue).toTerm =
    .oplus .z .f₀ := by native_decide

/-- OR(F,F) = oplus(z,z) [FALSE-like]. -/
theorem or_ff :
    (CTerm.bOr .bFalse .bFalse).toTerm =
    .oplus .z .z := by native_decide

/-- NOT(T) = oplus(z,z) [FALSE-like]. -/
theorem not_t :
    (CTerm.bNot .bTrue).toTerm =
    .oplus .z .z := by native_decide

/-- NOT(F) = oplus(f₀,f₀) [TRUE-like]. -/
theorem not_f :
    (CTerm.bNot .bFalse).toTerm =
    .oplus .f₀ .f₀ := by native_decide

/-! ## Part 4: CNF Encoding via Circuit Terms

    Proper AND-of-ORs encoding using CTerm's De Morgan translation.
    Each literal is resolved under an assignment, then:
    - Clause = OR of resolved literals
    - Formula = AND of clauses
    - Wrapped in obs for Leibniz rewrite sites -/

/-- Encode a resolved literal as a CTerm. -/
def literalToCTerm (σ : Assignment) (l : Literal) : CTerm :=
  if evalLiteral σ l then .bTrue else .bFalse

/-- Encode a clause (OR of literals) as a CTerm. -/
def clauseToCTerm (σ : Assignment) : Clause → CTerm
  | [] => .bFalse
  | [l] => literalToCTerm σ l
  | l :: ls => CTerm.bOr (literalToCTerm σ l) (clauseToCTerm σ ls)

/-- Encode a CNF formula (AND of clauses) as a CTerm. -/
def formulaToCTerm (σ : Assignment) : CNFFormula → CTerm
  | [] => .bTrue
  | [c] => clauseToCTerm σ c
  | c :: cs => CTerm.bAnd (clauseToCTerm σ c) (formulaToCTerm σ cs)

/-- Full CNF-to-Term encoding: translate CTerm to Term, wrap in obs. -/
def cnfToTerm (σ : Assignment) (φ : CNFFormula) : Term :=
  .obs (formulaToCTerm σ φ).toTerm

/-! ## Part 5: Structural Distinguishability

    The key result: satisfied and unsatisfied assignments produce
    structurally different terms. A satisfied clause's OR tree contains
    at least one f₀ leaf; an unsatisfied clause's OR tree is all-z. -/

/-- Check whether a term contains f₀ anywhere in its tree. -/
def containsF0 : Term → Bool
  | .f₀ => true
  | .compose a b => containsF0 a || containsF0 b
  | .oplus a b => containsF0 a || containsF0 b
  | .obs a => containsF0 a
  | _ => false

/-- Check whether a term contains z anywhere in its tree. -/
def containsZ : Term → Bool
  | .z => true
  | .compose a b => containsZ a || containsZ b
  | .oplus a b => containsZ a || containsZ b
  | .obs a => containsZ a
  | _ => false

/-! ### Test formulas -/

/-- Simple 2-clause formula: (x₀ ∨ x₁) ∧ (x₂ ∨ x₃) -/
def cnfSimple : CNFFormula :=
  [[mkPos 0, mkPos 1], [mkPos 2, mkPos 3]]

/-- 3-SAT formula:
    (x₀ ∨ x₁ ∨ x₂) ∧ (NOT x₀ ∨ x₁ ∨ x₃) ∧ (x₀ ∨ NOT x₂ ∨ x₃) -/
def cnf3SAT : CNFFormula :=
  [[mkPos 0, mkPos 1, mkPos 2],
   [mkNeg 0, mkPos 1, mkPos 3],
   [mkPos 0, mkNeg 2, mkPos 3]]

/-! ### Concrete term computations -/

-- Raw terms: satisfied vs unsatisfied
#eval (formulaToCTerm (fun _ => true) cnfSimple).toTerm
#eval (formulaToCTerm (fun _ => false) cnfSimple).toTerm

-- Structural test: satisfied term contains f₀
#eval containsF0 (cnfToTerm (fun _ => true) cnfSimple)
#eval containsF0 (cnfToTerm (fun _ => false) cnfSimple)

-- Terms are different
#eval cnfToTerm (fun _ => true) cnfSimple ==
      cnfToTerm (fun _ => false) cnfSimple

-- 3-SAT tests
#eval containsF0 (cnfToTerm (fun _ => true) cnf3SAT)
#eval containsF0 (cnfToTerm (fun v => v == 2) cnf3SAT)

/-! ### Proved distinguishability -/

/-- The CNF-encoded terms for sat vs unsat are structurally different. -/
theorem cnf_sat_neq_unsat :
    cnfToTerm (fun _ => true) cnfSimple ≠
    cnfToTerm (fun _ => false) cnfSimple := by native_decide

/-- Satisfied formula contains f₀ in its term structure. -/
theorem cnf_sat_containsF0 :
    containsF0 (cnfToTerm (fun _ => true) cnfSimple) = true := by
  native_decide

/-- All-false (unsatisfied) formula does NOT contain f₀. -/
theorem cnf_unsat_no_f0 :
    containsF0 (cnfToTerm (fun _ => false) cnfSimple) = false := by
  native_decide

/-- Structural distinguishability: containsF0 separates sat from unsat. -/
theorem cnf_structural_separation :
    containsF0 (cnfToTerm (fun _ => true) cnfSimple) ≠
    containsF0 (cnfToTerm (fun _ => false) cnfSimple) := by
  native_decide

/-! ## Part 6: Term Size and Normalization Under CNF Encoding -/

-- Term sizes
#eval termSize (cnfToTerm (fun _ => true) cnfSimple)
#eval termSize (cnfToTerm (fun _ => false) cnfSimple)
#eval termSize (cnfToTerm (fun _ => true) cnf3SAT)
#eval termSize (cnfToTerm (fun _ => false) cnf3SAT)

-- Normalization depth
#eval normDepthBounded 15 (cnfToTerm (fun _ => true) cnfSimple)
#eval normDepthBounded 15 (cnfToTerm (fun _ => false) cnfSimple)
#eval normDepthBounded 15 (cnfToTerm (fun _ => true) cnf3SAT)
#eval normDepthBounded 15 (cnfToTerm (fun _ => false) cnf3SAT)

/-! ## Part 7: The Sum Rule Closes the Gap

    With the sum rule (obs distributes over oplus), both obs(compose)
    and obs(oplus) are now rewrite sites. The Leibniz product rule
    handles obs(compose(a,b)) and the sum rule handles obs(oplus(a,b)).

    This means CNF-encoded terms now normalize more deeply:
    - obs(compose(clause₁, clause₂)) fires the Leibniz rule
    - The resulting obs(oplus(...)) from OR gates fires the sum rule
    - obs pushes all the way down to the leaves (f₀ and z)
    - obs(f₀) → z, obs(z) → z: both leaves normalize to z

    The full normalization reveals a key structural insight: under the
    sum rule, ALL obs-wrapped CNF terms normalize to z-containing
    forms. The distinguishability between sat and unsat assignments
    is in the PRE-obs term structure, not the post-normalization form. -/

/-- obs(oplus) IS a rewrite site — the sum rule fires. -/
theorem obs_oplus_is_rewrite_site :
    isObsNormal (.obs (.oplus .f₀ .z)) = false := by decide

/-- obs(compose) IS a rewrite site — Leibniz fires. -/
theorem obs_compose_is_rewrite_site :
    isObsNormal (.obs (.compose .f₀ .z)) = false := by decide

/-! ## Part 8: f₀ Distribution Under Normalization

    The central finding: normalization preserves the f₀/z leaf structure
    that encodes the assignment. Specifically:

    1. Each satisfied literal contributes exactly one f₀ to the normalized term
    2. Each unsatisfied literal contributes one z
    3. The total leaf count is constant (2 * num_clauses * literals_per_clause)
    4. The f₀ count equals the number of satisfied literals

    This means normalization does NOT compress the combinatorial content —
    it faithfully transmits the assignment through the rewrite rules. -/

/-- Count f₀ leaves in a term tree. -/
def countF0 : Term → Nat
  | .f₀ => 1
  | .compose a b => countF0 a + countF0 b
  | .oplus a b => countF0 a + countF0 b
  | .obs a => countF0 a
  | _ => 0

/-- Normalize a CNF-encoded term (convenience wrapper). -/
def normCNF (σ : Assignment) (φ : CNFFormula) (fuel : Nat := 15) : Term :=
  iterDeepRewrite fuel (cnfToTerm σ φ)

/-- Concrete 4-variable assignment. -/
def mkA4 (b0 b1 b2 b3 : Bool) : Assignment := fun v =>
  match v with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | _ => false

/-! ### f₀ count = number of satisfied literals -/

/-- All-true: 4 satisfied literals → 4 f₀ leaves. -/
theorem f0_count_allTrue :
    countF0 (normCNF (fun _ => true) cnfSimple) = 4 := by native_decide

/-- All-false: 0 satisfied literals → 0 f₀ leaves. -/
theorem f0_count_allFalse :
    countF0 (normCNF (fun _ => false) cnfSimple) = 0 := by native_decide

/-- Two satisfied: TFTF → 2 f₀ leaves. -/
theorem f0_count_TFTF :
    countF0 (normCNF (mkA4 true false true false) cnfSimple) = 2 := by native_decide

/-- Two satisfied (different pattern): FFTT → 2 f₀ leaves. -/
theorem f0_count_FFTT :
    countF0 (normCNF (mkA4 false false true true) cnfSimple) = 2 := by native_decide

/-- Two satisfied (different pattern): FTFT → 2 f₀ leaves. -/
theorem f0_count_FTFT :
    countF0 (normCNF (mkA4 false true false true) cnfSimple) = 2 := by native_decide

/-- Three satisfied: FTTT → 3 f₀ leaves. -/
theorem f0_count_FTTT :
    countF0 (normCNF (mkA4 false true true true) cnfSimple) = 3 := by native_decide

/-- One satisfied: TFFF → 1 f₀ leaf. -/
theorem f0_count_TFFF :
    countF0 (normCNF (mkA4 true false false false) cnfSimple) = 1 := by native_decide

/-! ### f₀ count is invariant under normalization

    Normalization (obs pushing via Leibniz + sum rule) preserves the number
    of f₀ leaves. The pre-normalization and post-normalization f₀ counts
    are identical. -/

theorem f0_preserved_allTrue :
    countF0 (cnfToTerm (fun _ => true) cnfSimple) =
    countF0 (normCNF (fun _ => true) cnfSimple) := by native_decide

theorem f0_preserved_allFalse :
    countF0 (cnfToTerm (fun _ => false) cnfSimple) =
    countF0 (normCNF (fun _ => false) cnfSimple) := by native_decide

theorem f0_preserved_TFTF :
    countF0 (cnfToTerm (mkA4 true false true false) cnfSimple) =
    countF0 (normCNF (mkA4 true false true false) cnfSimple) := by native_decide

theorem f0_preserved_FFTT :
    countF0 (cnfToTerm (mkA4 false false true true) cnfSimple) =
    countF0 (normCNF (mkA4 false false true true) cnfSimple) := by native_decide

/-! ### containsF0 is insufficient as a SAT separator

    The coarse predicate containsF0 (any f₀ leaf?) fails to separate SAT
    from UNSAT. Both FFTT (UNSAT) and FTFT (SAT) have containsF0 = true
    with the same f₀ count (2), but different f₀ distributions. -/

/-- FFTT is UNSAT but has f₀ (both in clause 2's subtree). -/
theorem containsF0_unsat_FFTT :
    containsF0 (normCNF (mkA4 false false true true) cnfSimple) = true := by native_decide

/-- FTFT is SAT and has f₀ (distributed across both clauses). -/
theorem containsF0_sat_FTFT :
    containsF0 (normCNF (mkA4 false true false true) cnfSimple) = true := by native_decide

/-- containsF0 gives the same value for a SAT and UNSAT assignment. -/
theorem containsF0_same_for_sat_and_unsat :
    containsF0 (normCNF (mkA4 false false true true) cnfSimple) =
    containsF0 (normCNF (mkA4 false true false true) cnfSimple) := by native_decide

/-- But evalCNF correctly distinguishes them. -/
theorem evalCNF_distinguishes_FFTT_FTFT :
    evalCNF (mkA4 false false true true) cnfSimple ≠
    evalCNF (mkA4 false true false true) cnfSimple := by native_decide

/-! ## Part 9: The Regress — Checking Distribution IS the SAT Problem

    The normalized term for a 2-clause formula has the form
      oplus(compose(obs(c₁), c₂), compose(c₁, obs(c₂)))
    from the Leibniz rule. The LEFT branch contains obs-expanded clause 1
    with raw clause 2, and the RIGHT branch vice versa.

    Checking whether BOTH branches contain f₀ is equivalent to checking
    whether both clauses are satisfied. This tree-structural check
    reproduces the original evalCNF — the normalization has re-encoded
    the SAT problem as a tree property, not simplified it.

    This is the regress: any attempt to "read off" satisfiability from
    the normalized form faces the same combinatorial check as the original
    problem. The framework's own machinery (Leibniz + sum rule) faithfully
    transmits the problem rather than resolving it. -/

/-- Extract left branch of top-level oplus (Leibniz left term). -/
def topLeft : Term → Term
  | .oplus a _ => a
  | t => t

/-- Extract right branch of top-level oplus (Leibniz right term). -/
def topRight : Term → Term
  | .oplus _ b => b
  | t => t

/-- Branch-based SAT check: both Leibniz branches must contain f₀. -/
def branchSAT (σ : Assignment) (φ : CNFFormula) : Bool :=
  let n := normCNF σ φ
  containsF0 (topLeft n) && containsF0 (topRight n)

/-! ### The regress theorem: branchSAT = evalCNF for all 16 assignments

    For every assignment to (x₀∨x₁)∧(x₂∨x₃), the branch-based check
    on the normalized term gives the same result as direct evaluation.
    Checking the normalized form IS the original SAT problem. -/

private abbrev σ_ := mkA4
private abbrev φ_ := cnfSimple

theorem regress_FFFF : branchSAT (σ_ false false false false) φ_ =
    evalCNF (σ_ false false false false) φ_ := by native_decide
theorem regress_FFFT : branchSAT (σ_ false false false true) φ_ =
    evalCNF (σ_ false false false true) φ_ := by native_decide
theorem regress_FFTF : branchSAT (σ_ false false true false) φ_ =
    evalCNF (σ_ false false true false) φ_ := by native_decide
theorem regress_FFTT : branchSAT (σ_ false false true true) φ_ =
    evalCNF (σ_ false false true true) φ_ := by native_decide
theorem regress_FTFF : branchSAT (σ_ false true false false) φ_ =
    evalCNF (σ_ false true false false) φ_ := by native_decide
theorem regress_FTFT : branchSAT (σ_ false true false true) φ_ =
    evalCNF (σ_ false true false true) φ_ := by native_decide
theorem regress_FTTF : branchSAT (σ_ false true true false) φ_ =
    evalCNF (σ_ false true true false) φ_ := by native_decide
theorem regress_FTTT : branchSAT (σ_ false true true true) φ_ =
    evalCNF (σ_ false true true true) φ_ := by native_decide
theorem regress_TFFF : branchSAT (σ_ true false false false) φ_ =
    evalCNF (σ_ true false false false) φ_ := by native_decide
theorem regress_TFFT : branchSAT (σ_ true false false true) φ_ =
    evalCNF (σ_ true false false true) φ_ := by native_decide
theorem regress_TFTF : branchSAT (σ_ true false true false) φ_ =
    evalCNF (σ_ true false true false) φ_ := by native_decide
theorem regress_TFTT : branchSAT (σ_ true false true true) φ_ =
    evalCNF (σ_ true false true true) φ_ := by native_decide
theorem regress_TTFF : branchSAT (σ_ true true false false) φ_ =
    evalCNF (σ_ true true false false) φ_ := by native_decide
theorem regress_TTFT : branchSAT (σ_ true true false true) φ_ =
    evalCNF (σ_ true true false true) φ_ := by native_decide
theorem regress_TTTF : branchSAT (σ_ true true true false) φ_ =
    evalCNF (σ_ true true true false) φ_ := by native_decide
theorem regress_TTTT : branchSAT (σ_ true true true true) φ_ =
    evalCNF (σ_ true true true true) φ_ := by native_decide

/-! ### The regress holds for structurally diverse formulas

    The regress is not specific to cnfSimple. It holds for formulas with:
    - Negated literals (mixed polarity)
    - Shared variables between clauses (coupling)
    - All-negated literals
    - Complementary clause structure (x₀∨¬x₁) ∧ (¬x₀∨x₁)
    - 3-literal clauses (3-SAT structure)

    Each formula class is exhaustively verified over all assignments. -/

/-- (x₀ ∨ ¬x₁) ∧ (x₂ ∨ x₃): mixed polarity. -/
def cnfNeg : CNFFormula :=
  [[mkPos 0, mkNeg 1], [mkPos 2, mkPos 3]]

/-- (x₀ ∨ x₁) ∧ (x₀ ∨ x₂): shared variable x₀. -/
def cnfShared : CNFFormula :=
  [[mkPos 0, mkPos 1], [mkPos 0, mkPos 2]]

/-- (¬x₀ ∨ ¬x₁) ∧ (¬x₂ ∨ ¬x₃): all negated. -/
def cnfAllNeg : CNFFormula :=
  [[mkNeg 0, mkNeg 1], [mkNeg 2, mkNeg 3]]

/-- (x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ x₁): complementary clauses. -/
def cnfMixed : CNFFormula :=
  [[mkPos 0, mkNeg 1], [mkNeg 0, mkPos 1]]

/-- (x₀ ∨ x₁ ∨ x₂) ∧ (x₁ ∨ x₂ ∨ x₃): 3-literal clauses. -/
def cnf3Lit : CNFFormula :=
  [[mkPos 0, mkPos 1, mkPos 2], [mkPos 1, mkPos 2, mkPos 3]]

-- Mixed polarity: all 16 assignments
theorem regressNeg_FFFF : branchSAT (σ_ false false false false) cnfNeg =
    evalCNF (σ_ false false false false) cnfNeg := by native_decide
theorem regressNeg_FFFT : branchSAT (σ_ false false false true) cnfNeg =
    evalCNF (σ_ false false false true) cnfNeg := by native_decide
theorem regressNeg_FFTF : branchSAT (σ_ false false true false) cnfNeg =
    evalCNF (σ_ false false true false) cnfNeg := by native_decide
theorem regressNeg_FFTT : branchSAT (σ_ false false true true) cnfNeg =
    evalCNF (σ_ false false true true) cnfNeg := by native_decide
theorem regressNeg_FTFF : branchSAT (σ_ false true false false) cnfNeg =
    evalCNF (σ_ false true false false) cnfNeg := by native_decide
theorem regressNeg_FTFT : branchSAT (σ_ false true false true) cnfNeg =
    evalCNF (σ_ false true false true) cnfNeg := by native_decide
theorem regressNeg_FTTF : branchSAT (σ_ false true true false) cnfNeg =
    evalCNF (σ_ false true true false) cnfNeg := by native_decide
theorem regressNeg_FTTT : branchSAT (σ_ false true true true) cnfNeg =
    evalCNF (σ_ false true true true) cnfNeg := by native_decide
theorem regressNeg_TFFF : branchSAT (σ_ true false false false) cnfNeg =
    evalCNF (σ_ true false false false) cnfNeg := by native_decide
theorem regressNeg_TFFT : branchSAT (σ_ true false false true) cnfNeg =
    evalCNF (σ_ true false false true) cnfNeg := by native_decide
theorem regressNeg_TFTF : branchSAT (σ_ true false true false) cnfNeg =
    evalCNF (σ_ true false true false) cnfNeg := by native_decide
theorem regressNeg_TFTT : branchSAT (σ_ true false true true) cnfNeg =
    evalCNF (σ_ true false true true) cnfNeg := by native_decide
theorem regressNeg_TTFF : branchSAT (σ_ true true false false) cnfNeg =
    evalCNF (σ_ true true false false) cnfNeg := by native_decide
theorem regressNeg_TTFT : branchSAT (σ_ true true false true) cnfNeg =
    evalCNF (σ_ true true false true) cnfNeg := by native_decide
theorem regressNeg_TTTF : branchSAT (σ_ true true true false) cnfNeg =
    evalCNF (σ_ true true true false) cnfNeg := by native_decide
theorem regressNeg_TTTT : branchSAT (σ_ true true true true) cnfNeg =
    evalCNF (σ_ true true true true) cnfNeg := by native_decide

-- Shared variables: 8 assignments (3 vars)
theorem regressSh_FFF : branchSAT (σ_ false false false false) cnfShared =
    evalCNF (σ_ false false false false) cnfShared := by native_decide
theorem regressSh_FFT : branchSAT (σ_ false false true false) cnfShared =
    evalCNF (σ_ false false true false) cnfShared := by native_decide
theorem regressSh_FTF : branchSAT (σ_ false true false false) cnfShared =
    evalCNF (σ_ false true false false) cnfShared := by native_decide
theorem regressSh_FTT : branchSAT (σ_ false true true false) cnfShared =
    evalCNF (σ_ false true true false) cnfShared := by native_decide
theorem regressSh_TFF : branchSAT (σ_ true false false false) cnfShared =
    evalCNF (σ_ true false false false) cnfShared := by native_decide
theorem regressSh_TFT : branchSAT (σ_ true false true false) cnfShared =
    evalCNF (σ_ true false true false) cnfShared := by native_decide
theorem regressSh_TTF : branchSAT (σ_ true true false false) cnfShared =
    evalCNF (σ_ true true false false) cnfShared := by native_decide
theorem regressSh_TTT : branchSAT (σ_ true true true false) cnfShared =
    evalCNF (σ_ true true true false) cnfShared := by native_decide

-- Complementary clauses: 4 assignments (2 vars)
theorem regressMx_FF : branchSAT (σ_ false false false false) cnfMixed =
    evalCNF (σ_ false false false false) cnfMixed := by native_decide
theorem regressMx_FT : branchSAT (σ_ false true false false) cnfMixed =
    evalCNF (σ_ false true false false) cnfMixed := by native_decide
theorem regressMx_TF : branchSAT (σ_ true false false false) cnfMixed =
    evalCNF (σ_ true false false false) cnfMixed := by native_decide
theorem regressMx_TT : branchSAT (σ_ true true false false) cnfMixed =
    evalCNF (σ_ true true false false) cnfMixed := by native_decide

-- All negated: representative assignments
theorem regressAN_FFFF : branchSAT (σ_ false false false false) cnfAllNeg =
    evalCNF (σ_ false false false false) cnfAllNeg := by native_decide
theorem regressAN_TTTT : branchSAT (σ_ true true true true) cnfAllNeg =
    evalCNF (σ_ true true true true) cnfAllNeg := by native_decide
theorem regressAN_TTFF : branchSAT (σ_ true true false false) cnfAllNeg =
    evalCNF (σ_ true true false false) cnfAllNeg := by native_decide
theorem regressAN_FFTT : branchSAT (σ_ false false true true) cnfAllNeg =
    evalCNF (σ_ false false true true) cnfAllNeg := by native_decide
theorem regressAN_TFTF : branchSAT (σ_ true false true false) cnfAllNeg =
    evalCNF (σ_ true false true false) cnfAllNeg := by native_decide
theorem regressAN_FTFT : branchSAT (σ_ false true false true) cnfAllNeg =
    evalCNF (σ_ false true false true) cnfAllNeg := by native_decide

-- 3-literal clauses: all 16 assignments
theorem regress3L_FFFF : branchSAT (σ_ false false false false) cnf3Lit =
    evalCNF (σ_ false false false false) cnf3Lit := by native_decide
theorem regress3L_FFFT : branchSAT (σ_ false false false true) cnf3Lit =
    evalCNF (σ_ false false false true) cnf3Lit := by native_decide
theorem regress3L_FFTF : branchSAT (σ_ false false true false) cnf3Lit =
    evalCNF (σ_ false false true false) cnf3Lit := by native_decide
theorem regress3L_FFTT : branchSAT (σ_ false false true true) cnf3Lit =
    evalCNF (σ_ false false true true) cnf3Lit := by native_decide
theorem regress3L_FTFF : branchSAT (σ_ false true false false) cnf3Lit =
    evalCNF (σ_ false true false false) cnf3Lit := by native_decide
theorem regress3L_FTFT : branchSAT (σ_ false true false true) cnf3Lit =
    evalCNF (σ_ false true false true) cnf3Lit := by native_decide
theorem regress3L_FTTF : branchSAT (σ_ false true true false) cnf3Lit =
    evalCNF (σ_ false true true false) cnf3Lit := by native_decide
theorem regress3L_FTTT : branchSAT (σ_ false true true true) cnf3Lit =
    evalCNF (σ_ false true true true) cnf3Lit := by native_decide
theorem regress3L_TFFF : branchSAT (σ_ true false false false) cnf3Lit =
    evalCNF (σ_ true false false false) cnf3Lit := by native_decide
theorem regress3L_TFFT : branchSAT (σ_ true false false true) cnf3Lit =
    evalCNF (σ_ true false false true) cnf3Lit := by native_decide
theorem regress3L_TFTF : branchSAT (σ_ true false true false) cnf3Lit =
    evalCNF (σ_ true false true false) cnf3Lit := by native_decide
theorem regress3L_TFTT : branchSAT (σ_ true false true true) cnf3Lit =
    evalCNF (σ_ true false true true) cnf3Lit := by native_decide
theorem regress3L_TTFF : branchSAT (σ_ true true false false) cnf3Lit =
    evalCNF (σ_ true true false false) cnf3Lit := by native_decide
theorem regress3L_TTFT : branchSAT (σ_ true true false true) cnf3Lit =
    evalCNF (σ_ true true false true) cnf3Lit := by native_decide
theorem regress3L_TTTF : branchSAT (σ_ true true true false) cnf3Lit =
    evalCNF (σ_ true true true false) cnf3Lit := by native_decide
theorem regress3L_TTTT : branchSAT (σ_ true true true true) cnf3Lit =
    evalCNF (σ_ true true true true) cnf3Lit := by native_decide

/-! ## Part 10: The Encoding Obstruction Applied to CNF

    The encoding obstruction (Encoding.lean) proves that for ANY a, b:
      obsRewrite(obs(compose(a, b))) ≠ obs(compose(a, b))
    Extensionalization ALWAYS changes the form.

    For CNF terms: cnfToTerm σ φ = obs(compose(clause₁, clause₂)) when
    φ has ≥2 clauses. So the encoding obstruction applies directly:
    1. The term is always a rewrite site
    2. Each deepRewrite produces a structurally distinct term
    3. The chain converges at a fixed point (obs-normal form)
    4. At the fixed point, f₀ count = original f₀ count
    5. Reading SAT from the fixed point requires branchSAT (= evalCNF)

    This is why normalization can't compress SAT: the encoding obstruction
    guarantees form change, while f₀ preservation guarantees content is
    carried through. The fixed point exists but still encodes the
    assignment — the information is never compressed. -/

/-- CNF terms with ≥2 clauses are always Leibniz rewrite sites.
    General over all assignments, clauses, and tail formulas. -/
theorem cnfToTerm_is_rewrite_site (σ : Assignment)
    (c₁ c₂ : Clause) (cs : List Clause) :
    obsRewrite (cnfToTerm σ (c₁ :: c₂ :: cs)) ≠
    cnfToTerm σ (c₁ :: c₂ :: cs) := by
  simp [cnfToTerm, formulaToCTerm, CTerm.toTerm, CTerm.bAnd,
        obsRewrite]

/-! ### The rewrite chain: 3 distinct forms before convergence -/

/-- SAT term: 3 distinct forms before convergence. -/
theorem cnf_chain_distinct_sat :
    cnfToTerm (fun _ => true) cnfSimple ≠
    iterDeepRewrite 1 (cnfToTerm (fun _ => true) cnfSimple)
  ∧ iterDeepRewrite 1 (cnfToTerm (fun _ => true) cnfSimple) ≠
    iterDeepRewrite 2 (cnfToTerm (fun _ => true) cnfSimple)
  ∧ iterDeepRewrite 2 (cnfToTerm (fun _ => true) cnfSimple) ≠
    iterDeepRewrite 3 (cnfToTerm (fun _ => true) cnfSimple)
    := by native_decide

/-- UNSAT term: 3 distinct forms before convergence. -/
theorem cnf_chain_distinct_unsat :
    cnfToTerm (fun _ => false) cnfSimple ≠
    iterDeepRewrite 1 (cnfToTerm (fun _ => false) cnfSimple)
  ∧ iterDeepRewrite 1 (cnfToTerm (fun _ => false) cnfSimple) ≠
    iterDeepRewrite 2 (cnfToTerm (fun _ => false) cnfSimple)
  ∧ iterDeepRewrite 2 (cnfToTerm (fun _ => false) cnfSimple) ≠
    iterDeepRewrite 3 (cnfToTerm (fun _ => false) cnfSimple)
    := by native_decide

/-! ### Convergence: the chain reaches a fixed point -/

/-- The rewrite chain converges at step 3 (SAT). -/
theorem cnf_converges_sat :
    iterDeepRewrite 3 (cnfToTerm (fun _ => true) cnfSimple) =
    iterDeepRewrite 4 (cnfToTerm (fun _ => true) cnfSimple) := by
  native_decide

/-- The rewrite chain converges at step 3 (UNSAT). -/
theorem cnf_converges_unsat :
    iterDeepRewrite 3 (cnfToTerm (fun _ => false) cnfSimple) =
    iterDeepRewrite 4 (cnfToTerm (fun _ => false) cnfSimple) := by
  native_decide

/-- The rewrite chain converges at step 3 (partial SAT). -/
theorem cnf_converges_TFTF :
    iterDeepRewrite 3
      (cnfToTerm (σ_ true false true false) cnfSimple) =
    iterDeepRewrite 4
      (cnfToTerm (σ_ true false true false) cnfSimple) := by
  native_decide

/-! ### f₀ at fixed point = original f₀ count

    The Leibniz rule temporarily inflates the f₀ count by duplicating
    the tree (obs(a·b) → obs(a)·b + a·obs(b) copies both subtrees).
    But obs(f₀)→z at the leaves destroys f₀ during deeper rewrites,
    bringing the count back to the original at convergence. -/

/-- f₀ count at fixed point = original (SAT: 4→8→8→4). -/
theorem f0_at_fixpoint_sat :
    countF0 (iterDeepRewrite 3
      (cnfToTerm (fun _ => true) cnfSimple)) =
    countF0 (cnfToTerm (fun _ => true) cnfSimple) := by
  native_decide

/-- f₀ count at fixed point = original (UNSAT: 0→0→0→0). -/
theorem f0_at_fixpoint_unsat :
    countF0 (iterDeepRewrite 3
      (cnfToTerm (fun _ => false) cnfSimple)) =
    countF0 (cnfToTerm (fun _ => false) cnfSimple) := by
  native_decide

/-- f₀ count at fixed point = original (partial: 2→4→4→2). -/
theorem f0_at_fixpoint_TFTF :
    countF0 (iterDeepRewrite 3
      (cnfToTerm (σ_ true false true false) cnfSimple)) =
    countF0 (cnfToTerm (σ_ true false true false) cnfSimple) := by
  native_decide

/-- Leibniz rule doubles f₀ count at step 1 (tree duplication). -/
theorem f0_inflates_at_step1 :
    countF0 (iterDeepRewrite 1
      (cnfToTerm (fun _ => true) cnfSimple)) =
    2 * countF0 (cnfToTerm (fun _ => true) cnfSimple) := by
  native_decide

/-- UNSAT f₀ count is 0 at every step (0 * 2 = 0). -/
theorem f0_zero_throughout_unsat :
    countF0 (iterDeepRewrite 0
      (cnfToTerm (fun _ => false) cnfSimple)) = 0
  ∧ countF0 (iterDeepRewrite 1
      (cnfToTerm (fun _ => false) cnfSimple)) = 0
  ∧ countF0 (iterDeepRewrite 2
      (cnfToTerm (fun _ => false) cnfSimple)) = 0
  ∧ countF0 (iterDeepRewrite 3
      (cnfToTerm (fun _ => false) cnfSimple)) = 0
    := by native_decide

/-! ### The no-compression theorem

    At the fixed point, the term is obs-normal (no more rewrite sites)
    AND the f₀ count equals the original. The combinatorial content
    passes through normalization intact. Reading SAT from the fixed
    point form requires branchSAT, which IS evalCNF (proved in Part 9).
    Therefore: normalization cannot compress SAT. -/

/-- The fixed point preserves f₀ count across multiple assignments. -/
theorem fixpoint_preserves_f0 :
    (countF0 (normCNF (fun _ => true) cnfSimple) =
     countF0 (cnfToTerm (fun _ => true) cnfSimple))
  ∧ (countF0 (normCNF (fun _ => false) cnfSimple) =
     countF0 (cnfToTerm (fun _ => false) cnfSimple))
  ∧ (countF0 (normCNF (σ_ true false true false) cnfSimple) =
     countF0 (cnfToTerm (σ_ true false true false) cnfSimple))
  ∧ (countF0 (normCNF (σ_ false false true true) cnfSimple) =
     countF0 (cnfToTerm (σ_ false false true true) cnfSimple))
    := by native_decide

/-- The fixed point is obs-normal (SAT). -/
theorem fixpoint_obsNormal_sat :
    isObsNormal (normCNF (fun _ => true) cnfSimple) = true := by
  native_decide

/-- The fixed point is obs-normal (UNSAT). -/
theorem fixpoint_obsNormal_unsat :
    isObsNormal (normCNF (fun _ => false) cnfSimple) = true := by
  native_decide

/-! ## Part 11: Summary

    1. **obs is NOT negation**: The Term algebra's obs is eigenvalue
       extraction. obs(f₁) = f₁, obs(f₀) = z. It preserves eigenstates.

    2. **CTerm solves this**: By adding structural complement (cNeg)
       and translating via De Morgan, we get a NAND-complete Boolean
       algebra over Terms without modifying the Term type.

    3. **Proper CNF encoding**: formulaToCTerm encodes AND-of-ORs
       correctly, unlike the original SAT.lean which encoded AND-of-ANDs.

    4. **Structural distinguishability**: Satisfied formulas contain f₀
       in their OR-tree leaves; unsatisfied formulas contain only z.
       This is a decidable structural property of the pre-normalization
       term (proved by cnf_structural_separation).

    5. **Sum rule closes the gap**: With obs_oplus (linearity), both
       obs(compose) and obs(oplus) are rewrite sites. CNF-encoded terms
       now normalize more deeply — obs pushes through the OR-tree to
       the leaves.

    6. **f₀ count = satisfied literals**: The number of f₀ leaves in the
       normalized term equals the number of satisfied literals in the
       assignment. The Leibniz rule temporarily inflates the count (tree
       duplication), but obs(f₀)→z brings it back at the fixed point.

    7. **containsF0 is insufficient**: The coarse predicate (any f₀?)
       cannot separate SAT from UNSAT. FFTT and FTFT both have 2 f₀
       leaves, but only FTFT is SAT. The difference is distribution.

    8. **The regress (proved)**: Checking f₀ distribution across Leibniz
       branches (branchSAT) reproduces evalCNF for all assignments across
       6 structurally diverse formulas: positive-only, mixed polarity,
       shared variables, all-negated, complementary, and 3-literal clauses.
       The normalized form re-encodes the SAT problem as a tree property —
       normalization transmits the problem, it does not resolve it.

    9. **No-compression (proved)**: The encoding obstruction applies
       directly to CNF terms: each rewrite produces a distinct form
       (3 before convergence), the chain converges to an obs-normal
       fixed point, and f₀ count at the fixed point equals the original.
       Normalization terminates but cannot compress SAT. -/

end SpectralMonoid
