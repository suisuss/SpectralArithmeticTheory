/-
  Depth Profile for 4-Variable Formula (Rank-Dimension Conjecture Test)
  =====================================================================

  The rank-dimension conjecture: for a CNF formula with incidence matrix M,
  the minimum separating dimension d_min of the DynSemiring depth profile
  equals rank(M).

  For phi (3-clause, 3-var): rank(M) = 2, d_min = 2 (verified in DepthProfile.lean).
  For phi4chain (4-clause, 4-var): rank(M) = 3, so we predict d_min = 3.

  phi4chain: (x₀ ∨ x₁) ∧ (¬x₁ ∨ x₂) ∧ (¬x₂ ∨ x₃) ∧ (¬x₃ ∨ ¬x₀)
  SAT assignments: 0111 and 1000 (verified in VectorEmbed.lean).
-/

import SpectralArithmetic.Lambda.Embedding
import SpectralArithmetic.Obstruction.DepthProfile

set_option linter.style.nativeDecide false

namespace SpectralMonoid
namespace DepthProfile4

open Combinator
open CombTerm
open DepthProfile

/-! ## Encode phi4chain as SK combinators

  (x₀ ∨ x₁) ∧ (¬x₁ ∨ x₂) ∧ (¬x₂ ∨ x₃) ∧ (¬x₃ ∨ ¬x₀) -/

/-- 4-clause chain formula with shared variables:
    (x₀ ∨ x₁) ∧ (¬x₁ ∨ x₂) ∧ (¬x₂ ∨ x₃) ∧ (¬x₃ ∨ ¬x₀) -/
def cnf4chain (b0 b1 b2 b3 : Bool) : CombTerm :=
  cAnd (cAnd (cOr (mkBool b0) (mkBool b1))
             (cOr (cNot (mkBool b1)) (mkBool b2)))
       (cAnd (cOr (cNot (mkBool b2)) (mkBool b3))
             (cOr (cNot (mkBool b3)) (cNot (mkBool b0))))

/-! ## Verify correctness: only 0111 and 1000 are SAT -/

-- SAT assignments reduce to cTrue
theorem cnf4chain_sat_0111 :
    reduce 60 (cnf4chain false true true true) = cTrue := by native_decide
theorem cnf4chain_sat_1000 :
    reduce 60 (cnf4chain true false false false) = cTrue := by native_decide

-- A few UNSAT assignments reduce to cFalse
theorem cnf4chain_unsat_0000 :
    reduce 60 (cnf4chain false false false false) = cFalse := by native_decide
theorem cnf4chain_unsat_1111 :
    reduce 60 (cnf4chain true true true true) = cFalse := by native_decide

/-! ## Normalized embeddings -/

/-- Normalized embedded 4-clause formula. -/
def normEmbed4 (fuel : Nat) (b0 b1 b2 b3 : Bool) : Term :=
  iterDeepRewrite fuel (.obs (embed (cnf4chain b0 b1 b2 b3)))

-- Check term depth at low fuel to gauge computational cost
#eval termDepth (normEmbed4 3 false false false false)
#eval termDepth (normEmbed4 3 false true true true)

/-! ## Depth profiles at fuel 3

  Start with fuel 3 (cheaper than fuel 5) to see if profiles separate. -/

-- f₀ profiles for all 16 assignments at fuel 3, depth 0-20
#eval f0Profile 20 (normEmbed4 3 false false false false)  -- 0000 UNSAT
#eval f0Profile 20 (normEmbed4 3 false false false true)   -- 0001 UNSAT
#eval f0Profile 20 (normEmbed4 3 false false true false)   -- 0010 UNSAT
#eval f0Profile 20 (normEmbed4 3 false false true true)    -- 0011 UNSAT
#eval f0Profile 20 (normEmbed4 3 false true false false)   -- 0100 UNSAT
#eval f0Profile 20 (normEmbed4 3 false true false true)    -- 0101 UNSAT
#eval f0Profile 20 (normEmbed4 3 false true true false)    -- 0110 UNSAT
#eval f0Profile 20 (normEmbed4 3 false true true true)     -- 0111 SAT
#eval f0Profile 20 (normEmbed4 3 true false false false)   -- 1000 SAT
#eval f0Profile 20 (normEmbed4 3 true false false true)    -- 1001 UNSAT
#eval f0Profile 20 (normEmbed4 3 true false true false)    -- 1010 UNSAT
#eval f0Profile 20 (normEmbed4 3 true false true true)     -- 1011 UNSAT
#eval f0Profile 20 (normEmbed4 3 true true false false)    -- 1100 UNSAT
#eval f0Profile 20 (normEmbed4 3 true true false true)     -- 1101 UNSAT
#eval f0Profile 20 (normEmbed4 3 true true true false)     -- 1110 UNSAT
#eval f0Profile 20 (normEmbed4 3 true true true true)      -- 1111 UNSAT

/-! ## Scalar countF0 for comparison -/

#eval countF0 (normEmbed4 3 false false false false)  -- 0000
#eval countF0 (normEmbed4 3 false true true true)     -- 0111 SAT
#eval countF0 (normEmbed4 3 true false false false)   -- 1000 SAT
#eval countF0 (normEmbed4 3 true true true true)      -- 1111

/-! ## Analysis: fuel 3 gives only 8 distinct profiles for 16 assignments

  The profiles split by (x₀, truecount(x₁,x₂,x₃)):
  - x₀=0, tc=0: 0000 unique
  - x₀=0, tc=1: 0001=0010=0100 (collision!)
  - x₀=0, tc=2: 0011=0101=0110 (collision!)
  - x₀=0, tc=3: 0111 (SAT) unique
  - x₀=1, tc=0: 1000 (SAT) unique
  - x₀=1, tc=1: 1001=1010=1100 (collision!)
  - x₀=1, tc=2: 1011=1101=1110 (collision!)
  - x₀=1, tc=3: 1111 unique

  d_min = 2 (x₀ bit + truecount of rest).
  rank(M) = 3 for phi4chain.
  RANK-DIMENSION CONJECTURE: REFUTED at fuel 3.

  The collisions are between assignments with the SAME truecount
  of the shared variables (x₁,x₂,x₃). This is the same truecount
  symmetry seen in phi, but now it's a PARTIAL symmetry — x₀ is
  distinguished because the encoding treats it asymmetrically.

  Let's check: do colliding assignments share SAT status?
  - 0001, 0010, 0100: all UNSAT. Safe.
  - 0011, 0101, 0110: all UNSAT. Safe.
  - 1001, 1010, 1100: all UNSAT. Safe.
  - 1011, 1101, 1110: all UNSAT. Safe.

  So the collisions are ALL between UNSAT assignments. The two SAT
  assignments (0111, 1000) have unique profiles. The depth profile
  DOES separate SAT from UNSAT at fuel 3, just not all 16 assignments.

  Critical: for the SEARCH problem, we only need to distinguish
  SAT from UNSAT. The depth profile achieves this despite collisions
  among UNSAT assignments.

  Try fuel 5 to see if more profiles separate: -/

-- Test a few colliding pairs at fuel 5 to check if they separate
-- 0001 vs 0010 (both UNSAT, same profile at fuel 3)
#eval f0Profile 20 (normEmbed4 5 false false false true)   -- 0001
#eval f0Profile 20 (normEmbed4 5 false false true false)   -- 0010

-- 0111 (SAT) and 1000 (SAT) — do they still have distinct profiles?
#eval f0Profile 20 (normEmbed4 5 false true true true)     -- 0111 SAT
#eval f0Profile 20 (normEmbed4 5 true false false false)   -- 1000 SAT

-- Scalar countF0 at fuel 5
#eval countF0 (normEmbed4 5 false false false true)   -- 0001
#eval countF0 (normEmbed4 5 false false true false)   -- 0010
#eval countF0 (normEmbed4 5 false true true true)     -- 0111 SAT
#eval countF0 (normEmbed4 5 true false false false)   -- 1000 SAT

end DepthProfile4
end SpectralMonoid
