/-
  Rotation Calculus: Runner
  ==========================
  Execute and display the examples.
-/

import SpectralArithmetic.Rotation.Examples

open RotationCalculus Term

def main : IO Unit := do
  IO.println "=== Rotation Calculus Examples ==="
  IO.println ""

  IO.println "--- Example 1: Unconstrained ---"
  IO.println (s!"run trivial [1,2,3]: {repr (run .trivial (.observe elems3) 10)}")
  IO.println (s!"verifyArrangement trivial [1,2,3]: {verifyArrangement .trivial elems3}")
  IO.println ""

  IO.println "--- Example 2: Ascending order ---"
  IO.println (s!"verify [1,2,3] sorted: {verifyArrangement ascendingConstraint sorted123}")
  IO.println (s!"verify [3,1,2] unsorted: {verifyArrangement ascendingConstraint unsorted312}")
  IO.println (s!"verify [2,1,3] unsorted: {verifyArrangement ascendingConstraint unsorted213}")
  IO.println ""

  IO.println "--- Example 3: Triangle 2-coloring ---"
  IO.println (s!"verify (v0:R, v1:B, v2:R): {verifyArrangement triConstraint triColor_RBR}")
  IO.println (s!"verify (v0:R, v1:B, v2:B): {verifyArrangement triConstraint triColor_RBB}")
  IO.println (s!"verify (v0:R, v1:R, v2:R): {verifyArrangement triConstraint triColor_RRR}")
  IO.println (s!"verify (v0:R, v1:R, v2:B): {verifyArrangement triConstraint triColor_RRB}")
  IO.println (s!"verify (v0:B, v1:R, v2:B): {verifyArrangement triConstraint triColor_BRB}")
  IO.println (s!"verify (v0:B, v1:B, v2:R): {verifyArrangement triConstraint triColor_BBR}")
  IO.println (s!"verify 3-color (R,B,G): {verifyArrangement triConstraint triColor3c}")
  IO.println ""

  IO.println "--- Example 4: Subset sum (target=11) ---"
  IO.println (s!"verify [3*,7,1,8*,2] (3+8=11): {verifySubsetSum 11 ssElems1}")
  IO.println (s!"verify [3,7*,1*,8,2*] (7+1+2=10): {verifySubsetSum 11 ssElems2}")
  IO.println (s!"verify [3*,7*,1*,8,2] (3+7+1=11): {verifySubsetSum 11 ssElems3}")
  IO.println ""

  IO.println "--- Example 5: Brute-force search ---"
  let sortSearch := bruteForceSearch ascendingConstraint
    [labeledElement 3, labeledElement 1, labeledElement 2]
  IO.println (s!"search sorted [3,1,2]: {(sortSearch.map (·.map getLabel))}")

  let triSearch2 := (bruteForceSearch triConstraint
    [coloredVertex 0 0, coloredVertex 1 1, coloredVertex 2 0]).isSome
  IO.println (s!"search 2-color triangle: found={triSearch2}")

  let triSearch3 := (bruteForceSearch triConstraint
    [coloredVertex 0 0, coloredVertex 1 1, coloredVertex 2 2]).isSome
  IO.println (s!"search 3-color triangle: found={triSearch3}")

  let elems := [labeledElement 1, labeledElement 2, labeledElement 3]
  let ps := perms elems
  let valid := ps.filter fun perm => verifyArrangement ascendingConstraint (fromList perm)
  IO.println (s!"sorted arrangements of [1,2,3]: {valid.length}/{ps.length}")
  IO.println ""

  IO.println "--- Example 6: Constraint density ---"
  let ps6 := perms repeatedElems
  let validNoRepeat := ps6.filter fun perm => verifyArrangement noRepeatConstraint (fromList perm)
  let validAscending := ps6.filter fun perm => verifyArrangement ascendingConstraint (fromList perm)
  IO.println (s!"no-repeat constraint: {validNoRepeat.length}/{ps6.length} valid (sparse)")
  IO.println (s!"ascending constraint: {validAscending.length}/{ps6.length} valid (dense)")
