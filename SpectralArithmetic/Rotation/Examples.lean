/-
  Rotation Calculus: Concrete Examples
  =====================================

  Using the language to encode and solve actual problems.
  Demonstrates verification (linear) vs search (exponential).

  Key architectural note: the base rotation rule walks into compound elements.
  For list-level problems (sorting, coloring, subset sum), we use a
  list-level verifier that processes one element per step rather than
  descending into element structure. This is the natural way to use the
  language: the constraint operates on list elements, not sub-terms.
-/

import SpectralArithmetic.Rotation.Complexity

namespace RotationCalculus

open Term

/-! ## Element tagging -/

/-- Encode a natural number as a term (unary: n nested pairs). -/
def natToTerm : ℕ → Term
  | 0 => .ground
  | n + 1 => .pair (natToTerm n) .ground

/-- Decode a term back to a natural number. -/
def termToNat : Term → ℕ
  | .pair t .ground => 1 + termToNat t
  | _ => 0

/-- A labeled element. -/
def labeledElement (label : ℕ) : Term :=
  .pair (natToTerm label) .ground

/-- Extract label from a labeled element. -/
def getLabel (t : Term) : ℕ :=
  match t with
  | .pair inner _ => termToNat inner
  | _ => 0

-- Label round-trip
#eval getLabel (labeledElement 3)  -- 3
#eval getLabel (labeledElement 0)  -- 0

/-! ## List-level verification

    The base rotation rule descends into compound elements.
    For list-level problems, we define a verifier that processes one
    list element at a time, checking the constraint between adjacent
    elements in the arrangement. This is the natural abstraction:
    the rotation visits each element exactly once, in order. -/

/-- Verify a flat list arrangement by walking elements and checking
    the constraint between each element and the remainder.
    This is equivalent to the rotation rule on a list where elements
    are treated as atomic units. -/
def verifyList (C : Constraint) : List Term → Bool
  | [] => true
  | [a] => C.check a .ground  -- Last element: check against ground (end of list)
  | a :: b :: rest =>
    if C.check a (.pair b (fromList rest))
    then verifyList C (b :: rest)
    else false

/-- Verify from a nested term by extracting the list. -/
def verifyArrangement (C : Constraint) (t : Term) : Bool :=
  verifyList C t.toList

/-! ## Example 1: Unconstrained rotation (trivial — everything contracts)

    Demonstrates that with no constraint, every arrangement passes. -/

def elems3 : Term := fromList [labeledElement 1, labeledElement 2, labeledElement 3]

#eval run .trivial (.observe elems3) 10  -- contracted
#eval verifyArrangement .trivial elems3  -- true

/-! ## Example 2: Ordering constraint (ascending order) -/

def ascendingConstraint : Constraint where
  check := fun a b =>
    let la := getLabel a
    let lb := match b with
      | .pair first _ => getLabel first
      | _ => la
    decide (la ≤ lb)

def sorted123 : Term := fromList [labeledElement 1, labeledElement 2, labeledElement 3]
def unsorted312 : Term := fromList [labeledElement 3, labeledElement 1, labeledElement 2]
def unsorted213 : Term := fromList [labeledElement 2, labeledElement 1, labeledElement 3]

-- Verification: linear
#eval verifyArrangement ascendingConstraint sorted123    -- true
#eval verifyArrangement ascendingConstraint unsorted312  -- false
#eval verifyArrangement ascendingConstraint unsorted213  -- false

/-! ## Example 3: Graph coloring (2-coloring a triangle — impossible) -/

def coloredVertex (vertex : ℕ) (color : ℕ) : Term :=
  .pair (.pair (natToTerm vertex) (natToTerm color)) .ground

def getVertexId (t : Term) : ℕ :=
  match t with
  | .pair (.pair v _) _ => termToNat v
  | _ => 0

def getColor (t : Term) : ℕ :=
  match t with
  | .pair (.pair _ c) _ => termToNat c
  | _ => 0

-- Triangle edges: 0-1, 1-2, 0-2
def triangleEdges : List Edge := [(0, 1), (1, 2), (0, 2)]

-- Graph coloring constraint: check current vertex against ALL remaining vertices
def graphColorConstraint (edges : List Edge) : Constraint where
  check := fun a b =>
    let va := getVertexId a
    let ca := getColor a
    let rec checkRest : Term → Bool
      | .pair first rest =>
        let vb := getVertexId first
        let cb := getColor first
        let adjacent := edges.any fun (e1, e2) =>
          (e1 == va && e2 == vb) || (e1 == vb && e2 == va)
        if adjacent && ca == cb then false
        else checkRest rest
      | _ => true
    checkRest b

def triConstraint := graphColorConstraint triangleEdges

-- All 2-colorings of the triangle
def triColor_RBR : Term := fromList [coloredVertex 0 0, coloredVertex 1 1, coloredVertex 2 0]
def triColor_RBB : Term := fromList [coloredVertex 0 0, coloredVertex 1 1, coloredVertex 2 1]
def triColor_RRR : Term := fromList [coloredVertex 0 0, coloredVertex 1 0, coloredVertex 2 0]
def triColor_RRB : Term := fromList [coloredVertex 0 0, coloredVertex 1 0, coloredVertex 2 1]
def triColor_BRB : Term := fromList [coloredVertex 0 1, coloredVertex 1 0, coloredVertex 2 1]
def triColor_BBR : Term := fromList [coloredVertex 0 1, coloredVertex 1 1, coloredVertex 2 0]

-- None should work for 2-coloring
#eval verifyArrangement triConstraint triColor_RBR  -- false (0-2 adjacent, both 0)
#eval verifyArrangement triConstraint triColor_RBB  -- false (1-2 adjacent, both 1)
#eval verifyArrangement triConstraint triColor_RRR  -- false (0-1 adjacent, both 0)
#eval verifyArrangement triConstraint triColor_RRB  -- false (0-1 adjacent, both 0)
#eval verifyArrangement triConstraint triColor_BRB  -- false (0-2 adjacent, both 1)
#eval verifyArrangement triConstraint triColor_BBR  -- false (0-1 adjacent, both 1)

-- 3-coloring works
def triColor3c : Term := fromList [coloredVertex 0 0, coloredVertex 1 1, coloredVertex 2 2]
#eval verifyArrangement triConstraint triColor3c  -- true

/-! ## Example 4: Subset sum

    Elements: (value, selected?). Target: sum of selected = target.
    Constraint checks running sum doesn't exceed target;
    at the last element, must equal target exactly. -/

def ssElement (value : ℕ) (selected : Bool) : Term :=
  .pair (.pair (natToTerm value) (if selected then .pair .ground .ground else .ground)) .ground

def getSSValue (t : Term) : ℕ :=
  match t with
  | .pair (.pair v _) _ => termToNat v
  | _ => 0

def isSelected (t : Term) : Bool :=
  match t with
  | .pair (.pair _ (.pair _ _)) _ => true
  | _ => false

-- Subset sum as a global check: verify the entire list has selected sum = target.
-- Unlike adjacency constraints (sorting, coloring), subset sum is a global property.
-- We define a dedicated verifier rather than forcing it into the per-step constraint.
def verifySubsetSum (target : ℕ) (elements : List Term) : Bool :=
  let total := elements.foldl (fun acc t =>
    if isSelected t then acc + getSSValue t else acc) 0
  total == target

-- {3, 7, 1, 8, 2}, target = 11
def ssElems1 := [ssElement 3 true, ssElement 7 false, ssElement 1 false,
  ssElement 8 true, ssElement 2 false]  -- 3 + 8 = 11
def ssElems2 := [ssElement 3 false, ssElement 7 true, ssElement 1 true,
  ssElement 8 false, ssElement 2 true]  -- 7 + 1 + 2 = 10
def ssElems3 := [ssElement 3 true, ssElement 7 true, ssElement 1 true,
  ssElement 8 false, ssElement 2 false]  -- 3 + 7 + 1 = 11

#eval verifySubsetSum 11 ssElems1  -- true  (3 + 8 = 11)
#eval verifySubsetSum 11 ssElems2  -- false (7 + 1 + 2 = 10)
#eval verifySubsetSum 11 ssElems3  -- true  (3 + 7 + 1 = 11)

/-! ## Example 5: Brute-force search over arrangements -/

def insertAt (x : α) : ℕ → List α → List α
  | _, [] => [x]
  | 0, ys => x :: ys
  | n + 1, y :: ys => y :: insertAt x n ys

def perms : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    (perms xs).flatMap fun perm =>
      List.range (perm.length + 1) |>.map fun i =>
        insertAt x i perm

-- Search: try all arrangements, return first that contracts
def bruteForceSearch (C : Constraint) (elements : List Term) : Option (List Term) :=
  let ps := perms elements
  ps.find? fun perm => verifyArrangement C (fromList perm)

-- Search for sorted arrangement of [3, 1, 2]
#eval (bruteForceSearch ascendingConstraint
  [labeledElement 3, labeledElement 1, labeledElement 2]).map (·.map getLabel)
-- Should find [1, 2, 3]

-- How many of 6 permutations of [1,2,3] are sorted?
#eval do
  let elems := [labeledElement 1, labeledElement 2, labeledElement 3]
  let ps := perms elems
  let valid := ps.filter fun perm => verifyArrangement ascendingConstraint (fromList perm)
  return (valid.length, ps.length)
-- (1, 6)

-- Search for valid 2-coloring of triangle: should find nothing
#eval (bruteForceSearch triConstraint
  [coloredVertex 0 0, coloredVertex 1 1, coloredVertex 2 0]).isSome
-- false

-- Search for valid 3-coloring: should find something
#eval (bruteForceSearch triConstraint
  [coloredVertex 0 0, coloredVertex 1 1, coloredVertex 2 2]).isSome
-- true

/-! ## Example 6: Constraint density vs search difficulty -/

def noRepeatConstraint : Constraint where
  check := fun a b =>
    match b with
    | .pair first _ => decide (getLabel a ≠ getLabel first)
    | _ => true

def repeatedElems : List Term :=
  [labeledElement 1, labeledElement 1, labeledElement 2,
   labeledElement 2, labeledElement 3, labeledElement 3]

-- Sparse constraint: many valid arrangements
#eval do
  let ps := perms repeatedElems
  let valid := ps.filter fun perm => verifyArrangement noRepeatConstraint (fromList perm)
  return (valid.length, ps.length)

-- Dense constraint: fewer valid arrangements
#eval do
  let ps := perms repeatedElems
  let valid := ps.filter fun perm => verifyArrangement ascendingConstraint (fromList perm)
  return (valid.length, ps.length)

end RotationCalculus
