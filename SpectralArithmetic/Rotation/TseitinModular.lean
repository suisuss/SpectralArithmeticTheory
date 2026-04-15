/-
  Modular Tseitin Formulas  (issue #45)
  ======================================

  Tseitin formula on a "chain of cliques" graph:
    - k clusters, each a complete graph K_n
    - Adjacent clusters joined by a single bridge edge
      (connecting vertex 0 of cluster i to vertex 0 of cluster i+1)
    - One vertex gets charge 1, all others charge 0
    - UNSAT by parity (sum of charges is odd; sum over edges in
      any graph is always even since each edge has two endpoints)

  Variables: one per EDGE (both cluster edges and bridges).
  Clauses:   for each vertex v, the 2^(deg(v)-1) CNF clauses
             encoding XOR(incident edges) = charge(v).

  Proof complexity theory (Ben-Sasson–Wigderson 2001, Urquhart 1987):
  resolution proofs of Tseitin(G, charge) have length
  2^Ω(expansion(G)). K_n has good expansion; chaining cliques
  preserves expansion at cluster granularity. So we expect
  scaling in k for fixed n, and in n for fixed k.
-/

import SpectralArithmetic.Rotation.SATEncoding

set_option linter.style.longLine false

namespace RotationCalculus

/-- Get bit i of Nat a (0 = least significant). -/
private def bitAt (a i : Nat) : Bool := (a / 2 ^ i) % 2 == 1

/-- CNF clauses encoding XOR(vars) = charge.
    Produces 2^(d-1) clauses where d = vars.length, each of width d.
    A clause rules out exactly the assignments with wrong XOR parity. -/
def xorClauses (vars : List Nat) (charge : Bool) : List SATClause :=
  let d := vars.length
  (List.range (2 ^ d)).filterMap fun a =>
    let bits := (List.range d).map (bitAt a)
    let xorVal := bits.foldl (fun acc b => acc != b) false
    if xorVal == charge then none
    else
      -- Assignment (bits) has the wrong parity. Emit the clause
      -- that rules it out: literal is positive iff bit was false.
      some (vars.zip bits |>.map fun (v, b) => (v, !b))

/-- Unordered pairs (i, j) with 0 ≤ i < j < n. -/
private def orderedPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i =>
    ((List.range n).drop (i + 1)).map (fun j => (i, j))

/-- Cluster edges: K_n on vertices [vertexBase, vertexBase + n).
    Returns (u, v, edge_id) triples, edge_id = offset + local_index. -/
def cliqueEdges (n vertexBase offset : Nat) : List (Nat × Nat × Nat) :=
  (orderedPairs n).zip (List.range (n * (n - 1) / 2)) |>.map
    fun ((i, j), idx) => (vertexBase + i, vertexBase + j, offset + idx)

/-- Bridge edges: connects vertex 0 of cluster c to vertex 0 of cluster c+1. -/
def bridgeEdges (k n offset : Nat) : List (Nat × Nat × Nat) :=
  (List.range (k - 1)).map fun c =>
    (c * n, (c + 1) * n, offset + c)

/-- Full edge list for the modular Tseitin graph. -/
def modularEdges (k n : Nat) : List (Nat × Nat × Nat) :=
  let edgesPerCluster := n * (n - 1) / 2
  let cEdges := (List.range k).flatMap fun c =>
    cliqueEdges n (c * n) (c * edgesPerCluster)
  let bEdges := bridgeEdges k n (k * edgesPerCluster)
  cEdges ++ bEdges

/-- Edges incident to vertex v, returned as their edge_ids. -/
private def incidentEdgeIds
    (edges : List (Nat × Nat × Nat)) (v : Nat) : List Nat :=
  edges.filterMap fun (u1, u2, eid) =>
    if u1 == v || u2 == v then some eid else none

/-- Modular Tseitin formula on chain of k K_n cliques.
    `seed` selects which vertex gets charge 1 (determinism,
    different seeds give different-but-isomorphic UNSAT instances).
    Returns (formula, nVars). -/
def modularTseitinFormula (k n seed : Nat) : SATFormula × Nat :=
  if h : k < 1 ∨ n < 2 then
    ([[]], 0)  -- degenerate; empty clause → trivially UNSAT
  else
    let edges := modularEdges k n
    let totalVars := edges.length
    let totalVertices := k * n
    let charged := seed % totalVertices
    let formula := (List.range totalVertices).flatMap fun v =>
      let incident := incidentEdgeIds edges v
      xorClauses incident (v == charged)
    (formula, totalVars)

/-! ## Sanity: small smoke test -/

#eval! do
  let (f, nv) := modularTseitinFormula 2 3 0
  IO.println s!"k=2 n=3 seed=0: vars={nv} clauses={f.length}"
  -- Charged vertex = 0 (seed % 6 = 0); vertex 0 has deg 3
  -- (2 clique edges within cluster 0 + 1 bridge)
  -- Non-portal vertices have deg 2 (K_3 interior). Clauses:
  --   deg-2, charge 0:  2 clauses of width 2
  --   deg-3, charge 0:  4 clauses of width 3
  --   deg-3, charge 1:  4 clauses of width 3
  let (g, nv2) := modularTseitinFormula 3 3 0
  IO.println s!"k=3 n=3 seed=0: vars={nv2} clauses={g.length}"

end RotationCalculus
