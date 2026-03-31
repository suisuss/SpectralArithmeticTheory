/-
  Industrial-Like Instances: Modular Structure + Transition Prediction
  =====================================================================

  Real industrial SAT instances have MODULAR structure:
  - Dense local clusters (circuit blocks, software modules)
  - Sparse cross-cluster connections (interfaces, APIs)

  We generate instances with controlled modularity:
  1. CLUSTERS: k groups of m variables, dense internal 3-SAT
  2. BRIDGES: b clauses spanning cluster boundaries
  3. HIERARCHY: tree of clusters with parent-child constraints

  Then run crawl-contract and check if the prediction signals
  (width narrowing, learned count decrease, partial contraction)
  appear before the transition.
-/

import SpectralArithmetic.Rotation.TransitionPredictor

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace RotationCalculus

open Term

/-! ## Modular formula generators -/

/-- Generate a dense random 3-SAT cluster on variables [base..base+size). -/
def randomCluster (base size nClauses seed : ℕ) : SATFormula :=
  if size < 3 then []
  else
    let rec go (remaining : ℕ) (state : UInt32) (acc : SATFormula)
        : SATFormula :=
      match remaining with
      | 0 => acc
      | remaining + 1 =>
        let (v1r, s1) := xrandMod state size
        let (p1, s2) := xrandMod s1 2
        let (v2r, s3) := xrandMod s2 (size - 1)
        let v2 := if v2r >= v1r then v2r + 1 else v2r
        let (p2, s4) := xrandMod s3 2
        let (v3r, s5) := xrandMod s4 (size - 2)
        let v3' := if v3r >= min v1r v2 then v3r + 1 else v3r
        let v3 := if v3' >= max v1r v2 then v3' + 1 else v3'
        let (p3, s6) := xrandMod s5 2
        let clause := [(base + v1r, p1 == 1),
                        (base + v2, p2 == 1),
                        (base + v3, p3 == 1)]
        go remaining s6 (acc ++ [clause])
    go nClauses (seedToState seed) []

/-- Generate bridge clauses between two clusters.
    Each bridge connects one variable from each cluster. -/
def bridgeClauses (base1 size1 base2 size2 nBridges seed : ℕ)
    : SATFormula :=
  let rec go (remaining : ℕ) (state : UInt32) (acc : SATFormula)
      : SATFormula :=
    match remaining with
    | 0 => acc
    | remaining + 1 =>
      let (v1, s1) := xrandMod state size1
      let (p1, s2) := xrandMod s1 2
      let (v2, s3) := xrandMod s2 size2
      let (p2, s4) := xrandMod s3 2
      let clause := [(base1 + v1, p1 == 1), (base2 + v2, p2 == 1)]
      go remaining s4 (acc ++ [clause])
  go nBridges (seedToState seed) []

/-- Modular UNSAT formula: k clusters + bridges + forcing clauses.
    Each cluster has dense internal constraints.
    Bridge clauses connect adjacent clusters.
    Forcing clauses make the whole thing UNSAT. -/
def modularFormula (nClusters clusterSize clausesPerCluster
    bridgesPerPair : ℕ) (seed : ℕ) : SATFormula × ℕ :=
  let totalVars := nClusters * clusterSize
  -- Generate clusters
  let clusters := (List.range nClusters).flatMap fun i =>
    let base := i * clusterSize
    randomCluster base clusterSize clausesPerCluster (seed + i * 100)
  -- Generate bridges between adjacent clusters
  let bridges := (List.range (nClusters - 1)).flatMap fun i =>
    let base1 := i * clusterSize
    let base2 := (i + 1) * clusterSize
    bridgeClauses base1 clusterSize base2 clusterSize
      bridgesPerPair (seed + 1000 + i * 100)
  -- Force UNSAT: add contradictory unit clauses on first variable
  let forcing := [[(0, true)], [(0, false)]]
  (clusters ++ bridges ++ forcing, totalVars)

/-- Hierarchical formula: tree of clusters.
    Root cluster connects to 2 child clusters.
    Each child connects to 2 grandchildren.
    depth = number of levels. -/
def hierarchicalFormula (depth clusterSize clausesPerCluster
    bridgesPerPair : ℕ) (seed : ℕ) : SATFormula × ℕ :=
  -- Total clusters = 2^depth - 1 (complete binary tree)
  let nClusters := 2^depth - 1
  let totalVars := nClusters * clusterSize
  -- Generate clusters
  let clusters := (List.range nClusters).flatMap fun i =>
    let base := i * clusterSize
    randomCluster base clusterSize clausesPerCluster (seed + i * 100)
  -- Tree bridges: cluster i connects to clusters 2i+1 and 2i+2
  let bridges := (List.range nClusters).flatMap fun i =>
    let left := 2 * i + 1
    let right := 2 * i + 2
    let leftBridges := if left < nClusters then
      bridgeClauses (i * clusterSize) clusterSize
        (left * clusterSize) clusterSize
        bridgesPerPair (seed + 2000 + i * 100)
    else []
    let rightBridges := if right < nClusters then
      bridgeClauses (i * clusterSize) clusterSize
        (right * clusterSize) clusterSize
        bridgesPerPair (seed + 3000 + i * 100)
    else []
    leftBridges ++ rightBridges
  -- Force UNSAT
  let forcing := [[(0, true)], [(0, false)]]
  (clusters ++ bridges ++ forcing, totalVars)

/-! ## Tests -/

#eval! do
  IO.println "=== INDUSTRIAL-LIKE INSTANCES ==="
  IO.println ""

  -- Modular: 3 clusters of 4 vars, 8 clauses each, 2 bridges
  IO.println "--- Modular (3 clusters x 4 vars) ---"
  let (f1, nv1) := modularFormula 3 4 8 2 42
  IO.println s!"  vars={nv1} clauses={List.length f1}"
  let (sat1, _) := flatBruteForce f1 nv1
  IO.println s!"  SAT={sat1.isSome}"
  if sat1.isNone then
    let (logs1, _, unsat1) := crawlContractSolve f1 nv1 20
    IO.println s!"  crawl-contract: rounds={List.length logs1} UNSAT={unsat1}"
    for (log : CCRound) in logs1 do
      IO.println s!"    R{log.round}: {log.phase} L={log.learned} avgW={log.avgWidth} ratio={log.contrRatio}%"

  IO.println ""
  IO.println "--- Modular (4 clusters x 5 vars) ---"
  let (f2, nv2) := modularFormula 4 5 12 3 42
  IO.println s!"  vars={nv2} clauses={List.length f2}"
  let (sat2, _) := flatBruteForce f2 nv2
  IO.println s!"  SAT={sat2.isSome}"
  if sat2.isNone then
    let (logs2, _, unsat2) := crawlContractSolve f2 nv2 20
    IO.println s!"  crawl-contract: rounds={List.length logs2} UNSAT={unsat2}"
    for (log : CCRound) in logs2 do
      IO.println s!"    R{log.round}: {log.phase} L={log.learned} avgW={log.avgWidth} ratio={log.contrRatio}%"

  IO.println ""
  IO.println "--- Hierarchical (depth=2, 3 clusters x 4 vars) ---"
  let (f3, nv3) := hierarchicalFormula 2 4 8 2 42
  IO.println s!"  vars={nv3} clauses={List.length f3}"
  let (sat3, _) := flatBruteForce f3 nv3
  IO.println s!"  SAT={sat3.isSome}"
  if sat3.isNone then
    let (logs3, _, unsat3) := crawlContractSolve f3 nv3 20
    IO.println s!"  crawl-contract: rounds={List.length logs3} UNSAT={unsat3}"
    for (log : CCRound) in logs3 do
      IO.println s!"    R{log.round}: {log.phase} L={log.learned} avgW={log.avgWidth} ratio={log.contrRatio}%"

  IO.println ""
  IO.println "--- Hierarchical (depth=3, 7 clusters x 3 vars) ---"
  let (f4, nv4) := hierarchicalFormula 3 3 6 2 42
  IO.println s!"  vars={nv4} clauses={List.length f4}"
  let (sat4, _) := flatBruteForce f4 nv4
  IO.println s!"  SAT={sat4.isSome}"
  if sat4.isNone then
    let (logs4, _, unsat4) := crawlContractSolve f4 nv4 20
    IO.println s!"  crawl-contract: rounds={List.length logs4} UNSAT={unsat4}"
    for (log : CCRound) in logs4 do
      IO.println s!"    R{log.round}: {log.phase} L={log.learned} avgW={log.avgWidth} ratio={log.contrRatio}%"

#eval! do
  IO.println ""
  IO.println "=== TRANSITION SIGNALS ON MODULAR INSTANCES ==="
  IO.println ""
  IO.println "clusters\tvars\twidth_traj\tlearned_traj\tratio_traj\tproven"
  for k in [2, 3, 4] do
    for m in [3, 4, 5] do
      let (f, nv) := modularFormula k m (m * 2) 2 42
      let (sat, _) := flatBruteForce f nv
      if sat.isNone then
        let (logs, _, proven) := crawlContractSolve f nv 15
        let signals := extractSignals logs
        let widths := signals.map fun (s : RoundSignal) => s.avgWidth
        let counts := signals.map fun (s : RoundSignal) => s.learned
        let ratios := signals.map fun (s : RoundSignal) => s.ratio
        IO.println s!"{k}x{m}\t\t{nv}\t{widths}\t\t{counts}\t\t{ratios}\t{proven}"

/-! ## Assessment

    If the prediction signals (width narrowing, learned decrease,
    partial contraction) appear on modular instances:

    → The transition prediction generalizes beyond PHP
    → The crawl budget can be set optimally for industrial instances
    → The split escape detects module boundaries

    If the signals DON'T appear:
    → The prediction is PHP-specific
    → Different signal types needed for modular structure
    → The modularity itself might be the signal (shared vars at split)
-/

end RotationCalculus
