/-
  Coupled Trees with Message Passing
  ====================================

  Decompose a SAT formula into tree-like clusters with coupling
  constraints. Solve each cluster independently. Negotiate coupling
  via iterative message passing.

  This is the bridge from tree decomposition to belief propagation:
  - Each cluster is a tractable subproblem (small tree)
  - Coupling constraints connect clusters via shared variables
  - Messages encode "what I need from you" between clusters
  - Iteration refines the coupling until convergence (or failure)

  Computational paradigm:
  - SmartDAG: solve once, combine once (no iteration)
  - CDCL: search with learning (sequential iteration)
  - Message passing: solve all clusters, exchange messages, repeat
    (parallel iteration)

  A message from cluster A to cluster B says:
  "Given what I know about my variables, these are the valid
  assignments for our shared variables."

  After each round, clusters update their solutions based on
  incoming messages. Convergence = all clusters agree on shared vars.
-/

import SpectralArithmetic.Rotation.ClauseLearning

namespace RotationCalculus

open Term

/-! ## Cluster decomposition

    Decompose a formula into clusters. Each cluster is a set of
    variables with their local clauses. Shared variables create
    coupling between clusters. -/

/-- A cluster: a set of variables and their local clauses. -/
structure Cluster where
  id : ℕ
  vars : List ℕ
  localClauses : SATFormula
  deriving Repr

/-- Coupling between two clusters: shared variables and cross-clauses. -/
structure Coupling where
  cluster1 : ℕ
  cluster2 : ℕ
  sharedVars : List ℕ
  crossClauses : SATFormula
  deriving Repr

/-- A message: valid assignments for shared variables, from one
    cluster's perspective. -/
structure Message where
  from_ : ℕ
  to_ : ℕ
  validAssignments : List (List (ℕ × Bool))
  deriving Repr

/-- Decompose a formula into k clusters by splitting variables evenly. -/
def decompose (formula : SATFormula) (n : ℕ) (k : ℕ)
    : List Cluster × List Coupling :=
  let varsPerCluster := (n + k - 1) / k
  let clusters := (List.range k).map fun i =>
    let start := i * varsPerCluster
    let end_ := min ((i + 1) * varsPerCluster) n
    let vars := (List.range (end_ - start)).map (· + start)
    let local_ := clausesInScope formula vars
    { id := i, vars := vars, localClauses := local_ }
  -- Find couplings between adjacent clusters
  let couplings := (List.range (k - 1)).filterMap fun i =>
    let c1 := clusters.getD i { id := 0, vars := [], localClauses := [] }
    let c2 := clusters.getD (i + 1) { id := 0, vars := [], localClauses := [] }
    let shared := c1.vars.filter fun v => c2.vars.contains v
    let cross := crossClauses formula c1.vars c2.vars
    if cross.isEmpty then none
    else some { cluster1 := i, cluster2 := i + 1,
                sharedVars := shared, crossClauses := cross }
  -- Also find couplings between non-adjacent clusters (for random instances)
  let nonAdj := (List.range k).flatMap fun i =>
    (List.range k).filterMap fun j =>
      if j > i + 1 then
        let c1 := clusters.getD i { id := 0, vars := [], localClauses := [] }
        let c2 := clusters.getD j { id := 0, vars := [], localClauses := [] }
        let cross := crossClauses formula c1.vars c2.vars
        if cross.isEmpty then none
        else some { cluster1 := i, cluster2 := j,
                    sharedVars := [], crossClauses := cross }
      else none
  (clusters, couplings ++ nonAdj)

/-! ## Solve a cluster given incoming messages

    Each cluster solves its local problem, constrained by messages
    from neighbors about shared variable assignments. -/

/-- Solve a cluster: find all valid assignments for its variables,
    respecting local clauses and incoming message constraints. -/
def solveCluster (cluster : Cluster)
    (incomingConstraints : List (ℕ × Bool))
    : List (List (ℕ × Bool)) × ℕ :=
  -- Variables not fixed by incoming constraints
  let freeVars := cluster.vars.filter fun v =>
    !incomingConstraints.any fun (v', _) => v == v'
  -- Build combined formula: local + constraints from messages
  let constraintClauses := incomingConstraints.map fun (v, p) => [(v, p)]
  let formula := cluster.localClauses ++ constraintClauses
  -- Solve with Choice (AND-OR search)
  let tree := buildSearchTree formula freeVars incomingConstraints
  let (found, cost) := evalSearchTree tree
  if found then
    -- Find all valid assignments
    let assigns := allVarAssignments freeVars
    let valid := assigns.filterMap fun a =>
      let full := incomingConstraints ++ a
      if satisfiesFormula full formula then some full
      else none
    (valid, cost)
  else ([], cost)

/-! ## Message computation

    A message from cluster A to cluster B says: "for each possible
    assignment of variables that B cares about, here's whether
    I can find a compatible solution."

    Specifically: project A's valid solutions onto the variables
    shared with B (or variables in B's cross-clauses). -/

/-- Compute message from one cluster to a coupling.
    Returns valid assignments for cross-clause variables. -/
def computeMessage (solutions : List (List (ℕ × Bool)))
    (coupling : Coupling) (fromCluster : ℕ)
    : Message :=
  let toCluster := if coupling.cluster1 == fromCluster
    then coupling.cluster2 else coupling.cluster1
  -- Extract the variables that matter for the coupling
  let relevantVars := (coupling.crossClauses.flatMap fun clause =>
    clause.map fun (v, _) => v).eraseDups
  -- Project solutions onto relevant variables
  let projected := solutions.map fun sol =>
    sol.filter fun (v, _) => relevantVars.contains v
  -- Deduplicate
  let unique := projected.eraseDups
  { from_ := fromCluster, to_ := toCluster,
    validAssignments := unique }

/-! ## Iterative message passing

    1. Solve each cluster independently (no constraints)
    2. Compute messages between coupled clusters
    3. Resolve each cluster with incoming message constraints
    4. Repeat until convergence or max iterations -/

/-- One round of message passing.
    Returns (cluster_solutions, messages, total_cost). -/
def messagePassRound (clusters : List Cluster)
    (couplings : List Coupling)
    (prevMessages : List Message)
    : List (List (List (ℕ × Bool))) × List Message × ℕ :=
  -- Solve each cluster with constraints from incoming messages
  let solutions := clusters.map fun cluster =>
    -- Collect constraints from messages TO this cluster
    let incoming := prevMessages.filter fun m => m.to_ == cluster.id
    let constraints := incoming.flatMap fun m =>
      -- Use the first valid assignment from each message as a constraint
      match m.validAssignments.head? with
      | some assign => assign
      | none => []
    let (sols, _) := solveCluster cluster constraints
    sols
  -- Compute new messages
  let messages := couplings.flatMap fun coupling =>
    let c1Sols := solutions.getD coupling.cluster1 []
    let c2Sols := solutions.getD coupling.cluster2 []
    let msg1to2 := computeMessage c1Sols coupling coupling.cluster1
    let msg2to1 := computeMessage c2Sols coupling coupling.cluster2
    [msg1to2, msg2to1]
  let cost := clusters.length  -- one solve per cluster per round
  (solutions, messages, cost)

/-- Check if messages have converged (same as previous round). -/
def messagesConverged (prev curr : List Message) : Bool :=
  if prev.length != curr.length then false
  else (prev.zip curr).all fun (p, c) =>
    p.validAssignments.length == c.validAssignments.length

/-- Run message passing for up to maxIter rounds. -/
def runMessagePassing (formula : SATFormula) (n : ℕ)
    (nClusters : ℕ) (maxIter : ℕ := 10)
    : Option (List (ℕ × Bool)) × ℕ × ℕ :=  -- (solution, cost, iterations)
  let (clusters, couplings) := decompose formula n nClusters
  let rec iterate (messages : List Message) (iter cost : ℕ)
      : Option (List (ℕ × Bool)) × ℕ × ℕ :=
    if iter ≥ maxIter then (none, cost, iter)
    else
      let (solutions, newMessages, roundCost) :=
        messagePassRound clusters couplings messages
      let totalCost := cost + roundCost
      -- Check convergence
      if messagesConverged messages newMessages then
        -- Converged! Try to combine cluster solutions
        let combined := solutions.foldl (fun acc sols =>
          match sols.head? with
          | some s => acc ++ s
          | none => acc) []
        -- Verify combined solution against full formula
        if satisfiesFormula combined formula then
          (some combined, totalCost, iter + 1)
        else
          (none, totalCost, iter + 1)
      else
        iterate newMessages (iter + 1) totalCost
  iterate [] 0 0

/-! ## Comparison: all strategies including message passing -/

-- Random 3-SAT n=8
#eval do
  let n := 8
  let m := 32
  let data := [42, 123, 456].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let md := minDegOrdering f n
    let (_, chmd) := choiceSATOrdered f md
    let (_, cdcl, learned) := satCDCL f n
    let (r, mpCost, mpIter) := runMessagePassing f n 2
    let (r4, mp4Cost, mp4Iter) := runMessagePassing f n 4
    s!"seed={seed} flat={flat} ch+md={chmd} cdcl={cdcl}(L={learned}) mp2={mpCost}(i={mpIter},f={r.isSome}) mp4={mp4Cost}(i={mp4Iter},f={r4.isSome})"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- Random 3-SAT n=10
#eval do
  let n := 10
  let m := 42
  let data := [42, 123, 456].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let md := minDegOrdering f n
    let (_, chmd) := choiceSATOrdered f md
    let (_, cdcl, learned) := satCDCL f n
    let (r, mpCost, mpIter) := runMessagePassing f n 2
    let (r5, mp5Cost, mp5Iter) := runMessagePassing f n 5
    s!"seed={seed} flat={flat} ch+md={chmd} cdcl={cdcl}(L={learned}) mp2={mpCost}(i={mpIter},f={r.isSome}) mp5={mp5Cost}(i={mp5Iter},f={r5.isSome})"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- Structured instances
#eval do
  let data := [8, 10, 12].map fun n =>
    let f := reachInstance n 3
    let (_, smart) := satSmartDAG f n 2
    let (_, cdcl, learned) := satCDCL f n
    let (r, mpCost, mpIter) := runMessagePassing f n 2
    s!"n={n} smart={smart} cdcl={cdcl}(L={learned}) mp2={mpCost}(i={mpIter},f={r.isSome})"
  IO.println s!"Structured reach=3:"
  IO.println (String.intercalate "\n" data)

-- PHP (unsatisfiable)
#eval do
  let f := pigeonhole 3 2
  let (_, cdcl, learned) := satCDCL f 6
  let (r, mpCost, mpIter) := runMessagePassing f 6 2
  IO.println s!"PHP(3,2): cdcl={cdcl}(L={learned}) mp2={mpCost}(i={mpIter},f={r.isSome})"

#eval do
  let f := pigeonhole 4 3
  let (_, cdcl, learned) := satCDCL f 12
  let (r, mpCost, mpIter) := runMessagePassing f 12 3
  IO.println s!"PHP(4,3): cdcl={cdcl}(L={learned}) mp3={mpCost}(i={mpIter},f={r.isSome})"

/-! ## Assessment

    Message passing is a fundamentally different paradigm:
    - DPLL/CDCL: sequential search, one path at a time
    - SmartDAG: spatial decomposition, one split at a time
    - Message passing: parallel cluster solving, iterative refinement

    Expected behavior:
    - If clusters are weakly coupled: converges in few iterations.
      Each cluster is a small tractable problem. Total cost ≈
      nClusters × (cost per cluster) × iterations.
    - If clusters are strongly coupled: messages oscillate (don't
      converge) or converge to inconsistent states. This is where
      BP fails in the hard regime.
    - The NUMBER OF ITERATIONS to convergence is the coupling
      strength — another complexity fingerprint.

    Connection to statistical physics:
    - Our "message" (list of valid assignments for shared vars)
      is a simplified version of BP messages (marginal distributions
      over variable states).
    - Full BP would send probability distributions, not hard
      assignment lists. This would handle uncertainty better.
    - Survey propagation would send distributions OVER distributions
      (one level deeper — accounting for cluster structure).

    What this IS:
    - A simple form of iterative belief propagation
    - The bridge from tree decomposition to message passing
    - A new computational paradigm in the rotation framework

    What this IS NOT:
    - Full belief propagation (we use hard assignments, not probabilities)
    - Survey propagation (we don't model cluster structure)
    - A solution to random 3-SAT at threshold (that requires SP) -/

end RotationCalculus
