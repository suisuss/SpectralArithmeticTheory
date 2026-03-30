/-
  Belief Propagation: Soft Constraints and Marginal Distributions
  ================================================================

  Hard message passing fails because it commits to specific values.
  Belief propagation sends DISTRIBUTIONS: "I think x3=T with
  probability 0.7 and x3=F with probability 0.3."

  Implementation:
  - Replace Bool constraints with ℕ weights (count satisfying configs)
  - Messages are marginal distributions: (count_true, count_false) per var
  - Each cluster computes marginals given incoming messages
  - Iterate until marginals converge
  - Read off assignment from converged marginals (pick most likely value)

  This is the replica-symmetric (RS) version of cavity method.
  It works below the clustering transition. Above it, you'd need
  survey propagation (1RSB), which sends distributions OVER
  distributions.
-/

import SpectralArithmetic.Rotation.MessagePassing

namespace RotationCalculus

open Term

/-! ## Soft constraint evaluation

    Instead of "does this assignment satisfy the formula?" compute
    "how many clauses does this assignment satisfy?" -/

/-- Count how many clauses are satisfied by an assignment. -/
def satisfactionCount (assign : List (ℕ × Bool))
    (formula : SATFormula) : ℕ :=
  formula.foldl (fun count clause =>
    if satisfiesClause assign clause then count + 1 else count) 0

/-- Weight of an assignment: 1 if all clauses satisfied, 0 otherwise.
    For BP, we use hard constraints (all-or-nothing) but propagate
    counts of satisfying assignments rather than single examples. -/
def assignmentWeight (assign : List (ℕ × Bool))
    (formula : SATFormula) : ℕ :=
  if satisfiesFormula assign formula then 1 else 0

/-! ## Marginal distributions

    For each variable, compute the marginal:
    P(x=T) ∝ number of satisfying assignments with x=T
    P(x=F) ∝ number of satisfying assignments with x=F

    We represent marginals as (count_true, count_false) pairs.
    The ratio gives the probability. -/

/-- Marginal for one variable: (count with true, count with false). -/
abbrev Marginal := ℕ × ℕ

/-- Compute marginals for a set of variables by enumeration.
    For each variable, count how many satisfying assignments have
    it true vs false. -/
def computeMarginals (formula : SATFormula) (vars : List ℕ)
    : List (ℕ × Marginal) :=
  let allAssigns := allVarAssignments vars
  vars.map fun v =>
    let countTrue := allAssigns.foldl (fun count assign =>
      let withV := assign.any fun (v', p) => v' == v && p == true
      if withV && satisfiesFormula assign (clausesInScope formula vars)
      then count + 1 else count) 0
    let countFalse := allAssigns.foldl (fun count assign =>
      let withV := assign.any fun (v', p) => v' == v && p == false
      if withV && satisfiesFormula assign (clausesInScope formula vars)
      then count + 1 else count) 0
    (v, (countTrue, countFalse))

/-! ## BP-style message passing

    Each cluster computes marginals for its variables.
    Messages between clusters are the marginals of shared variables.
    Incoming marginals bias the local computation.

    Instead of "x3 must be T" (hard), the message says
    "x3 is T in 7 out of 10 configurations" (soft). -/

/-- A soft message: marginals for variables relevant to a coupling. -/
structure SoftMessage where
  from_ : ℕ
  to_ : ℕ
  marginals : List (ℕ × Marginal)
  deriving Repr

/-- Compute marginals for a cluster, biased by incoming soft messages.
    Incoming marginals act as priors: assignments consistent with
    high-probability values are weighted more heavily. -/
def computeClusterMarginals (cluster : Cluster)
    (incoming : List SoftMessage)
    : List (ℕ × Marginal) × ℕ :=
  -- Collect incoming marginals as bias
  let bias := incoming.flatMap (·.marginals)
  -- Enumerate all assignments for cluster variables
  let allAssigns := allVarAssignments cluster.vars
  -- Weight each assignment by: satisfies local clauses × consistent with bias
  let weighted := allAssigns.filterMap fun assign =>
    if satisfiesFormula assign cluster.localClauses then
      -- Compute bias weight: product of marginal ratios for biased vars
      let biasWeight := bias.foldl (fun w (v, (ct, cf)) =>
        let total := ct + cf
        if total == 0 then w
        else
          match assign.find? fun (v', _) => v' == v with
          | some (_, true) => w * (ct + 1)   -- +1 smoothing
          | some (_, false) => w * (cf + 1)
          | none => w
      ) 1
      some (assign, biasWeight)
    else none
  -- Compute marginals from weighted assignments
  let marginals := cluster.vars.map fun v =>
    let countTrue := weighted.foldl (fun count (assign, w) =>
      if assign.any fun (v', p) => v' == v && p == true
      then count + w else count) 0
    let countFalse := weighted.foldl (fun count (assign, w) =>
      if assign.any fun (v', p) => v' == v && p == false
      then count + w else count) 0
    (v, (countTrue, countFalse))
  (marginals, weighted.length)

/-- Compute soft message from cluster marginals to a coupling. -/
def computeSoftMessage (marginals : List (ℕ × Marginal))
    (coupling : Coupling) (fromCluster : ℕ) : SoftMessage :=
  let toCluster := if coupling.cluster1 == fromCluster
    then coupling.cluster2 else coupling.cluster1
  let relevantVars := (coupling.crossClauses.flatMap fun clause =>
    clause.map fun (v, _) => v).eraseDups
  let relevant := marginals.filter fun (v, _) =>
    relevantVars.contains v
  { from_ := fromCluster, to_ := toCluster, marginals := relevant }

/-! ## BP iteration -/

/-- One round of belief propagation. -/
def bpRound (clusters : List Cluster)
    (couplings : List Coupling)
    (prevMessages : List SoftMessage)
    : List (List (ℕ × Marginal)) × List SoftMessage × ℕ :=
  let allMarginals := clusters.map fun cluster =>
    let incoming := prevMessages.filter fun m => m.to_ == cluster.id
    let (marginals, _) := computeClusterMarginals cluster incoming
    marginals
  let messages := couplings.flatMap fun coupling =>
    let m1 := allMarginals.getD coupling.cluster1 []
    let m2 := allMarginals.getD coupling.cluster2 []
    [computeSoftMessage m1 coupling coupling.cluster1,
     computeSoftMessage m2 coupling coupling.cluster2]
  (allMarginals, messages, clusters.length)

/-- Check if BP marginals have converged. -/
def marginalsConverged (prev curr : List (List (ℕ × Marginal)))
    : Bool :=
  if prev.length != curr.length then false
  else (prev.zip curr).all fun (pCluster, cCluster) =>
    (pCluster.zip cCluster).all fun ((_, (pt, pf)), (_, (ct, cf))) =>
      -- Check if the "winner" (T or F) is the same
      (pt > pf) == (ct > cf)

/-- Read off assignment from converged marginals. -/
def readAssignment (marginals : List (List (ℕ × Marginal)))
    : List (ℕ × Bool) :=
  marginals.flatMap fun cluster =>
    cluster.map fun (v, (ct, cf)) => (v, ct > cf)

/-- Run BP for up to maxIter rounds. -/
def runBP (formula : SATFormula) (n : ℕ)
    (nClusters : ℕ) (maxIter : ℕ := 20)
    : Option (List (ℕ × Bool)) × ℕ × ℕ :=
  let (clusters, couplings) := decompose formula n nClusters
  let rec iterate (messages : List SoftMessage)
      (prevMarginals : List (List (ℕ × Marginal)))
      (iter cost : ℕ)
      : Option (List (ℕ × Bool)) × ℕ × ℕ :=
    if iter ≥ maxIter then
      -- Max iterations: read off best guess
      let assign := readAssignment prevMarginals
      let valid := satisfiesFormula assign formula
      (if valid then some assign else none, cost, iter)
    else
      let (marginals, newMessages, roundCost) :=
        bpRound clusters couplings messages
      let totalCost := cost + roundCost
      if marginalsConverged prevMarginals marginals then
        -- Converged: read off assignment
        let assign := readAssignment marginals
        let valid := satisfiesFormula assign formula
        (if valid then some assign else none, totalCost, iter + 1)
      else
        iterate newMessages marginals (iter + 1) totalCost
  iterate [] [] 0 0

/-! ## Comparison: all paradigms -/

-- Random 3-SAT n=8
#eval do
  let n := 8
  let m := 32
  let data := [42, 123, 456].map fun seed =>
    let f := random3SAT n m seed
    let (_, flat) := flatBruteForce f n
    let (_, cdcl, _) := satCDCL f n
    let (r2, bp2Cost, bp2Iter) := runBP f n 2
    let (r4, bp4Cost, bp4Iter) := runBP f n 4
    s!"seed={seed} flat={flat} cdcl={cdcl} bp2={bp2Cost}(i={bp2Iter},f={r2.isSome}) bp4={bp4Cost}(i={bp4Iter},f={r4.isSome})"
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
    let (_, cdcl, _) := satCDCL f n
    let (r, bpCost, bpIter) := runBP f n 2
    let (r5, bp5Cost, bp5Iter) := runBP f n 5
    s!"seed={seed} flat={flat} ch+md={chmd} cdcl={cdcl} bp2={bpCost}(i={bpIter},f={r.isSome}) bp5={bp5Cost}(i={bp5Iter},f={r5.isSome})"
  IO.println s!"Random n={n} m={m}:"
  IO.println (String.intercalate "\n" data)

-- Structured
#eval do
  let data := [8, 10, 12].map fun n =>
    let f := reachInstance n 3
    let (_, smart) := satSmartDAG f n 2
    let (_, cdcl, _) := satCDCL f n
    let (r, bpCost, bpIter) := runBP f n 2
    s!"n={n} smart={smart} cdcl={cdcl} bp2={bpCost}(i={bpIter},f={r.isSome})"
  IO.println s!"Structured reach=3:"
  IO.println (String.intercalate "\n" data)

-- PHP (UNSAT)
#eval do
  let f := pigeonhole 3 2
  let (_, cdcl, _) := satCDCL f 6
  let (r, bpCost, bpIter) := runBP f 6 2
  IO.println s!"PHP(3,2): cdcl={cdcl} bp2={bpCost}(i={bpIter},f={r.isSome})"

/-! ## Assessment

    Belief propagation sends SOFT messages (marginal distributions)
    instead of hard assignments. This allows clusters to negotiate
    probabilistically: "I slightly prefer x3=T" rather than
    "x3 MUST be T."

    Expected improvements over hard message passing:
    - Convergence to CORRECT states (marginals reflect true distribution)
    - Handles disagreement gracefully (probabilities average out)
    - The assignment read from marginals is the "most likely" solution

    Known limitations of BP (replica-symmetric):
    - Fails above the clustering transition (solution space shatters)
    - Can oscillate on loopy graphs (our factor graph has loops)
    - The marginals may not correspond to any actual solution
      (even if each variable's most likely value is correct,
      the combination might not satisfy all clauses)

    To go beyond BP:
    - Survey propagation (1RSB): send distributions OVER marginals
    - This accounts for the cluster structure that BP misses
    - But SP is significantly more complex to implement

    The hierarchy:
    | Method | Messages | Accounts for |
    |--------|----------|-------------|
    | Hard MP | single assignment | nothing |
    | BP (RS) | marginal distribution | variable correlations |
    | SP (1RSB) | distribution over marginals | cluster structure |
    | Full RSB | hierarchy of distributions | all correlations | -/

end RotationCalculus
