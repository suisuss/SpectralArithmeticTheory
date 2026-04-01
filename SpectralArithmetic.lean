-- Core axiom tower
import SpectralArithmetic.Core.Basic
import SpectralArithmetic.Core.Semiring
import SpectralArithmetic.Core.IntegralDomain
import SpectralArithmetic.Core.Rational
import SpectralArithmetic.Core.Complete
import SpectralArithmetic.Core.Complex
-- Verification
import SpectralArithmetic.Verification.PeanoTest
import SpectralArithmetic.Verification.ZFTest
import SpectralArithmetic.Verification.Model
import SpectralArithmetic.Verification.Countermodels
-- Encoding obstruction
import SpectralArithmetic.Obstruction.Encoding
import SpectralArithmetic.Obstruction.Pairing
import SpectralArithmetic.Obstruction.Oplus
import SpectralArithmetic.Obstruction.Main
-- Convergence conjecture (open)
import SpectralArithmetic.Obstruction.Convergence
-- Complexity asymmetry (P vs NP structural analogy)
import SpectralArithmetic.Obstruction.Complexity
-- SAT encoding as term structure
import SpectralArithmetic.Obstruction.SAT
-- deepRewrite cost bounds
import SpectralArithmetic.Obstruction.CostBounds
-- Variable sharing and normalization cost
import SpectralArithmetic.Obstruction.VarSharing
-- JIT obs placement pipeline
import SpectralArithmetic.Obstruction.JIT
-- Coupled case analysis and constraint graphs
import SpectralArithmetic.Obstruction.CoupledAnalysis
-- NAND encoding via circuit terms (proper CNF = AND-of-ORs)
import SpectralArithmetic.Obstruction.NANDEncoding
-- Lambda calculus embedding (SK combinators → DynSemiring)
import SpectralArithmetic.Lambda.Combinator
import SpectralArithmetic.Lambda.Embedding
-- Boolean expression ADT with eager/lazy evaluation strategies
import SpectralArithmetic.Lambda.Expr
-- Untyped S-expression rewriting (stripped ADT)
import SpectralArithmetic.Lambda.UntypedExpr
-- BCKW combinatory logic (second Turing-complete basis)
import SpectralArithmetic.Lambda.BCKW
-- Polynomial arithmetization (commutative algebra test)
import SpectralArithmetic.Lambda.Poly
-- Rotation calculus (formal language for complexity)
import SpectralArithmetic.Rotation.Syntax
import SpectralArithmetic.Rotation.Rewrite
import SpectralArithmetic.Rotation.Constraint
import SpectralArithmetic.Rotation.Complexity
import SpectralArithmetic.Rotation.Examples
-- CSP equivalence investigation (falsification test)
import SpectralArithmetic.Rotation.CSPEquivalence
-- Generator fixed-point analysis (Direction 3 equivalence test)
import SpectralArithmetic.Rotation.GeneratorFixedPoint
-- Tree arrangements (Catalan space investigation)
import SpectralArithmetic.Rotation.TreeArrangement
-- Tree complexity hierarchy (level-by-level analysis)
import SpectralArithmetic.Rotation.TreeComplexity
-- Asymmetric information flow investigation
import SpectralArithmetic.Rotation.TreeFlow
-- Constraint factorization (treewidth connection)
import SpectralArithmetic.Rotation.Factorization
-- Checking vs constructing (catamorphism vs anamorphism)
import SpectralArithmetic.Rotation.Construction
-- Gap analysis (measuring P vs NP)
import SpectralArithmetic.Rotation.GapAnalysis
-- SAT encoding via tree arrangements
import SpectralArithmetic.Rotation.SATEncoding
-- DAG arrangements (shared subtrees, memoization)
import SpectralArithmetic.Rotation.DAG
-- Choice constructor (AND-OR trees, alternation)
import SpectralArithmetic.Rotation.Choice
-- Scaling comparison across treewidths
import SpectralArithmetic.Rotation.Scaling
-- Bounded DAG (treewidth-parameterized solver)
import SpectralArithmetic.Rotation.DAGBounded
-- Random 3-SAT generality test
import SpectralArithmetic.Rotation.Random3SAT
-- Graph-aware variable ordering (#12)
import SpectralArithmetic.Rotation.GraphOrder
-- Choice-based SAT via AND-OR trees (#13)
import SpectralArithmetic.Rotation.ChoiceSAT
-- Hybrid solver: SmartDAG + Choice
import SpectralArithmetic.Rotation.HybridSolver
-- Adaptive solver: evaluate then select
import SpectralArithmetic.Rotation.AdaptiveSolver
-- Clause learning / CDCL (general resolution)
import SpectralArithmetic.Rotation.ClauseLearning
-- Message passing (coupled trees, belief propagation)
import SpectralArithmetic.Rotation.MessagePassing
-- Belief propagation (soft constraints, marginals)
import SpectralArithmetic.Rotation.BeliefProp
-- Extended resolution (abstraction, proof compression)
import SpectralArithmetic.Rotation.ExtendedResolution
-- Formal proofs of soundness (#19)
import SpectralArithmetic.Rotation.FormalProofs
-- Composition theory (#22)
import SpectralArithmetic.Rotation.CompositionTheory
-- Phase transition study (#23)
import SpectralArithmetic.Rotation.PhaseTransition
-- Real pipeline: traced tactics through shared state
import SpectralArithmetic.Rotation.Pipeline
-- Trajectory analysis: meta-rewriting feasibility test
import SpectralArithmetic.Rotation.TrajectoryAnalysis
-- Trajectory analysis: large-scale test
import SpectralArithmetic.Rotation.TrajectoryLargeScale
-- Rotation rule index: all possible rules and their structures
import SpectralArithmetic.Rotation.RotationIndex
-- Self-contained rotation calculus (A: rule selection, C: constraint as term)
import SpectralArithmetic.Rotation.SelfContained
-- Meta-rewriting #0: rotation calculus as rewriting system
import SpectralArithmetic.Rotation.MetaRewrite0
-- UNSAT proofs in the rotation calculus
import SpectralArithmetic.Rotation.UNSATProof
-- Resolution as contraction in the rotation calculus
import SpectralArithmetic.Rotation.Resolution
-- Resolution contraction: subsumption, UP bridge, extended resolution
import SpectralArithmetic.Rotation.ResolutionContraction
-- Resolution strategy as term (head-tape unification)
import SpectralArithmetic.Rotation.StrategyAsTerm
-- Constraint evolution (learned clauses as living constraints)
import SpectralArithmetic.Rotation.ConstraintEvolution
-- Symmetry breaking (orbit detection, breaking constraints, pruning)
import SpectralArithmetic.Rotation.SymmetryBreaking
-- Craig interpolation (UNSAT proof factorization)
import SpectralArithmetic.Rotation.Interpolation
-- Proof compression (dead steps, deduplication, subsumption collapse)
import SpectralArithmetic.Rotation.ProofCompression
-- Width trajectories and proof system classification
import SpectralArithmetic.Rotation.WidthTrajectory
-- Fast resolution (variable-indexed clause database)
import SpectralArithmetic.Rotation.FastResolution
-- Proof system test: strategy independence
import SpectralArithmetic.Rotation.ProofSystemTest
-- Adaptive meta-solver: monolithic/composed hybrid
import SpectralArithmetic.Rotation.AdaptiveMetaSolver
-- Tactic selector: meta-guided strategy dispatch
import SpectralArithmetic.Rotation.TacticSelector
-- Width-guided solver: phase-aware resolution with BP and interpolation
import SpectralArithmetic.Rotation.WidthGuidedSolver
-- Chain analysis: do random UNSAT instances have single-chain proofs?
import SpectralArithmetic.Rotation.ChainAnalysis
-- CDCL with 1-UIP conflict analysis
import SpectralArithmetic.Rotation.CDCL1UIP
-- Iterated 1-UIP: learn → augment → cascade → repeat
import SpectralArithmetic.Rotation.IteratedCDCL
-- Crawl-Contract: signal-driven inprocessing
import SpectralArithmetic.Rotation.CrawlContract
-- Transition prediction: can we detect the phase jump early?
import SpectralArithmetic.Rotation.TransitionPredictor
-- Industrial-like modular instances
import SpectralArithmetic.Rotation.IndustrialInstances
-- Promotion-aware learning
import SpectralArithmetic.Rotation.PromotionAware
-- Scaling test
import SpectralArithmetic.Rotation.ScalingTest
-- Meta-rewriting #1: constraint evolution with complexity trajectories
import SpectralArithmetic.Rotation.MetaRewriting
-- Interleaved representation: verification = construction
import SpectralArithmetic.Rotation.InterRepresentation
