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
