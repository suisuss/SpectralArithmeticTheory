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
