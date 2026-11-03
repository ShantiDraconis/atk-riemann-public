import MCore.RH.R0.HardFrontierReduction
import MCore.RH.R0.GramExplicit
import MCore.RH.R0.ConcreteZeroObstruction
import MCore.RH.Experimental.GeometryAnsatz

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.Experimental

/-- Exact quantitative certificate for the inverse-Gram frontier. -/
structure LogRateCertificate where
  K : ℝ
  hK : 0 ≤ K
  bound : ∀ N : ℕ,
    1 - dotProduct (concreteTargetVector N)
      ((concreteGramMatrix N)⁻¹ *ᵥ concreteTargetVector N)
      ≤ logMajorant K N

/-- Explicit orthogonal witness package in the frozen L2(0,infinity) carrier. -/
structure E1WitnessCertificate (ρ : ℂ) where
  w : concreteNBData.H
  nonzero : w ≠ 0
  zeroHyp : riemannZeta ρ = 0
  generatorOrthogonal :
    ∀ n : ℕ, inner ℝ (concreteGeneratorFamily n) w = 0
  targetPairingNonzero :
    inner ℝ concreteNBData.chi w ≠ 0

/-- A certificate can only use a geometry through actual coefficients and a log-rate bound. -/
structure AuditedGeometryCertificate (G : GeometryAnsatz) extends GeometryLogCertificate G where
  normalResidual : ∀ N : ℕ,
    G.gramResidual N (param N) = 0

/-- Explicit outcome, requiring a real inhabitant on one side. No Decidable shortcut. -/
inductive ExplicitOutcome (P : Prop) : Type
| proved : P → ExplicitOutcome P
| refuted : (¬ P) → ExplicitOutcome P

/-- A witness package immediately gives the concrete obstruction already proved in MCore. -/
theorem E1WitnessCertificate.refutesUniformLogDN
    {ρ : ℂ} (h : E1WitnessCertificate ρ) :
    ¬ ConcreteUniformLogDNBound := by
  exact no_ConcreteUniformLogDNBound_of_orthogonal_witness
    h.w h.nonzero h.targetPairingNonzero h.generatorOrthogonal

#print axioms MCore.RH.R0.E1WitnessCertificate.refutesUniformLogDN

end MCore.RH.R0
