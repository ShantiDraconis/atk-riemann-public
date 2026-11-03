import MCore.RH.R0.DiscoveryCertificates
import MCore.RH.R0.ExponentialUniqueness
import MCore.RH.R0.LinearIndependentReduction
import MCore.RH.Experimental.GeometryClassification
import Lean

open Lean Elab Tactic

namespace MCore.RH.ForcedAll

open MCore.RH.R0
open MCore.RH.NB
open MCore.RH.Experimental

inductive RHGap
| A1_0_LpToAE
| A1_1_WeightedIntegrable
| A1_2_Linearity
| A1_3_Scaling
| A1_4_BasePositive
| A2_Vandermonde
| A3_LinearIndependent
| B1_PosDef
| B2_InverseFormula
| B3_DetNonzero
| C_TargetIntegral
| C_GramIntegral
| C_TargetGamma
| C_GramArithmetic
| D_MellinRho
| D_MellinChi
| D_Plancherel
| E_RawNear
| E_RawTail
| E_CorrectWitness
| F_Spectral
| G_Square
| G_Cube
| G_Sphere
| G_Cylinder
| G_Cone
| G_DoubleCone
| G_TripleCone
| G_Torus
| G_Custom
| H_GramRate
| H_Uniform
| H_Terminal
deriving Repr

elab "vomit_gap " name:str : tactic => do
  let g ← getMainGoal
  let fmt ← g.withContext do ppGoal g
  let body := toString fmt
  logInfo m!"[RH-FORCED:{name.getString}]\n{body}"
  IO.FS.writeFile s!"/tmp/rh_forced_{name.getString}.txt" body

/-- Registry entry: statement plus optional explicit proof/refutation supplied by later files. -/
structure GapContract where
  id : RHGap
  statement : Prop

def gapContracts : List GapContract :=
  [ ⟨.A2_Vandermonde, ∀ N : ℕ, ConcreteMomentUniqueness N⟩
  , ⟨.A3_LinearIndependent, ∀ N : ℕ, LinearIndependent ℝ (fun i : Fin N => concreteGeneratorFamily i)⟩
  , ⟨.B1_PosDef, ∀ N : ℕ, (concreteGramMatrix N).PosDef⟩
  , ⟨.H_Uniform, ConcreteUniformLogDNBound⟩
  , ⟨.H_Terminal, RiemannTerminalCertifies⟩
  ]

/-- A2 should eventually be promoted from SOURCE_READY only after kernel build succeeds. -/
theorem DISCOVER_A2_ALL : ∀ N : ℕ, ConcreteMomentUniqueness N := by
  intro N
  exact concreteMomentUniqueness_vandermonde N

/-- A3 remains conditional until A1 is inhabited. -/
theorem DISCOVER_A3_FROM_A1
    (hA1 : ∀ N : ℕ, ConcreteMomentBridge N) :
    ∀ N : ℕ, LinearIndependent ℝ (fun i : Fin N => concreteGeneratorFamily i) := by
  intro N
  exact concreteGeneratorFamily_linearIndependent_of_moments N (hA1 N)
    (concreteMomentUniqueness_vandermonde N)

/-- Final material question, left intentionally RED. -/
theorem DISCOVER_H1 : Nonempty LogRateCertificate := by
  vomit_gap "H1_LOG_RATE_CERTIFICATE"
  exact ?_

/-- Explicit witness outcome, also intentionally RED. -/
theorem DISCOVER_E1_OUTCOME (ρ : ℂ) :
    ExplicitOutcome (Nonempty (E1WitnessCertificate ρ)) := by
  vomit_gap "E1_EXPLICIT_OUTCOME"
  exact ?_

/-- Geometry must supply a real audited certificate; labels alone do not count. -/
theorem DISCOVER_GEOMETRY (G : GeometryAnsatz) :
    ExplicitOutcome (Nonempty (AuditedGeometryCertificate G)) := by
  vomit_gap "GEOMETRY_EXPLICIT_OUTCOME"
  exact ?_

end MCore.RH.ForcedAll
