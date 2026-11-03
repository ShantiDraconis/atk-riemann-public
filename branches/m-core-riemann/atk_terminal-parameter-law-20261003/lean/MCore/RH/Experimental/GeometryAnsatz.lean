import MCore.RH.R0.HardFrontierReduction
import MCore.RH.R0.GramExplicit

namespace MCore.RH.Experimental

open MCore.RH.NB
open MCore.RH.R0

structure GeometryAnsatz where
  Param : Type
  coeff : (N : ℕ) → Param → Fin N → ℝ

noncomputable def GeometryAnsatz.errorSq
    (G : GeometryAnsatz) (N : ℕ) (p : G.Param) : ℝ :=
  ‖concreteNBData.chi -
    concreteNBData.coefficientApproximantAt
      concreteGeneratorFamily N (G.coeff N p)‖ ^ 2

structure GeometryLogCertificate (G : GeometryAnsatz) where
  K : ℝ
  hK : 0 ≤ K
  param : (N : ℕ) → G.Param
  error_le :
    ∀ N : ℕ, G.errorSq N (param N) ≤ logMajorant K N

theorem GeometryLogCertificate.toUniformLogDNBound
    {G : GeometryAnsatz} (h : GeometryLogCertificate G) :
    ConcreteUniformLogDNBound := by
  refine ⟨h.K, h.hK, ?_⟩
  intro N
  exact le_trans
    (concreteNBData.DN_le_coefficient_error_sq
      concreteGeneratorFamily N (G.coeff N (h.param N)))
    (h.error_le N)

noncomputable def GeometryAnsatz.gramResidual
    (G : GeometryAnsatz) (N : ℕ) (p : G.Param) : Fin N → ℝ :=
  concreteGramMatrix N *ᵥ G.coeff N p - concreteTargetVector N

def GeometryNormalCompatible (G : GeometryAnsatz) : Prop :=
  ∀ N : ℕ, ∃ p : G.Param, G.gramResidual N p = 0

structure GeometryDescriptor where
  label : String
  dimension : ℕ

def squareDescriptor : GeometryDescriptor := ⟨"square", 2⟩
def cubeDescriptor : GeometryDescriptor := ⟨"cube", 3⟩
def sphereDescriptor : GeometryDescriptor := ⟨"sphere", 2⟩
def cylinderDescriptor : GeometryDescriptor := ⟨"cylinder", 2⟩
def coneDescriptor : GeometryDescriptor := ⟨"cone", 2⟩
def doubleConeDescriptor : GeometryDescriptor := ⟨"double_cone", 2⟩
def tripleConeDescriptor : GeometryDescriptor := ⟨"triple_cone", 2⟩
def torusDescriptor : GeometryDescriptor := ⟨"torus", 2⟩

#print axioms MCore.RH.Experimental.GeometryLogCertificate.toUniformLogDNBound

end MCore.RH.Experimental
