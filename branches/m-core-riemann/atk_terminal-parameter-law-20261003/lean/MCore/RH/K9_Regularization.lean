import MCore.A14_Formal

namespace MCore

/-- A regularized system is a new object, not an assertion that path dependence vanished. -/
structure RegularizedMCoreSystem where
  source : MCoreSystem
  regularizedLimit : ZeroDirection → ℝ
  scaleRegularized : ℝ → ℝ
  selfRefEliminated : Prop

/-- The regularized limits are path-independent.  A value of this structure is a proof
certificate for the A3 inversion; defining the structure does not construct one. -/
structure PathIndependenceCertificate (reg : RegularizedMCoreSystem) : Prop where
  commonLimit : ℝ
  K0_eq : reg.regularizedLimit .K0 = commonLimit
  RHO_eq : reg.regularizedLimit .RHO = commonLimit
  ETA_eq : reg.regularizedLimit .ETA = commonLimit

/-- Regularization must preserve the scale information used downstream. -/
structure ScalePreservationCertificate (reg : RegularizedMCoreSystem) : Prop where
  scale_eq : ∀ λ : ℝ, 0 < λ → reg.scaleRegularized λ = reg.source.baseVal

/-- A2 detects a cycle.  Closing the firewall requires a separate proof that the
regularized object no longer uses that circular dependency. -/
structure SelfReferenceEliminationCertificate (reg : RegularizedMCoreSystem) : Prop where
  eliminated : reg.selfRefEliminated

/-- Complete regularization certificate.  This is intentionally uninhabited until the
three mathematical obligations are proved. -/
structure RegularizationCertificate (reg : RegularizedMCoreSystem) : Prop where
  pathIndependent : PathIndependenceCertificate reg
  scalePreserved : ScalePreservationCertificate reg
  selfReferenceRemoved : SelfReferenceEliminationCertificate reg

end MCore
