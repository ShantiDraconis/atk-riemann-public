import MCore.A14_Formal
import MCore.RH.K09_Continuation
import MCore.RH.K9_Regularization
import MCore.RH.K9_ZetaBridge
import MCore.RH.K9_RigidityRoutes
import MCore.RH.K9_CriterionRoutes
import MCore.RH.K9_RiemannHypothesis

namespace MCore

/-- K9 research umbrella.  Importing this file does not construct `MCoreRHCertificate`
and therefore does not promote the RH endpoint. -/
theorem k9_preserves_k8_firewall :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k8_preserves_k7_firewall

end MCore
