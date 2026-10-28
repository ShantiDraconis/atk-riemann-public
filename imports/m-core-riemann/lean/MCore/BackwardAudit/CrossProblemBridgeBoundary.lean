import MCore.BackwardAudit.EndpointTypeResidue

namespace MCore
namespace BackwardAudit

/-- Abstract cross-problem specification. The current RH repository has not yet
typed the classical RH endpoint proposition, so these are bridge obligations,
not established implications. -/
structure CrossProblemBridgeSpec where
  rh : Prop
  pnpDiscriminant : Prop
  factoringPolynomialTime : Prop
  twistedZetaOffCritical : Prop

def RHToPNPEqualityBridge (S : CrossProblemBridgeSpec) : Prop :=
  S.rh → S.pnpDiscriminant

def RHToPNPSeparationBridge (S : CrossProblemBridgeSpec) : Prop :=
  S.rh → ¬ S.pnpDiscriminant

def RHToFactoringBridge (S : CrossProblemBridgeSpec) : Prop :=
  S.rh → S.factoringPolynomialTime

def TwistedZetaToPNPSeparationBridge
    (S : CrossProblemBridgeSpec) : Prop :=
  S.twistedZetaOffCritical → ¬ S.pnpDiscriminant

theorem rh_to_pnp_equality_if_bridge_supplied
    (S : CrossProblemBridgeSpec)
    (hBridge : RHToPNPEqualityBridge S)
    (hRH : S.rh) :
    S.pnpDiscriminant :=
  hBridge hRH

theorem rh_to_pnp_separation_if_bridge_supplied
    (S : CrossProblemBridgeSpec)
    (hBridge : RHToPNPSeparationBridge S)
    (hRH : S.rh) :
    ¬ S.pnpDiscriminant :=
  hBridge hRH

theorem rh_to_factoring_if_bridge_supplied
    (S : CrossProblemBridgeSpec)
    (hBridge : RHToFactoringBridge S)
    (hRH : S.rh) :
    S.factoringPolynomialTime :=
  hBridge hRH

theorem twisted_zeta_to_separation_if_bridge_supplied
    (S : CrossProblemBridgeSpec)
    (hBridge : TwistedZetaToPNPSeparationBridge S)
    (hOff : S.twistedZetaOffCritical) :
    ¬ S.pnpDiscriminant :=
  hBridge hOff

/-- The current repository state itself remains untyped at the classical RH
endpoint. This theorem records that no cross-problem bridge may be promoted
before the endpoint proposition is first typed. -/
theorem cross_problem_endpoint_still_untyped :
    endpointPropositionTyped = false :=
  endpoint_proposition_still_untyped

#print axioms rh_to_pnp_equality_if_bridge_supplied
#print axioms rh_to_pnp_separation_if_bridge_supplied
#print axioms rh_to_factoring_if_bridge_supplied
#print axioms twisted_zeta_to_separation_if_bridge_supplied
#print axioms cross_problem_endpoint_still_untyped

end BackwardAudit
end MCore
