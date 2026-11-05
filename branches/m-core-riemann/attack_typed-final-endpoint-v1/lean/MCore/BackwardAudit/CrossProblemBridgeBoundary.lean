import MCore.BackwardAudit.EndpointTypeResidue

namespace MCore
namespace BackwardAudit

/-- Abstract cross-problem specification. RH now has a typed endpoint interface. Cross-problem claims are still bridge
obligations unless an explicit implication is independently supplied. -/
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

/-- Endpoint typing is closed, but no RH-to-complexity implication is created
by typing alone. -/
theorem cross_problem_endpoint_is_typed :
    endpointPropositionTyped = true :=
  endpoint_proposition_is_typed

#print axioms rh_to_pnp_equality_if_bridge_supplied
#print axioms rh_to_pnp_separation_if_bridge_supplied
#print axioms rh_to_factoring_if_bridge_supplied
#print axioms twisted_zeta_to_separation_if_bridge_supplied
#print axioms cross_problem_endpoint_is_typed

end BackwardAudit
end MCore
