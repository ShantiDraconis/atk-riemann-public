import MCore.K0

namespace MCore.RH

/-- Kernel-portable semantic interface for the classical RH endpoint. -/
structure EndpointSemantics where
  Point : Type
  NontrivialZero : Point → Prop
  CriticalLine : Point → Prop

/-- Every nontrivial zeta zero lies on the critical line.
    This is a proposition only; no truth value is asserted. -/
def FinalEndpoint (S : EndpointSemantics) : Prop :=
  ∀ s : S.Point, S.NontrivialZero s → S.CriticalLine s

/-- Adapter obligation connecting the kernel-portable endpoint to a concrete
    implementation of the analytically continued zeta function. -/
structure ClassicalZetaAdapter (S : EndpointSemantics) where
  ConcretePoint : Type
  embed : ConcretePoint → S.Point
  isClassicalNontrivialZero : ConcretePoint → Prop
  isClassicalCriticalLine : ConcretePoint → Prop
  zero_match : ∀ s, isClassicalNontrivialZero s ↔ S.NontrivialZero (embed s)
  line_match : ∀ s, isClassicalCriticalLine s ↔ S.CriticalLine (embed s)

theorem endpoint_transport
    (S : EndpointSemantics)
    (A : ClassicalZetaAdapter S)
    (h : FinalEndpoint S) :
    ∀ s : A.ConcretePoint,
      A.isClassicalNontrivialZero s → A.isClassicalCriticalLine s := by
  intro s hs
  apply (A.line_match s).2
  exact h (A.embed s) ((A.zero_match s).1 hs)

#print axioms endpoint_transport

end MCore.RH
