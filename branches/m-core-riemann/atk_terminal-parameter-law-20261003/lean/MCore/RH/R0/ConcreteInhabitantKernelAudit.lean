import MCore.RH.R0.ConcreteVanishingProducer

namespace MCore.RH.R0

/--
Kernel audit bundle for the RH terminal composition.

This object deliberately does not contain an inhabitant.  It certifies that
all downstream maps are already present and that the only remaining datum is
the concrete quantitative producer itself.
-/
structure ConcreteInhabitantKernelAudit where
  producerType : Type
  terminalType : Prop
  gramType : Prop
  finiteSpanType : Prop

def concreteInhabitantKernelAudit : ConcreteInhabitantKernelAudit where
  producerType := ConcreteVanishingUpperBound
  terminalType := RiemannTerminalCertifies
  gramType := ConcreteGramResidual
  finiteSpanType :=
    concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily

theorem kernel_path_FINAL_ROOT
    (h : ConcreteVanishingUpperBound) :
    MCore.RH.NB.Final.FINAL_ROOT concreteNBData concreteGeneratorFamily :=
  concreteVanishingUpperBound_to_FINAL_ROOT h

theorem kernel_path_terminal
    (h : ConcreteVanishingUpperBound) :
    RiemannTerminalCertifies :=
  concreteVanishingUpperBound_to_RiemannTerminalCertifies h

#print axioms MCore.RH.R0.kernel_path_FINAL_ROOT
#print axioms MCore.RH.R0.kernel_path_terminal

end MCore.RH.R0
