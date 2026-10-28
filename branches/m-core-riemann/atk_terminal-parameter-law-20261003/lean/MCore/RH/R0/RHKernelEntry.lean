import MCore.RH.R0.ConcreteInhabitantKernelAudit
import MCore.RH.R0.ConcreteLogMajorantProducer
import MCore.RH.R0.HardFrontier
import MCore.RH.R0.FinalKernelComposition

namespace MCore.RH.R0

/--
Single kernel entrypoint for the RH terminal producer chain.
This file is intentionally consumer-only: it proves that one concrete
VanishingUpperBound inhabits every already-certified downstream endpoint.
-/
theorem rh_kernel_entry_FINAL_ROOT
    (h : ConcreteVanishingUpperBound) :
    MCore.RH.NB.Final.FINAL_ROOT concreteNBData concreteGeneratorFamily :=
  kernel_path_FINAL_ROOT h

theorem rh_kernel_entry_GramResidual
    (h : ConcreteVanishingUpperBound) :
    ConcreteGramResidual :=
  concreteVanishingUpperBound_to_ConcreteGramResidual h

theorem rh_kernel_entry_FiniteSpan
    (h : ConcreteVanishingUpperBound) :
    concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily :=
  concreteVanishingUpperBound_to_FiniteSpanApproximatesChi h

theorem rh_kernel_entry_Terminal
    (h : ConcreteVanishingUpperBound) :
    RiemannTerminalCertifies :=
  kernel_path_terminal h

#print axioms MCore.RH.R0.rh_kernel_entry_FINAL_ROOT
#print axioms MCore.RH.R0.rh_kernel_entry_GramResidual
#print axioms MCore.RH.R0.rh_kernel_entry_FiniteSpan
theorem rh_kernel_entry_LogMajorantTerminal
    (h : ConcreteLogDNBound) :
    RiemannTerminalCertifies :=
  concreteLogDNBound_to_RiemannTerminalCertifies h

#print axioms MCore.RH.R0.rh_kernel_entry_Terminal
theorem rh_kernel_entry_HardFrontier
    (h : ConcreteUniformLogDNBound) :
    RiemannTerminalCertifies :=
  terminal_of_concreteUniformLogDNBound h

#print axioms MCore.RH.R0.rh_kernel_entry_LogMajorantTerminal
theorem rh_kernel_entry_MaterialProducer
    (h : RHMaterialProducer) :
    RiemannTerminalCertifies :=
  rh_material_producer_closes_terminal h

#print axioms MCore.RH.R0.rh_kernel_entry_HardFrontier
#print axioms MCore.RH.R0.rh_kernel_entry_MaterialProducer

end MCore.RH.R0
