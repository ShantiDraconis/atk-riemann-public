import MCore.RH.R0.ConcreteGramClosure

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

def RiemannTerminalCertifies : Prop :=
  FINAL_ROOT concreteNBData concreteGeneratorFamily

def RiemannTerminalRefutes : Prop :=
  concreteNBData.DNLimit concreteGeneratorFamily ≠ 0

theorem riemannTerminalCertifies_iff_zero :
    RiemannTerminalCertifies ↔
      concreteNBData.DNLimit concreteGeneratorFamily = 0 := by
  rfl

theorem not_riemannTerminalCertifies_iff_refutes :
    ¬ RiemannTerminalCertifies ↔ RiemannTerminalRefutes := by
  rfl

theorem riemann_terminal_cert_refute_disjoint :
    ¬ (RiemannTerminalCertifies ∧ RiemannTerminalRefutes) := by
  rintro ⟨hcert, href⟩
  exact href hcert

theorem concreteGramResidual_certifies_terminal
    (h : ConcreteGramResidual) :
    RiemannTerminalCertifies :=
  concreteGramResidual_closes_FINAL_ROOT h

theorem concreteGramResidual_iff_terminal :
    ConcreteGramResidual ↔ RiemannTerminalCertifies :=
  concreteGramResidual_iff_FINAL_ROOT

end MCore.RH.R0
