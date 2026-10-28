import MCore.RH.NB.FinalExternal
import MCore.RH.NB.CoefficientEndpoint
import MCore.RH.R0.RhoConcrete
import MCore.RH.R0.ConcreteGramEndpoint

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/-- Concrete final coefficient residual on the certified Báez--Duarte family. -/
def ConcreteCoefficientResidual : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon ->
    ∃ N : ℕ, ∃ c : Fin N -> ℝ,
      ‖concreteNBData.chi -
        concreteNBData.coefficientApproximantAt concreteGeneratorFamily N c‖
        < epsilon

/-- The concrete coefficient residual is exactly enough to create FinalExternal. -/
theorem concreteCoefficientResidual_to_FinalExternal
    (h : ConcreteCoefficientResidual) :
    FinalExternalCertificate concreteNBData concreteGeneratorFamily := by
  apply (concreteNBData.DNToZero_iff_exists_coefficients
    concreteGeneratorFamily).2
  exact h

/-- Kernel-level concrete zero-defect final root. -/
theorem concreteCoefficientResidual_to_FINAL_ROOT
    (h : ConcreteCoefficientResidual) :
    FINAL_ROOT concreteNBData concreteGeneratorFamily :=
  finalExternal_to_FINAL_ROOT concreteNBData concreteGeneratorFamily
    (concreteCoefficientResidual_to_FinalExternal h)

/-- Equivalent finite Gram scalar formulation with the concrete chi norm = 1. -/
def ConcreteGramResidual : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon ->
    ∃ N : ℕ, ∃ c : Fin N -> ℝ,
      (∀ j : Fin N,
        (∑ i : Fin N,
          c i * concreteNBData.gramEntry concreteGeneratorFamily i j) =
          concreteNBData.targetEntry concreteGeneratorFamily j) ∧
      1 - (∑ i : Fin N,
        c i * concreteNBData.targetEntry concreteGeneratorFamily i) <
        epsilon ^ 2

theorem concreteGramResidual_to_FINAL_ROOT
    (h : ConcreteGramResidual) :
    FINAL_ROOT concreteNBData concreteGeneratorFamily :=
  (concrete_DNLimit_eq_zero_iff_gram_scalar).2 h

#print axioms MCore.RH.R0.concreteCoefficientResidual_to_FinalExternal
#print axioms MCore.RH.R0.concreteCoefficientResidual_to_FINAL_ROOT
#print axioms MCore.RH.R0.concreteGramResidual_to_FINAL_ROOT

end MCore.RH.R0
