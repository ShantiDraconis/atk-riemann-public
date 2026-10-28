import MCore.RH.R0.RhoConcrete
import MCore.RH.NB.ZeroLimitFrontier
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MCore.RH.R2

noncomputable section

def FinalStatement : Prop := RiemannHypothesis

def CompressedEndpoint : Prop :=
  MCore.RH.R0.concreteNBData.DNLimit
    MCore.RH.R0.concreteGeneratorFamily = 0

def OpenBridge : Prop :=
  MCore.RH.R0.concreteNBData.DNToZero
    MCore.RH.R0.concreteGeneratorFamily

def R1ExternalBridge : Prop :=
  CompressedEndpoint ↔ FinalStatement

def VanishingUpperCertificate : Prop :=
  ∃ eps : ℕ → ℝ,
    (∀ N : ℕ,
      MCore.RH.R0.concreteNBData.DN
        MCore.RH.R0.concreteGeneratorFamily N ≤ eps N) ∧
    Filter.Tendsto eps Filter.atTop (nhds 0)

theorem openBridge_of_vanishing
    (V : VanishingUpperCertificate) :
    OpenBridge := by
  rcases V with ⟨eps, hupper, heps⟩
  unfold OpenBridge MCore.RH.NB.NBHilbertData.DNToZero
  exact squeeze_zero
    (fun N =>
      MCore.RH.R0.concreteNBData.DN_nonneg
        MCore.RH.R0.concreteGeneratorFamily N)
    hupper heps

theorem compressed_of_openBridge
    (h : OpenBridge) :
    CompressedEndpoint := by
  exact
    (MCore.RH.NB.NBHilbertData.DNToZero_iff_DNLimit_eq_zero
      MCore.RH.R0.concreteNBData
      MCore.RH.R0.concreteGeneratorFamily).1 h

structure FinalExternal : Type where
  r1 : R1ExternalBridge
  vanishing : VanishingUpperCertificate

def FINAL_EXTERNAL : Type := FinalExternal

theorem FINAL_ROOT
    (E : FINAL_EXTERNAL) :
    FinalStatement := by
  exact E.r1.mp (compressed_of_openBridge (openBridge_of_vanishing E.vanishing))

#print axioms MCore.RH.R2.FINAL_ROOT

end
end MCore.RH.R2
