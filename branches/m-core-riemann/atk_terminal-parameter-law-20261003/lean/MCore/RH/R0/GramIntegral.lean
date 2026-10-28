import MCore.RH.R0.GramInverse
import MCore.RH.R0.ChiMemLp
import MCore.RH.R0.RhoBasicFacts
import Mathlib.MeasureTheory.Function.L2Space

namespace MCore.RH.R0

open MeasureTheory Set

/-- The frozen target has the literal chiRepresentative as an a.e. representative. -/
theorem concreteChi_coeFn_ae :
    ((show ConcreteH from concreteNBData.chi) : ℝ → ℝ) =ᵐ[zeroInfinityMeasure]
      chiRepresentative := by
  simpa [concreteNBData, ConcreteH, twoExponent, chiLpConcrete, chiLp] using
    chi_memLp_two.coeFn_toLp

/-- C2: target vector entry as a literal integral over the frozen positive-half-line measure. -/
theorem concreteTargetVector_eq_integral
    (N : ℕ) (i : Fin N) :
    concreteTargetVector N i =
      ∫ x : ℝ, chiRepresentative x * rhoRepresentative i x ∂zeroInfinityMeasure := by
  rw [concreteTargetVector_apply]
  unfold MCore.RH.NB.NBHilbertData.targetEntry
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [concreteChi_coeFn_ae, concreteGeneratorFamily_coeFn_ae i] with x hchi hrho
  simp [hchi, hrho, mul_comm]

/-- C3: Gram entry as a literal product integral over the frozen measure. -/
theorem concreteGramMatrix_eq_integral
    (N : ℕ) (i j : Fin N) :
    concreteGramMatrix N i j =
      ∫ x : ℝ, rhoRepresentative i x * rhoRepresentative j x ∂zeroInfinityMeasure := by
  rw [concreteGramMatrix_apply]
  unfold MCore.RH.NB.NBHilbertData.gramEntry
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    concreteGeneratorFamily_coeFn_ae i,
    concreteGeneratorFamily_coeFn_ae j] with x hi hj
  simp [hi, hj, mul_comm]

/-- Same target identity expressed as a Lebesgue set integral on (0,infinity). -/
theorem concreteTargetVector_eq_setIntegral
    (N : ℕ) (i : Fin N) :
    concreteTargetVector N i =
      ∫ x : ℝ in Ioi 0, chiRepresentative x * rhoRepresentative i x := by
  rw [concreteTargetVector_eq_integral N i]
  rfl

/-- Same Gram identity expressed as a Lebesgue set integral on (0,infinity). -/
theorem concreteGramMatrix_eq_setIntegral
    (N : ℕ) (i j : Fin N) :
    concreteGramMatrix N i j =
      ∫ x : ℝ in Ioi 0, rhoRepresentative i x * rhoRepresentative j x := by
  rw [concreteGramMatrix_eq_integral N i j]
  rfl

#print axioms MCore.RH.R0.concreteTargetVector_eq_setIntegral
#print axioms MCore.RH.R0.concreteGramMatrix_eq_setIntegral

end MCore.RH.R0
