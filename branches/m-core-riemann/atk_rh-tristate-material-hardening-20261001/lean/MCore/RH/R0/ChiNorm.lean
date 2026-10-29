import MCore.RH.R0.RhoConcrete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace MCore.RH.R0

open MeasureTheory Set

/-- The support of chi has measure one in the selected L2(0,infinity) measure. -/
theorem zeroInfinityMeasure_chiSupport :
    zeroInfinityMeasure chiSupport = 1 := by
  change (volume.restrict (Ioi (0 : ℝ))) (Ioo (0 : ℝ) 1) = 1
  rw [Measure.restrict_apply measurableSet_Ioo]
  have hset :
      Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, _⟩
      exact ⟨hx0, hx1⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨⟨hx0, hx1⟩, hx0⟩
  rw [hset, Real.volume_Ioo]
  norm_num

/-- The distinguished concrete Nyman--Beurling target has L2 norm exactly one. -/
theorem chiLpConcrete_norm :
    ‖chiLpConcrete‖ = 1 := by
  unfold chiLpConcrete chiLp
  rw [Lp.norm_toLp]
  rw [chiRepresentative_eq_indicator]
  change
    (eLpNorm
      ((Ioo (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)))
      twoExponent zeroInfinityMeasure).toReal = 1
  rw [eLpNorm_indicator_const measurableSet_Ioo
    (by simp [twoExponent]) (by simp [twoExponent])]
  have hmeasure :
      zeroInfinityMeasure (Ioo (0 : ℝ) 1) = 1 := by
    simpa [chiSupport] using zeroInfinityMeasure_chiSupport
  rw [hmeasure]
  simp [twoExponent]

/-- Squared normalization used by the finite Gram energy. -/
theorem chiLpConcrete_norm_sq :
    ‖chiLpConcrete‖ ^ 2 = 1 := by
  rw [chiLpConcrete_norm]
  norm_num

/-- The same normalization through the concrete NB data field. -/
theorem concreteNBData_chi_norm :
    ‖concreteNBData.chi‖ = 1 := by
  simpa [concreteNBData, ConcreteH, twoExponent] using chiLpConcrete_norm

theorem concreteNBData_chi_norm_sq :
    ‖concreteNBData.chi‖ ^ 2 = 1 := by
  rw [concreteNBData_chi_norm]
  norm_num

#print axioms zeroInfinityMeasure_chiSupport
#print axioms chiLpConcrete_norm
#print axioms concreteNBData_chi_norm
#print axioms concreteNBData_chi_norm_sq

end MCore.RH.R0
