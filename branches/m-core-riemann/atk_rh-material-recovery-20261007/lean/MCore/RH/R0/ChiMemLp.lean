import MCore.RH.R0.ChiL2
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace MCore.RH.R0

open MeasureTheory

/-- The target representative is pointwise bounded by one. -/
theorem chiRepresentative_norm_le_one (x : BaseDomain) :
    ‖chiRepresentative x‖ ≤ 1 := by
  by_cases hx : 0 < x ∧ x < 1
  · simp [chiRepresentative, hx]
  · simp [chiRepresentative, hx]

/-- The concrete target representative is measurable. -/
theorem chiRepresentative_measurable : Measurable chiRepresentative := by
  unfold chiRepresentative
  apply Measurable.ite
  · change MeasurableSet (Set.Ioi 0 ∩ Set.Iio 1)
    exact MeasurableSet.inter measurableSet_Ioi measurableSet_Iio
  · exact measurable_const
  · exact measurable_const

/-- The if-then-else representative is exactly the constant-one indicator of `(0,1)`. -/
theorem chiRepresentative_eq_indicator :
    chiRepresentative = chiSupport.indicator (fun _ : BaseDomain => (1 : ℝ)) := by
  funext x
  by_cases hx : x ∈ chiSupport
  · have hcond : 0 < x ∧ x < 1 := hx
    simp [chiRepresentative, hx, hcond]
  · have hcond : ¬ (0 < x ∧ x < 1) := by
      simpa [chiSupport] using hx
    simp [chiRepresentative, hx, hcond]

/-- The support interval has finite measure for the selected positive-half-line measure. -/
theorem chiSupport_measure_ne_top : zeroInfinityMeasure chiSupport ≠ ⊤ := by
  have hle : zeroInfinityMeasure chiSupport ≤ ambientMeasure chiSupport := by
    unfold zeroInfinityMeasure
    exact Measure.restrict_apply_le zeroInfinityDomain chiSupport
  have hfinite : ambientMeasure chiSupport ≠ ⊤ := by
    unfold ambientMeasure chiSupport
    simp
  exact ne_top_of_le_ne_top hfinite hle

/-- The actual R0.4 obligation: the concrete target belongs to L². -/
theorem chi_memLp_two : ChiMemLpTwo := by
  rw [ChiMemLpTwo, chiRepresentative_eq_indicator]
  exact memLp_indicator_const twoExponent measurableSet_Ioo (1 : ℝ)
    (Or.inr chiSupport_measure_ne_top)

/-- The unconditional concrete L² target obtained from the proved membership theorem. -/
noncomputable def chiLpConcrete : Lp ℝ twoExponent zeroInfinityMeasure :=
  chiLp chi_memLp_two

end MCore.RH.R0
