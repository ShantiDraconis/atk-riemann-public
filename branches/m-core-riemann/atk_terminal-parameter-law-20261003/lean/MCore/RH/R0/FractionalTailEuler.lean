import MCore.RH.R0.TargetClosedFormReduction
import MCore.RH.R0.RhoBasicFacts
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace MCore.RH.R0

open MeasureTheory Set Filter Topology

noncomputable def fractionalTailIntegrand (t : ℝ) : ℝ :=
  Int.fract t / (t ^ 2)

/-- The universal fractional-tail integrand is integrable on (1,infinity). -/
theorem fractionalTailIntegrand_integrableOn :
    IntegrableOn fractionalTailIntegrand (Ioi 1) volume := by
  have hmodel :
      IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi 1) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hmeas :
      AEStronglyMeasurable fractionalTailIntegrand
        (volume.restrict (Ioi 1)) := by
    exact (((measurable_id.fract).div (measurable_id.pow_const 2))).aestronglyMeasurable.restrict
  refine Integrable.mono' hmodel hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hf0 : 0 ≤ Int.fract t := Int.fract_nonneg _
  have hf1 : Int.fract t ≤ 1 := le_of_lt (Int.fract_lt_one _)
  have hden : 0 < t ^ 2 := sq_pos_of_pos ht0
  rw [fractionalTailIntegrand, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hf0 hden.le)]
  have hle : Int.fract t / t ^ 2 ≤ 1 / t ^ 2 := div_le_div_of_nonneg_right hf1 hden.le
  have hrpow : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
    rw [Real.rpow_neg ht0.le, Real.rpow_two]
  rw [hrpow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hle

/-- On each positive integer block, our fractional integrand is exactly Mathlib's zeta-asymptotic term. -/
theorem fractionalTail_block_eq_zetaTerm (n : ℕ) :
    (∫ t : ℝ in (n + 1 : ℕ)..(n + 2 : ℕ), fractionalTailIntegrand t) =
      ZetaAsymptotics.term (n + 1) 1 := by
  have hle : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by norm_num
  rw [intervalIntegral.integral_of_le hle]
  rw [ZetaAsymptotics.term, intervalIntegral.integral_of_le hle]
  rw [← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  have hfloor : ⌊t⌋ = (n + 1 : ℤ) := by
    exact Int.floor_eq_on_Ico (n + 1 : ℤ) t (by simpa using ht)
  rw [fractionalTailIntegrand, Int.fract, hfloor]
  norm_num

/-- Finite truncations of the universal tail are exactly Mathlib's finite term sums. -/
theorem fractionalTail_partial_eq_termSum (N : ℕ) :
    (∫ t : ℝ in (1 : ℝ)..(N + 1 : ℕ), fractionalTailIntegrand t) =
      ZetaAsymptotics.term_sum 1 N := by
  rw [ZetaAsymptotics.term_sum]
  have hint : ∀ k < N,
      IntervalIntegrable fractionalTailIntegrand volume
        ((k + 1 : ℕ) : ℝ) ((k + 2 : ℕ) : ℝ) := by
    intro k hk
    exact fractionalTailIntegrand_integrableOn.intervalIntegrable
      (by positivity) (by positivity)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fractionalTailIntegrand) (μ := volume)
    (a := fun k : ℕ => ((k + 1 : ℕ) : ℝ)) hint
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  exact fractionalTail_block_eq_zetaTerm k

/-- The universal tail constant is exactly 1 - Euler's constant. -/
theorem fractionalTailEulerIdentity_realized :
    FractionalTailEulerIdentity := by
  unfold FractionalTailEulerIdentity fractionalTailConstant
  have hInt :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in (1 : ℝ)..((N + 1 : ℕ) : ℝ), fractionalTailIntegrand t)
        atTop
        (𝓝 (∫ t : ℝ in Ioi 1, fractionalTailIntegrand t)) := by
    exact intervalIntegral_tendsto_integral_Ioi 1
      fractionalTailIntegrand_integrableOn
      (tendsto_natCast_atTop_atTop.atTop_add_const_right 1)
  have hSum :
      Tendsto (fun N : ℕ => ZetaAsymptotics.term_sum 1 N)
        atTop (𝓝 (1 - Real.eulerMascheroniConstant)) := by
    exact ZetaAsymptotics.term_tsum_one.tendsto_sum_nat
  exact tendsto_nhds_unique
    (hInt.congr' (Eventually.of_forall fun N => fractionalTail_partial_eq_termSum N))
    hSum

#print axioms MCore.RH.R0.fractionalTailEulerIdentity_realized

end MCore.RH.R0
