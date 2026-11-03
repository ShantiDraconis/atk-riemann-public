import MCore.RH.R0.VasyuninUnitBlocksReduction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace MCore.RH.R0

open MeasureTheory Set

/-- Positive cutoff small enough that both fractional parts are in their linear branch. -/
noncomputable def rationalAutocorrelationCutoff (h k : ℕ) : ℝ :=
  1 / ((h + k : ℕ) : ℝ)

theorem rationalAutocorrelationCutoff_pos
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    0 < rationalAutocorrelationCutoff h k := by
  unfold rationalAutocorrelationCutoff
  positivity

/-- On the initial interval, the rational autocorrelation integrand is constant h/k. -/
theorem rationalAutocorrelationIntegrand_near_zero
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k)
    {t : ℝ}
    (ht0 : 0 < t)
    (htδ : t ≤ rationalAutocorrelationCutoff h k) :
    rationalAutocorrelationIntegrand h k t = (h : ℝ) / (k : ℝ) := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsum : (1 : ℝ) < ((h + k : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨by omega, by omega⟩
  have ht1 : t < 1 := by
    calc
      t ≤ rationalAutocorrelationCutoff h k := htδ
      _ < 1 := by
        unfold rationalAutocorrelationCutoff
        exact one_div_lt_one (by positivity) hsum
  have hrt0 : 0 ≤ ((h : ℝ) / (k : ℝ)) * t := by positivity
  have hrt1 : ((h : ℝ) / (k : ℝ)) * t < 1 := by
    calc
      ((h : ℝ) / (k : ℝ)) * t
          ≤ ((h : ℝ) / (k : ℝ)) * rationalAutocorrelationCutoff h k := by
            gcongr
      _ = (h : ℝ) / ((k : ℝ) * ((h + k : ℕ) : ℝ)) := by
            unfold rationalAutocorrelationCutoff
            field_simp
            ring
      _ < 1 := by
            rw [div_lt_one (mul_pos hkR (by positivity))]
            nlinarith
  unfold rationalAutocorrelationIntegrand
  rw [Int.fract_eq_self.2 ⟨hrt0, hrt1⟩]
  rw [Int.fract_eq_self.2 ⟨ht0.le, ht1⟩]
  field_simp [ht0.ne', hkR.ne']
  ring

/-- The rational autocorrelation kernel is globally integrable on the positive half-line. -/
theorem rationalAutocorrelationIntegrable_realized :
    RationalAutocorrelationIntegrable := by
  intro h k hh hk
  let δ := rationalAutocorrelationCutoff h k
  have hδ : 0 < δ := rationalAutocorrelationCutoff_pos h k hh hk
  have hnear :
      IntegrableOn
        (rationalAutocorrelationIntegrand h k)
        (Ioc 0 δ) := by
    have hconst :
        IntegrableOn (fun _ : ℝ => (h : ℝ) / (k : ℝ)) (Ioc 0 δ) := by
      exact integrableOn_const measure_Ioc_lt_top.ne
    refine hconst.congr_fun ?_ measurableSet_Ioc
    intro t ht
    exact (rationalAutocorrelationIntegrand_near_zero h k hh hk ht.1 ht.2).symm
  have htailModel :
      IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi δ) := by
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hδ
  have hmeas :
      AEStronglyMeasurable
        (rationalAutocorrelationIntegrand h k)
        (volume.restrict (Ioi δ)) := by
    have hratio : Measurable (fun t : ℝ => ((h : ℝ) / (k : ℝ)) * t) :=
      measurable_const.mul measurable_id
    have hnum : Measurable (fun t : ℝ =>
        Int.fract (((h : ℝ) / (k : ℝ)) * t) * Int.fract t) :=
      hratio.fract.mul measurable_id.fract
    have hden : Measurable (fun t : ℝ => t ^ 2) := measurable_id.pow_const 2
    exact (hnum.div hden).aestronglyMeasurable.restrict
  have htail :
      IntegrableOn
        (rationalAutocorrelationIntegrand h k)
        (Ioi δ) := by
    refine Integrable.mono' htailModel hmeas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hδ.trans ht
    have hfa0 : 0 ≤ Int.fract (((h : ℝ) / (k : ℝ)) * t) := Int.fract_nonneg _
    have hfb0 : 0 ≤ Int.fract t := Int.fract_nonneg _
    have hfa1 : Int.fract (((h : ℝ) / (k : ℝ)) * t) ≤ 1 :=
      (Int.fract_lt_one _).le
    have hfb1 : Int.fract t ≤ 1 := (Int.fract_lt_one _).le
    have hden : 0 < t ^ 2 := sq_pos_of_pos ht0
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hfa0 hfb0) hden.le)]
    have hprod : Int.fract (((h : ℝ) / (k : ℝ)) * t) * Int.fract t ≤ 1 := by
      nlinarith
    calc
      rationalAutocorrelationIntegrand h k t
          ≤ 1 / t ^ 2 := by
            unfold rationalAutocorrelationIntegrand
            exact div_le_div_of_nonneg_right hprod hden.le
      _ = t ^ (-2 : ℝ) := by
            rw [Real.rpow_neg ht0.le, Real.rpow_two]
      _ = ‖t ^ (-2 : ℝ)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg _ _)]
  have hunion := hnear.union htail
  have hset : Ioc (0 : ℝ) δ ∪ Ioi δ = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact hδ.trans ht
    · intro ht
      by_cases hle : t ≤ δ
      · exact Or.inl ⟨ht, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
  rw [← hset]
  exact hunion

#print axioms MCore.RH.R0.rationalAutocorrelationIntegrable_realized

end MCore.RH.R0
