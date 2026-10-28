import MCore.RH.Analytic.MellinNearZero
import MCore.RH.Analytic.MellinTailContinuation

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- The fractional Mellin integrand is integrable on the tail for Re(s)>0. -/
theorem fractional_mellin_tail_integrable
    (s : ℂ) (hs0 : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ))
      (Ioi 1) := by
  have hpow :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (-s - 1))
        (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt
      (by simp only [sub_re, neg_re, one_re]; linarith)
      zero_lt_one
  apply Integrable.mono' hpow.norm
  · exact AEStronglyMeasurable.mul
      hpow.aestronglyMeasurable
      ((measurable_id.fract).ofReal.aestronglyMeasurable.restrict)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [norm_mul]
    have hfract : ‖(Int.fract t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    calc
      ‖(t : ℂ) ^ (-s - 1)‖ * ‖(Int.fract t : ℂ)‖
          ≤ ‖(t : ℂ) ^ (-s - 1)‖ * 1 :=
        mul_le_mul_of_nonneg_left hfract (norm_nonneg _)
      _ = ‖(t : ℂ) ^ (-s - 1)‖ := by ring

/-- The near-zero fractional Mellin integrand is integrable for Re(s)<1. -/
theorem fractional_mellin_nearZero_integrable
    (s : ℂ) (hs1 : s.re < 1) :
    IntegrableOn
      (fun t : ℝ => ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ))
      (Ioc 0 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  rw [intervalIntegrable_congr_uIoo
    (g := fun t : ℝ => (t : ℂ) ^ (-s)) ?_]
  · exact intervalIntegral.intervalIntegrable_cpow'
      (by simp only [neg_re]; linarith)
  · intro t ht
    rw [uIoo_of_le zero_le_one] at ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    rw [Int.fract_eq_self.2 ⟨ht0.le, ht1⟩]
    push_cast
    rw [← cpow_add ht0.ne']
    ring_nf

/-- Split the Mellin transform of fract at t=1. -/
theorem mellin_fract_split
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin fractRepresentativeC (-s) =
      (∫ t : ℝ in Ioo 0 1,
        ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ)) +
      fractionalTailComplex s := by
  rw [mellin]
  simp only [fractRepresentativeC, neg_sub]
  have hnear := fractional_mellin_nearZero_integrable s hs1
  have htail := fractional_mellin_tail_integrable s hs0
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hnear htail]
  rw [integral_Ioc_eq_integral_Ioo]
  rfl

/-- The exact fractional-zeta Mellin identity is now material on the critical strip. -/
theorem fractionalZetaMellinIdentity_realized :
    FractionalZetaMellinIdentity := by
  intro s hs0 hs1
  have hsne1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs1
  rw [mellin_fract_split s hs0 hs1]
  rw [d1_nearZero_identity s hs1]
  rw [tailAnalyticContinuation_realized s hs0 hsne1]
  have hsne0 : s ≠ 0 := ne_zero_of_re_pos hs0
  field_simp [hsne0, hsne1]
  ring

/-- D1 is closed all the way to the Mellin transform of rho_0. -/
theorem mellin_rho_base_realized
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (rhoRepresentativeC 0) s = - riemannZeta s / s := by
  exact mellin_rho_base_of_fractionalZeta
    fractionalZetaMellinIdentity_realized s hs0 hs1

/-- D1 for the full concrete generator family. -/
theorem mellin_rho_realized
    (n : ℕ) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (rhoRepresentativeC n) s =
      - (((rhoIndex n : ℕ) : ℂ) ^ (-s)) * riemannZeta s / s := by
  rw [mellin_rhoRepresentativeC_dilate]
  rw [mellin_rho_base_realized s hs0 hs1]
  ring

#print axioms MCore.RH.R0.fractionalZetaMellinIdentity_realized
#print axioms MCore.RH.R0.mellin_rho_base_realized
#print axioms MCore.RH.R0.mellin_rho_realized

end MCore.RH.R0
