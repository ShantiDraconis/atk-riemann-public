import MCore.RH.Analytic.MellinRhoReduction

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- D1.3: the near-zero fractional-part Mellin piece is elementary. -/
theorem d1_nearZero_identity
    (s : ℂ) (hs : s.re < 1) :
    (∫ t : ℝ in Ioo 0 1,
      ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ)) =
      1 / (1 - s) := by
  rw [integral_Ioo_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hcongr :
      (∫ t : ℝ in (0 : ℝ)..1,
        ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ)) =
      ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (-s) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    by_cases h0 : t = 0
    · subst t
      simp
    by_cases h1 : t = 1
    · subst t
      simp
    · have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
      have ht1' : t < 1 := lt_of_le_of_ne ht1 h1
      rw [Int.fract_eq_self.2 ⟨ht0'.le, ht1'⟩]
      push_cast
      rw [← cpow_add ht0'.ne']
      ring_nf
  rw [hcongr]
  rw [integral_cpow]
  · have hsne : 1 - s ≠ 0 := by
      intro h
      have : s = 1 := by linear_combination h
      subst s
      norm_num at hs
    simp [hsne]
    ring
  · left
    simp only [neg_re]
    linarith

#print axioms MCore.RH.R0.d1_nearZero_identity

end MCore.RH.R0
