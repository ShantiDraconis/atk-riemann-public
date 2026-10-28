import MCore.RH.R0.RhoBasicFacts
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace MCore.RH.R0

open MeasureTheory Set

/--
A1.1: for every real Mellin parameter in the open strip 0 < s < 1,
rho_n(x) * x^(s-1) is integrable on the positive half-line.

Near zero we use 0 <= rho_n <= 1. On x > 1 we use the exact tail
rho_n(x) = 1 / ((n+1)x), reducing to x^(s-2).
-/
theorem rho_weighted_integrableOn_Ioi
    (n : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn
      (fun x : ℝ => rhoRepresentative n x * x ^ (s - 1))
      (Ioi 0) volume := by
  have hnear_rpow :
      IntegrableOn (fun x : ℝ => x ^ (s - 1)) (Ioc 0 1) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hnear_meas :
      AEStronglyMeasurable
        (fun x : ℝ => rhoRepresentative n x * x ^ (s - 1))
        (volume.restrict (Ioc 0 1)) := by
    apply AEStronglyMeasurable.mul
    · exact (rhoRepresentative_measurable_public n).aestronglyMeasurable.restrict
    · exact ContinuousOn.aestronglyMeasurable
        (continuousOn_of_forall_continuousAt fun x hx =>
          Real.continuousAt_rpow_const _ _ (Or.inl hx.1.ne'))
        measurableSet_Ioc
  have hnear :
      IntegrableOn
        (fun x : ℝ => rhoRepresentative n x * x ^ (s - 1))
        (Ioc 0 1) volume := by
    refine Integrable.mono' hnear_rpow hnear_meas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    have hp : 0 ≤ x ^ (s - 1) :=
      (Real.rpow_pos_of_pos hx.1 _).le
    have hr : 0 ≤ rhoRepresentative n x :=
      rhoRepresentative_nonneg n x
    have hr1 : rhoRepresentative n x ≤ 1 :=
      rhoRepresentative_le_one n x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr hp)]
    exact mul_le_of_le_one_left hp hr1
  have htail_rpow :
      IntegrableOn (fun x : ℝ => x ^ (s - 2)) (Ioi 1) volume := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have htail_model :
      IntegrableOn
        (fun x : ℝ =>
          (1 / (((rhoIndex n : ℕ) : ℝ))) * x ^ (s - 2))
        (Ioi 1) volume :=
    htail_rpow.const_mul _
  have htail :
      IntegrableOn
        (fun x : ℝ => rhoRepresentative n x * x ^ (s - 1))
        (Ioi 1) volume := by
    refine htail_model.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have ha0 : 0 < ((rhoIndex n : ℕ) : ℝ) := by
      exact_mod_cast rhoIndex_pos n
    change
      (1 / (((rhoIndex n : ℕ) : ℝ))) * x ^ (s - 2) =
        rhoRepresentative n x * x ^ (s - 1)
    rw [rhoRepresentative_tail n hx]
    rw [show s - 2 = (s - 1) - 1 by ring,
      Real.rpow_sub_one hx0.ne' (s - 1)]
    field_simp
  have hunion := hnear.union htail
  have hset : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hx0, _⟩ | hx1)
      · exact hx0
      · linarith
    · intro hx0
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx0, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hset]
  exact hunion

/-- A1.1 in the exact producer-interface form used by RHA1Decomposition. -/
theorem A1_WeightedIntegrability_realized :
    ∀ (n : ℕ) (s : ℝ), 0 < s → s < 1 →
      IntegrableOn
        (fun x : ℝ => rhoRepresentative n x * x ^ (s - 1))
        (Set.Ioi 0) := by
  intro n s hs0 hs1
  exact rho_weighted_integrableOn_Ioi n s hs0 hs1

#print axioms MCore.RH.R0.rho_weighted_integrableOn_Ioi
#print axioms MCore.RH.R0.A1_WeightedIntegrability_realized

end MCore.RH.R0
