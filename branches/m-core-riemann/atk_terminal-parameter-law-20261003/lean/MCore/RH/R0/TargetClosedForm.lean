import MCore.RH.R0.FractionalTailEuler
import MCore.RH.R0.GramIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace MCore.RH.R0

open MeasureTheory Set

/-- Inversion x -> 1/x converts the target integral into a tail fractional-part integral. -/
theorem target_entry_inversion
    (N : ℕ) (i : Fin N) :
    concreteTargetVector N i =
      ∫ x : ℝ in Ioi 1,
        Int.fract (x / (((rhoIndex i : ℕ) : ℝ))) / (x ^ 2) := by
  rw [concreteTargetVector_eq_setIntegral N i]
  let a : ℝ := ((rhoIndex i : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; exact_mod_cast rhoIndex_pos i
  have hinv := integral_comp_rpow_Ioi
    (g := fun y : ℝ => chiRepresentative y * rhoRepresentative i y)
    (p := (-1 : ℝ)) (by norm_num : (-1 : ℝ) ≠ 0)
  symm at hinv
  calc
    (∫ x : ℝ in Ioi 0, chiRepresentative x * rhoRepresentative i x)
        = ∫ x : ℝ in Ioi 0,
            (|-1 : ℝ| * x ^ ((-1 : ℝ) - 1)) *
              (chiRepresentative (x ^ (-1 : ℝ)) *
                rhoRepresentative i (x ^ (-1 : ℝ))) := by
            simpa [smul_eq_mul] using hinv
    _ = ∫ x : ℝ in Ioi 1, Int.fract (x / a) / x ^ 2 := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx1 : 1 < x
      · have hx0 : 0 < x := zero_lt_one.trans hx1
        simp [Set.indicator_of_mem hx1, Set.indicator_of_mem hx0, abs_of_nonneg,
          Real.rpow_neg_one, hx0.ne', chiRepresentative, hx1, rhoRepresentative, rhoBase,
          rhoIndex, a]
        field_simp
      · have hnot1 : x ∉ Ioi (1 : ℝ) := hx1
        by_cases hx0 : 0 < x
        · have hinvge : 1 ≤ x⁻¹ := by
            rw [le_inv₀ hx0]; exact le_of_not_gt hx1
          simp [Set.indicator_of_not_mem hnot1, Set.indicator_of_mem hx0,
            Real.rpow_neg_one, hx0.ne', chiRepresentative, hinvge.not_lt]
        · have hnot0 : x ∉ Ioi (0 : ℝ) := hx0
          simp [Set.indicator_of_not_mem hnot0, Set.indicator_of_not_mem hnot1]

/-- Dilation x=a*t isolates the universal fractional-tail kernel. -/
theorem target_entry_scaled_tail
    (N : ℕ) (i : Fin N) :
    concreteTargetVector N i =
      (1 / (((rhoIndex i : ℕ) : ℝ))) *
        (∫ t : ℝ in Ioi (1 / (((rhoIndex i : ℕ) : ℝ))),
          fractionalTailIntegrand t) := by
  rw [target_entry_inversion N i]
  let a : ℝ := ((rhoIndex i : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; exact_mod_cast rhoIndex_pos i
  have hchange := integral_comp_mul_left_Ioi'
    (g := fun x : ℝ => Int.fract (x / a) / x ^ 2)
    (a := 1 / a) ha
  have hsimp :
      ∀ t ∈ Ioi (1 / a),
        Int.fract ((a * t) / a) / ((a * t) ^ 2) =
          (1 / a ^ 2) * fractionalTailIntegrand t := by
    intro t ht
    have hane : a ≠ 0 := ha.ne'
    simp [fractionalTailIntegrand, hane]
    field_simp
  rw [show a * (1 / a) = 1 by field_simp] at hchange
  rw [← hchange]
  rw [setIntegral_congr_fun measurableSet_Ioi hsimp]
  rw [integral_const_mul]
  dsimp [a]
  field_simp
  ring

/-- The exact transform used by C4. -/
theorem targetEntryTransform_realized : TargetEntryTransform := by
  intro N i
  dsimp
  let a : ℝ := ((rhoIndex i : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; exact_mod_cast rhoIndex_pos i
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast Nat.succ_le_iff.mpr (rhoIndex_pos i)
  rw [target_entry_scaled_tail N i]
  change (1 / a) * (∫ t : ℝ in Ioi (1 / a), fractionalTailIntegrand t) = _
  rw [← Ioc_union_Ioi_eq_Ioi (show 1 / a ≤ (1 : ℝ) by
    exact (one_div_le_one ha).mpr ha1)]
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  · rw [integral_Ioc_eq_integral_Ioo]
    have helem := target_elementary_interval_identity_realized a ha1
    dsimp [TargetElementaryIntervalIdentity] at helem
    rw [show (fun t : ℝ => Int.fract t / t ^ 2) = fractionalTailIntegrand by
      funext t; rfl] at helem
    rw [mul_add, helem]
    rfl
  · exact fractionalTailIntegrand_integrableOn.mono_set Ioc_subset_Ioi_self
  · exact fractionalTailIntegrand_integrableOn

/-- C4: exact closed form for the concrete target vector. -/
theorem concreteTargetVector_closed_form
    (N : ℕ) (i : Fin N) :
    concreteTargetVector N i =
      (Real.log ((rhoIndex i : ℕ) : ℝ) + 1 - Real.eulerMascheroniConstant) /
        (((rhoIndex i : ℕ) : ℝ)) := by
  exact target_closed_form_of_transform_tail
    targetEntryTransform_realized fractionalTailEulerIdentity_realized N i

#print axioms MCore.RH.R0.concreteTargetVector_closed_form

end MCore.RH.R0
