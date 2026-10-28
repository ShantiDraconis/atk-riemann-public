import MCore.RH.R0.WeightedIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace MCore.RH.R0

open MeasureTheory Set Function

/-- On (1/2,1), the base fractional-part generator is strictly positive. -/
theorem rhoRepresentative_zero_pos_on_half_one
    {x : ℝ} (hx : x ∈ Ioo (1 / 2 : ℝ) 1) :
    0 < rhoRepresentative 0 x := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hlow : 1 < 1 / x := by
    rw [lt_div_iff₀ hx0]
    simpa using hx.2
  have hhigh : 1 / x < 2 := by
    rw [div_lt_iff₀ hx0]
    nlinarith [hx.1]
  have hfloor : ⌊(1 / x : ℝ)⌋ = (1 : ℤ) := by
    rw [Int.floor_eq_iff]
    norm_num
    exact ⟨le_of_lt (by simpa [one_div] using hlow),
      (by simpa [one_div] using hhigh)⟩
  have hfract : Int.fract (1 / x) = 1 / x - 1 := by
    calc
      Int.fract (1 / x) = 1 / x - (⌊(1 / x : ℝ)⌋ : ℝ) := by rfl
      _ = 1 / x - 1 := by rw [hfloor]; norm_num
  have hpos : 0 < Int.fract (1 / x) := by
    rw [hfract]
    linarith
  simpa [rhoRepresentative, rhoBase, rhoIndex, one_mul] using hpos

/-- A1.4: the base real Mellin integral is strictly positive on 0<s<1. -/
theorem base_weighted_integral_pos
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < ∫ x : ℝ in Ioi 0, rhoRepresentative 0 x * x ^ (s - 1) := by
  let f : ℝ → ℝ := fun x => rhoRepresentative 0 x * x ^ (s - 1)
  have hfint : IntegrableOn f (Ioi 0) volume := by
    simpa [f] using rho_weighted_integrableOn_Ioi 0 s hs0 hs1
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact mul_nonneg (rhoRepresentative_nonneg 0 x)
      (Real.rpow_pos_of_pos hx _).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hfnonneg hfint]
  have hsupp :
      Ioo (1 / 2 : ℝ) 1 ⊆ support f ∩ Ioi 0 := by
    intro x hx
    constructor
    · change f x ≠ 0
      have hrho : 0 < rhoRepresentative 0 x :=
        rhoRepresentative_zero_pos_on_half_one hx
      have hx0 : 0 < x := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hx.1
      exact mul_ne_zero hrho.ne' (Real.rpow_pos_of_pos hx0 _).ne'
    · exact lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hx.1
  exact ((Measure.measure_Ioo_pos volume).mpr (by norm_num : (1 / 2 : ℝ) < 1)).trans_le
    (measure_mono hsupp)

/-- A1.4 in the exact producer-interface form used by discovery. -/
theorem A1_BaseMellinPositive_realized :
    ∀ s : ℝ, 0 < s → s < 1 →
      0 < ∫ x : ℝ in Ioi 0, rhoRepresentative 0 x * x ^ (s - 1) := by
  intro s hs0 hs1
  exact base_weighted_integral_pos s hs0 hs1

#print axioms MCore.RH.R0.rhoRepresentative_zero_pos_on_half_one
#print axioms MCore.RH.R0.base_weighted_integral_pos

end MCore.RH.R0
