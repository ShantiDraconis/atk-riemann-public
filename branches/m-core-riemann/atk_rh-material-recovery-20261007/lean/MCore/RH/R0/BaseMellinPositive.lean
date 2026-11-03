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
    linarith [hx.1]
  have hne : Int.fract (1 / x) ≠ 0 := by
    rw [Int.fract_ne_zero_iff]
    intro hcast
    rcases hcast with ⟨z, hz⟩
    have hzlow : (1 : ℝ) < (z : ℝ) := by simpa [← hz] using hlow
    have hzhigh : (z : ℝ) < 2 := by simpa [← hz] using hhigh
    have hzlow' : (1 : ℤ) < z := by exact_mod_cast hzlow
    have hzhigh' : z < (2 : ℤ) := by exact_mod_cast hzhigh
    omega
  have hnonneg : 0 ≤ Int.fract (1 / x) := Int.fract_nonneg _
  have hpos : 0 < Int.fract (1 / x) := lt_of_le_of_ne hnonneg (Ne.symm hne)
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
    · apply mem_support.mpr
      have hrho : 0 < rhoRepresentative 0 x :=
        rhoRepresentative_zero_pos_on_half_one hx
      have hx0 : 0 < x := by linarith [hx.1]
      exact mul_ne_zero hrho.ne' (Real.rpow_pos_of_pos hx0 _).ne'
    · linarith [hx.1]
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
