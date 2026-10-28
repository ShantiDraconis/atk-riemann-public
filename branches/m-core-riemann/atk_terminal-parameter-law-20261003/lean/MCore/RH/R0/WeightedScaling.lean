import MCore.RH.R0.WeightedIntegrability
import MCore.RH.R0.LinearIndependentReduction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace MCore.RH.R0

open MeasureTheory Set

/-- Real dilation identity underlying the concrete Mellin scaling law. -/
theorem rhoRepresentative_eq_dilate (n : ℕ) :
    rhoRepresentative n =
      fun x => rhoRepresentative 0 (((rhoIndex n : ℕ) : ℝ) * x) := by
  funext x
  simp [rhoRepresentative, rhoBase, rhoIndex]

/-- A1.3: real weighted-integral scaling, with no zeta input. -/
theorem rho_weighted_integral_scaling
    (n : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ x : ℝ in Ioi 0, rhoRepresentative n x * x ^ (s - 1)) =
      mellinScale n s *
        (∫ x : ℝ in Ioi 0, rhoRepresentative 0 x * x ^ (s - 1)) := by
  let a : ℝ := ((rhoIndex n : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast rhoIndex_pos n
  have hrewrite :
      ∀ x ∈ Ioi (0 : ℝ),
        rhoRepresentative n x * x ^ (s - 1) =
          a ^ (1 - s) *
            (rhoRepresentative 0 (a * x) * (a * x) ^ (s - 1)) := by
    intro x hx
    have hx0 : 0 < x := hx
    rw [rhoRepresentative_eq_dilate n]
    dsimp [a]
    rw [Real.mul_rpow ha.le hx0.le]
    have hpow :
        a ^ (1 - s) * a ^ (s - 1) = 1 := by
      rw [← Real.rpow_add ha]
      ring_nf
      simp
    calc
      rhoRepresentative 0 (a * x) * x ^ (s - 1)
          = (a ^ (1 - s) * a ^ (s - 1)) *
              (rhoRepresentative 0 (a * x) * x ^ (s - 1)) := by
                rw [hpow, one_mul]
      _ = a ^ (1 - s) *
            (rhoRepresentative 0 (a * x) * (a ^ (s - 1) * x ^ (s - 1))) := by
              ring
  rw [setIntegral_congr_fun measurableSet_Ioi hrewrite]
  rw [integral_const_mul]
  rw [integral_comp_mul_left_Ioi
    (fun u : ℝ => rhoRepresentative 0 u * u ^ (s - 1)) 0 ha]
  simp only [mul_zero, smul_eq_mul]
  change a ^ (1 - s) *
      (a⁻¹ * (∫ x : ℝ in Ioi 0, rhoRepresentative 0 x * x ^ (s - 1))) =
    a ^ (-s) *
      (∫ x : ℝ in Ioi 0, rhoRepresentative 0 x * x ^ (s - 1))
  have hfac : a ^ (1 - s) * a⁻¹ = a ^ (-s) := by
    rw [show (1 - s : ℝ) = 1 + (-s) by ring]
    rw [Real.rpow_add ha, Real.rpow_one]
    field_simp
  rw [← mul_assoc, hfac]

/-- A1.3 in the exact producer-interface form used by the discovery tree. -/
theorem A1_RealMellinScaling_realized :
    ∀ (n : ℕ) (s : ℝ), 0 < s → s < 1 →
      (∫ x : ℝ in Set.Ioi 0, rhoRepresentative n x * x ^ (s - 1)) =
        mellinScale n s *
          (∫ x : ℝ in Set.Ioi 0, rhoRepresentative 0 x * x ^ (s - 1)) := by
  intro n s hs0 hs1
  exact rho_weighted_integral_scaling n s hs0 hs1

#print axioms MCore.RH.R0.rhoRepresentative_eq_dilate
#print axioms MCore.RH.R0.rho_weighted_integral_scaling

end MCore.RH.R0
