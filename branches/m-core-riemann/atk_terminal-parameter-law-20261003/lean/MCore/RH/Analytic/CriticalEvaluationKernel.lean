import MCore.RH.Analytic.ResidualCriticalLine
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace MCore.RH.R0

open MeasureTheory Complex Real

/-- Distance of an interior point from the critical line. -/
noncomputable def criticalHalfPlaneDepth (ρ : ℂ) : ℝ :=
  ρ.re - 1 / 2

/--
Cauchy evaluation-kernel candidate on the critical line.
No reproducing property is asserted in this definition.
-/
noncomputable def criticalEvaluationKernel (ρ : ℂ) (t : ℝ) : ℂ :=
  (((criticalHalfPlaneDepth ρ : ℝ) : ℂ) +
    ((t - ρ.im : ℝ) : ℂ) * I)⁻¹

theorem criticalHalfPlaneDepth_pos
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    0 < criticalHalfPlaneDepth ρ := by
  unfold criticalHalfPlaneDepth
  linarith

/-- Exact squared norm of the Cauchy kernel. -/
theorem criticalEvaluationKernel_normSq
    (ρ : ℂ) (t : ℝ) :
    ‖criticalEvaluationKernel ρ t‖ ^ 2 =
      1 / (criticalHalfPlaneDepth ρ ^ 2 + (t - ρ.im) ^ 2) := by
  unfold criticalEvaluationKernel
  rw [norm_inv, inv_pow, Complex.sq_norm]
  simp [Complex.normSq_apply, criticalHalfPlaneDepth]
  ring

/-- The scalar squared-norm kernel is integrable whenever ρ lies right of the critical line. -/
theorem criticalEvaluationKernel_normSq_integrable
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    Integrable (fun t : ℝ => ‖criticalEvaluationKernel ρ t‖ ^ 2) := by
  let a := criticalHalfPlaneDepth ρ
  have ha : 0 < a := criticalHalfPlaneDepth_pos hρ
  have hbase : Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have hscaled :
      Integrable (fun u : ℝ => (1 + (u / a) ^ 2)⁻¹) := by
    rw [show (fun u : ℝ => (1 + (u / a) ^ 2)⁻¹) =
      fun u => (fun v : ℝ => (1 + v ^ 2)⁻¹) (u / a) by rfl]
    exact (MeasureTheory.integrable_comp_div_iff (μ := volume)
      (fun v : ℝ => (1 + v ^ 2)⁻¹) ha.ne').2 hbase
  have hconst :
      Integrable (fun u : ℝ => (1 / a ^ 2) * (1 + (u / a) ^ 2)⁻¹) :=
    hscaled.const_mul _
  have htranslate :
      Integrable
        (fun t : ℝ =>
          (1 / a ^ 2) * (1 + ((t - ρ.im) / a) ^ 2)⁻¹) := by
    simpa [sub_eq_add_neg] using
      (hconst.comp_add_right (-ρ.im))
  apply htranslate.congr
  filter_upwards with t
  rw [criticalEvaluationKernel_normSq]
  dsimp [a]
  have ha0 : criticalHalfPlaneDepth ρ ≠ 0 := ha.ne'
  field_simp
  ring

/-- The exact L² mass of the unnormalized evaluation kernel. -/
theorem integral_criticalEvaluationKernel_normSq
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    (∫ t : ℝ, ‖criticalEvaluationKernel ρ t‖ ^ 2) =
      Real.pi / criticalHalfPlaneDepth ρ := by
  let a := criticalHalfPlaneDepth ρ
  have ha : 0 < a := criticalHalfPlaneDepth_pos hρ
  rw [integral_congr_ae
    (Eventually.of_forall fun t => criticalEvaluationKernel_normSq ρ t)]
  have htranslate :
      (∫ t : ℝ, 1 / (a ^ 2 + (t - ρ.im) ^ 2)) =
        ∫ u : ℝ, 1 / (a ^ 2 + u ^ 2) := by
    simpa [sub_eq_add_neg] using
      (integral_add_right_eq_self
        (fun u : ℝ => 1 / (a ^ 2 + u ^ 2)) (-ρ.im))
  rw [htranslate]
  have hpoint :
      (fun u : ℝ => 1 / (a ^ 2 + u ^ 2)) =
        fun u : ℝ => (1 / a ^ 2) * (1 + (u / a) ^ 2)⁻¹ := by
    funext u
    field_simp [ha.ne']
    ring
  rw [hpoint, integral_const_mul]
  have hscale := Measure.integral_comp_div
    (fun x : ℝ => (1 + x ^ 2)⁻¹) a
  rw [abs_of_pos ha, integral_univ_inv_one_add_sq] at hscale
  rw [hscale]
  field_simp [ha.ne']
  ring

#print axioms MCore.RH.R0.criticalEvaluationKernel_normSq
#print axioms MCore.RH.R0.criticalEvaluationKernel_normSq_integrable
#print axioms MCore.RH.R0.integral_criticalEvaluationKernel_normSq

end MCore.RH.R0
