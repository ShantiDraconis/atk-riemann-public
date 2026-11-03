import MCore.RH.Analytic.MellinPlancherelReduction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace MCore.RH.R0

open MeasureTheory Set

/-- Whole-line logarithmic substitution with the sign convention used by Mellin. -/
theorem integral_exp_neg_comp (h : ℝ → ℝ) :
    (∫ u : ℝ, Real.exp (-u) * h (Real.exp (-u))) =
      ∫ x : ℝ in Ioi 0, h x := by
  let F : ℝ → ℝ := fun u => Real.exp u * h (Real.exp u)
  have hneg : (∫ u : ℝ, F (-u)) = ∫ u : ℝ, F u := by
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding F
  have hexp : (∫ u : ℝ, F u) = ∫ x : ℝ in Ioi 0, h x := by
    simpa [F] using integral_comp_exp h
  calc
    (∫ u : ℝ, Real.exp (-u) * h (Real.exp (-u)))
        = ∫ u : ℝ, F (-u) := by rfl
    _ = ∫ u : ℝ, F u := hneg
    _ = ∫ x : ℝ in Ioi 0, h x := hexp

/-- Pointwise norm-square identity for the critical logarithmic transport. -/
theorem normSq_criticalLogTransport (f : ℝ → ℂ) (u : ℝ) :
    ‖criticalLogTransport f u‖ ^ 2 =
      Real.exp (-u) * ‖f (Real.exp (-u))‖ ^ 2 := by
  rw [criticalLogTransport, norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [mul_pow]
  congr 1
  rw [← Real.exp_mul]
  congr 1
  ring

/-- Exact norm-square change of variables underlying Mellin--Plancherel. -/
theorem criticalLogTransport_integral_norm_sq (f : ℝ → ℂ) :
    (∫ u : ℝ, ‖criticalLogTransport f u‖ ^ 2) =
      ∫ x : ℝ in Ioi 0, ‖f x‖ ^ 2 := by
  simp_rw [normSq_criticalLogTransport]
  exact integral_exp_neg_comp (fun x => ‖f x‖ ^ 2)

theorem criticalLogIntegralIsometry_realized : CriticalLogIntegralIsometry := by
  intro f
  exact criticalLogTransport_integral_norm_sq f

#print axioms MCore.RH.R0.criticalLogTransport_integral_norm_sq

end MCore.RH.R0
