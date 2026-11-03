import MCore.RH.Analytic.CriticalLogIsometry
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace MCore.RH.R0

open MeasureTheory

/-- Frequency rescaling t = 2*pi*y, in the exact normalization used by MellinInversion. -/
theorem integral_frequency_scale_two_pi (F : ℝ → ℝ) :
    (1 / (2 * Real.pi)) *
      (∫ t : ℝ, F (t / (2 * Real.pi))) =
        ∫ y : ℝ, F y := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hscale := Measure.integral_comp_mul_left F (1 / (2 * Real.pi))
  have habs : |((1 / (2 * Real.pi) : ℝ)⁻¹)| = 2 * Real.pi := by
    rw [inv_div]
    simp [abs_of_pos h2pi]
  rw [show (fun t : ℝ => F (t / (2 * Real.pi))) =
      fun t : ℝ => F ((1 / (2 * Real.pi)) * t) by
        funext t; congr 1; ring] 
  rw [hscale, habs]
  field_simp [ne_of_gt h2pi]

/-- Critical-line Mellin frequency scaling after the Fourier identification. -/
theorem criticalLine_frequency_scale
    (f : ℝ → ℂ) :
    (1 / (2 * Real.pi)) *
      (∫ t : ℝ,
        ‖𝓕 (criticalLogTransport f) (t / (2 * Real.pi))‖ ^ 2) =
      ∫ y : ℝ, ‖𝓕 (criticalLogTransport f) y‖ ^ 2 := by
  exact integral_frequency_scale_two_pi
    (fun y : ℝ => ‖𝓕 (criticalLogTransport f) y‖ ^ 2)

#print axioms MCore.RH.R0.integral_frequency_scale_two_pi

end MCore.RH.R0
