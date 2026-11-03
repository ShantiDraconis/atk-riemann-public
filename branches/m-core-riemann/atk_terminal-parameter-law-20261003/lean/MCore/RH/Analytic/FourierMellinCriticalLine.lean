import MCore.RH.Analytic.LogPullbackIsometry
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace MCore.RH.R0

open MeasureTheory Complex
open scoped FourierTransform

/-- On the critical line, the Mellin transform is the Fourier transform of the critical log pullback. -/
theorem mellin_criticalLine_eq_fourier
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    mellin (residualRepresentativeC c) (criticalLinePoint t) =
      𝓕 (criticalLogPullback c) (t / (2 * Real.pi)) := by
  simpa [criticalLinePoint, criticalLogPullback, mul_comm, mul_left_comm, mul_assoc] using
    (mellin_eq_fourierIntegral (residualRepresentativeC c)
      (s := criticalLinePoint t))

/-- Reparameterizing t = 2*pi*xi gives the exact 1/(2*pi) factor. -/
theorem fourier_integral_eq_mellin_line
    {N : ℕ} (c : Fin N → ℝ) :
    (∫ ξ : ℝ, Complex.normSq (𝓕 (criticalLogPullback c) ξ)) =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          Complex.normSq
            (mellin (residualRepresentativeC c) (criticalLinePoint t)) := by
  let g : ℝ → ℝ := fun t =>
    Complex.normSq
      (mellin (residualRepresentativeC c) (criticalLinePoint t))
  have hscale := Measure.integral_comp_mul_left g (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hfactor : |(2 * Real.pi)⁻¹| = 1 / (2 * Real.pi) := by
    rw [abs_of_pos (inv_pos.mpr hpi)]
    rfl
  rw [hfactor] at hscale
  have hleft :
      (∫ ξ : ℝ, g ((2 * Real.pi) * ξ)) =
        ∫ ξ : ℝ, Complex.normSq (𝓕 (criticalLogPullback c) ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    unfold g
    have h2pi : 2 * Real.pi ≠ 0 := ne_of_gt hpi
    rw [mellin_criticalLine_eq_fourier c ((2 * Real.pi) * ξ)]
    congr 2
    field_simp [h2pi]
  rw [hleft] at hscale
  simpa [g, smul_eq_mul] using hscale

/-- D3.3 in the exact discovery-interface form. -/
theorem d3_fourierToMellinLine_realized :
    ∀ {N : ℕ} (c : Fin N → ℝ),
      (∫ ξ : ℝ, Complex.normSq (𝓕 (criticalLogPullback c) ξ)) =
        (1 / (2 * Real.pi)) *
          ∫ t : ℝ,
            Complex.normSq
              (mellin (residualRepresentativeC c) (criticalLinePoint t)) := by
  intro N c
  exact fourier_integral_eq_mellin_line c

#print axioms MCore.RH.R0.mellin_criticalLine_eq_fourier
#print axioms MCore.RH.R0.fourier_integral_eq_mellin_line
#print axioms MCore.RH.R0.d3_fourierToMellinLine_realized

end MCore.RH.R0
