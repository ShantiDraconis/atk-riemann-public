import MCore.RH.Analytic.MellinPlancherelReduction
import Mathlib.Analysis.MellinInversion

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- Logarithmic pullback used to convert Mellin on Re(s)=1/2 into Fourier. -/
noncomputable def residualLogTransform
    {N : ℕ} (c : Fin N → ℝ) (u : ℝ) : ℂ :=
  Real.exp (-(1 / 2 : ℝ) * u) *
    residualRepresentativeC c (Real.exp (-u))

/-- Change of variables x = exp(-u): exact L2 isometry between dx and du models. -/
def ResidualLogL2Isometry : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    (∫ x : ℝ in Ioi 0, Complex.normSq (residualRepresentativeC c x)) =
      ∫ u : ℝ, Complex.normSq (residualLogTransform c u)

/-- Fourier Plancherel for the logarithmic residual transform. -/
def ResidualFourierPlancherel : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    (∫ u : ℝ, Complex.normSq (residualLogTransform c u)) =
      ∫ y : ℝ, Complex.normSq (𝓕 (residualLogTransform c) y)

/-- Mellin is the Fourier integral of the logarithmic pullback, with t/(2pi) normalization. -/
theorem residual_mellin_eq_fourierIntegral
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    mellin (residualRepresentativeC c) (criticalLinePoint t) =
      𝓕 (residualLogTransform c) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourierIntegral]
  unfold criticalLinePoint residualLogTransform
  congr 1
  funext u
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul,
    sub_zero, one_div, neg_mul]
  ring_nf

/-- Scaling y=t/(2pi) converts Fourier frequency measure to the critical-line measure. -/
def CriticalLineFrequencyScaling : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    (∫ t : ℝ,
      Complex.normSq (𝓕 (residualLogTransform c) (t / (2 * Real.pi)))) =
      (2 * Real.pi) *
        ∫ y : ℝ, Complex.normSq (𝓕 (residualLogTransform c) y)

/-- The frequency rescaling t = 2*pi*y is purely a Haar-measure change of variables. -/
theorem criticalLineFrequencyScaling_realized :
    CriticalLineFrequencyScaling := by
  intro N c
  let F : ℝ → ℝ := fun y =>
    Complex.normSq (𝓕 (residualLogTransform c) y)
  have h2pi : 0 < (2 * Real.pi : ℝ) := by positivity
  have hchange := Measure.integral_comp_mul_left F ((2 * Real.pi)⁻¹)
  change
    (∫ t : ℝ, F (t / (2 * Real.pi))) =
      (2 * Real.pi) * ∫ y : ℝ, F y
  convert hchange using 1
  · congr 1
    funext t
    simp [F, div_eq_mul_inv]
  · rw [abs_of_pos]
    · field_simp
    · positivity

/--
The original critical-line Mellin-Plancherel statement follows from exactly:
log-coordinate L2 isometry + Fourier Plancherel + frequency rescaling.
-/
theorem criticalLineMellinPlancherel_of_three_bridges
    (hlog : ResidualLogL2Isometry)
    (hfourier : ResidualFourierPlancherel)
    (hscale : CriticalLineFrequencyScaling) :
    CriticalLineMellinPlancherel := by
  intro N c
  rw [hlog c, hfourier c]
  have hs := hscale c
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [show
      (fun t : ℝ =>
        Complex.normSq
          (mellin (residualRepresentativeC c) (criticalLinePoint t))) =
      (fun t : ℝ =>
        Complex.normSq
          (𝓕 (residualLogTransform c) (t / (2 * Real.pi)))) by
      funext t
      rw [residual_mellin_eq_fourierIntegral c t]]
  rw [hs]
  field_simp
  ring

#print axioms MCore.RH.R0.residual_mellin_eq_fourierIntegral
#print axioms MCore.RH.R0.criticalLineFrequencyScaling_realized
#print axioms MCore.RH.R0.criticalLineMellinPlancherel_of_three_bridges

end MCore.RH.R0
