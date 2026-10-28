import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransform

namespace MCore.RH.R0

open MeasureTheory Complex Real
open scoped FourierTransform

/-- Frequency Gaussian in the pinned analyst Fourier normalization. -/
noncomputable def d3GaussianMultiplierReal (ε t : ℝ) : ℝ :=
  Real.exp (-Real.pi * ε * t ^ 2)

/-- Normalized spatial Gaussian K_ε(x)=ε^{-1/2} exp(-π x²/ε). -/
noncomputable def d3HeatKernelReal (ε x : ℝ) : ℝ :=
  ε⁻¹ ^ (1 / 2 : ℝ) * Real.exp (-Real.pi * x ^ 2 / ε)

/--
Complex form of the normalized heat kernel.  This form is chosen so that
the pinned Gaussian Fourier theorem applies literally.
-/
noncomputable def d3HeatKernelC (ε x : ℝ) : ℂ :=
  ((ε : ℂ)⁻¹ ^ (1 / 2 : ℂ)) *
    Complex.exp (-Real.pi * ((ε : ℂ)⁻¹) * (x : ℂ) ^ 2)

/-- The pinned Gaussian theorem gives the exact unnormalized Fourier transform. -/
theorem fourier_gaussian_inv_epsilon
    {ε : ℝ} (hε : 0 < ε) :
    (𝓕 fun x : ℝ =>
      Complex.exp (-Real.pi * ((ε : ℂ)⁻¹) * (x : ℂ) ^ 2))
      =
    fun t : ℝ =>
      1 / (((ε : ℂ)⁻¹) ^ (1 / 2 : ℂ)) *
        Complex.exp (-Real.pi / ((ε : ℂ)⁻¹) * (t : ℂ) ^ 2) := by
  have hinv_re : 0 < (((ε : ℂ)⁻¹)).re := by
    rw [Complex.inv_re]
    simp
    positivity
  simpa using
    (fourierIntegral_gaussian_pi (b := (ε : ℂ)⁻¹) hinv_re)

/-- Exact Fourier transform of the normalized complex heat kernel. -/
theorem fourier_d3HeatKernelC
    {ε : ℝ} (hε : 0 < ε) :
    𝓕 (d3HeatKernelC ε) =
      fun t : ℝ => Complex.exp (-Real.pi * (ε : ℂ) * (t : ℂ) ^ 2) := by
  funext t
  unfold d3HeatKernelC
  rw [Real.fourierIntegral_const_smul]
  rw [congr_fun (fourier_gaussian_inv_epsilon hε) t]
  have hεc : (ε : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hε
  have hinvcpow :
      ((ε : ℂ)⁻¹) ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero _ (inv_ne_zero hεc)
  field_simp [hinvcpow, hεc]
  congr 1
  field_simp [hεc]
  ring

/-- The complex Gaussian multiplier is the coercion of the real one. -/
theorem d3GaussianMultiplierReal_coe
    {ε t : ℝ} :
    (d3GaussianMultiplierReal ε t : ℂ) =
      Complex.exp (-Real.pi * (ε : ℂ) * (t : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp]
  congr 1
  norm_cast

#print axioms MCore.RH.R0.fourier_gaussian_inv_epsilon
#print axioms MCore.RH.R0.fourier_d3HeatKernelC
#print axioms MCore.RH.R0.d3GaussianMultiplierReal_coe

end MCore.RH.R0
