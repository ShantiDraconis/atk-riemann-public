import MCore.RH.Analytic.MellinPlancherelReduction
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.FourierTransform

namespace MCore.RH.R0

open MeasureTheory Set Complex
open MCore.RH.NB

/-- Logarithmic pullback that converts critical-line Mellin into Fourier. -/
noncomputable def criticalLogPullback
    {N : ℕ} (c : Fin N → ℝ) (u : ℝ) : ℂ :=
  Real.exp (-((1 / 2 : ℝ) * u)) •
    residualRepresentativeC c (Real.exp (-u))

/-- D3.0: real Hilbert residual norm equals the literal complex representative L2 integral. -/
def D3_ResidualRepresentativeNormBridge : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℝ),
    ‖concreteNBData.chi -
      concreteNBData.coefficientApproximantAt
        concreteGeneratorFamily N c‖ ^ 2 =
      ∫ x : ℝ in Ioi 0,
        Complex.normSq (residualRepresentativeC c x)

/-- D3.1: x=e^{-u} converts dx to e^{-u}du, exactly absorbed by the half-weight. -/
def D3_LogPullbackNormBridge : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℝ),
    (∫ x : ℝ in Ioi 0,
      Complex.normSq (residualRepresentativeC c x)) =
    ∫ u : ℝ, Complex.normSq (criticalLogPullback c u)

/-- D3.2: Plancherel for the logarithmic pullback. -/
def D3_FourierPlancherelBridge : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℝ),
    (∫ u : ℝ, Complex.normSq (criticalLogPullback c u)) =
    ∫ y : ℝ, Complex.normSq (𝓕 (criticalLogPullback c) y)

/-- D3.3: reparameterize Fourier frequency y=t/(2π). -/
def D3_FrequencyRescaleBridge : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℝ),
    (∫ y : ℝ, Complex.normSq (𝓕 (criticalLogPullback c) y)) =
    (1 / (2 * Real.pi)) *
      ∫ t : ℝ,
        Complex.normSq (𝓕 (criticalLogPullback c) (t / (2 * Real.pi)))

/-- Mathlib already gives the pointwise Mellin/Fourier identification. -/
theorem criticalLine_mellin_eq_fourier
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    mellin (residualRepresentativeC c) (criticalLine t) =
      𝓕 (criticalLogPullback c) (t / (2 * Real.pi)) := by
  simpa [criticalLine, criticalLogPullback, mul_comm, mul_left_comm, mul_assoc]
    using (mellin_eq_fourierIntegral
      (residualRepresentativeC c)
      (s := criticalLine t))

/-- The four local bridges imply the single D3 critical-line producer. -/
theorem criticalLineMellinPlancherel_of_components
    (h0 : D3_ResidualRepresentativeNormBridge)
    (h1 : D3_LogPullbackNormBridge)
    (h2 : D3_FourierPlancherelBridge)
    (h3 : D3_FrequencyRescaleBridge) :
    CriticalLineMellinPlancherel := by
  intro N c
  calc
    ‖concreteNBData.chi -
      concreteNBData.coefficientApproximantAt
        concreteGeneratorFamily N c‖ ^ 2
        = ∫ x : ℝ in Ioi 0,
            Complex.normSq (residualRepresentativeC c x) := h0 N c
    _ = ∫ u : ℝ, Complex.normSq (criticalLogPullback c u) := h1 N c
    _ = ∫ y : ℝ, Complex.normSq (𝓕 (criticalLogPullback c) y) := h2 N c
    _ = (1 / (2 * Real.pi)) *
          ∫ t : ℝ,
            Complex.normSq (𝓕 (criticalLogPullback c) (t / (2 * Real.pi))) :=
          h3 N c
    _ = (1 / (2 * Real.pi)) *
          ∫ t : ℝ,
            Complex.normSq
              (mellin (residualRepresentativeC c) (criticalLine t)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with t
          rw [criticalLine_mellin_eq_fourier c t]

#print axioms MCore.RH.R0.criticalLine_mellin_eq_fourier
#print axioms MCore.RH.R0.criticalLineMellinPlancherel_of_components

end MCore.RH.R0
