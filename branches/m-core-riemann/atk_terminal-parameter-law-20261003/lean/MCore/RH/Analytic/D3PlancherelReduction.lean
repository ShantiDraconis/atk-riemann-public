import MCore.RH.Analytic.ResidualMellin
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.LpSpace

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- Critical line parameterization used by the residual Plancherel identity. -/
noncomputable def criticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * I

/--
The only genuinely Hilbert-analytic producer left in D3:
Mellin Plancherel on the critical line, in the exact normalization induced by
Mathlib's Fourier transform convention.
-/
def CriticalLineMellinPlancherel : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    (∫ x : ℝ in Ioi 0, ‖residualRepresentativeC c x‖ ^ 2) =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ, ‖mellin (residualRepresentativeC c) (criticalLinePoint t)‖ ^ 2

/-- Every critical-line point lies in the open Mellin strip. -/
theorem criticalLinePoint_re (t : ℝ) :
    (criticalLinePoint t).re = 1 / 2 := by
  simp [criticalLinePoint]

theorem criticalLinePoint_strip (t : ℝ) :
    0 < (criticalLinePoint t).re ∧
      (criticalLinePoint t).re < 1 := by
  rw [criticalLinePoint_re]
  constructor <;> norm_num

/-- Pointwise D3 spectral integrand obtained from the closed residual Mellin formula. -/
theorem residual_mellin_critical_line
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    mellin (residualRepresentativeC c) (criticalLinePoint t) =
      (1 + riemannZeta (criticalLinePoint t) *
        residualDirichletPolynomial c (criticalLinePoint t)) /
      criticalLinePoint t := by
  rcases criticalLinePoint_strip t with ⟨h0, h1⟩
  exact mellin_residual_closed_form c (criticalLinePoint t) h0 h1

/-- The denominator on the critical line has squared norm 1/4+t^2. -/
theorem criticalLinePoint_norm_sq (t : ℝ) :
    Complex.normSq (criticalLinePoint t) = (1 / 4 : ℝ) + t ^ 2 := by
  simp [criticalLinePoint, Complex.normSq_apply, pow_two]
  ring

/-- Squared norm of the residual Mellin transform in fully explicit zeta form. -/
theorem residual_mellin_norm_sq_critical_line
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    ‖mellin (residualRepresentativeC c) (criticalLinePoint t)‖ ^ 2 =
      Complex.normSq
        (1 + riemannZeta (criticalLinePoint t) *
          residualDirichletPolynomial c (criticalLinePoint t)) /
        ((1 / 4 : ℝ) + t ^ 2) := by
  rw [residual_mellin_critical_line c t]
  rw [Complex.sq_norm, Complex.normSq_div, criticalLinePoint_norm_sq]

/--
Once critical-line Mellin Plancherel is supplied, D3 becomes a direct rewrite:
no zeta algebra remains hidden.
-/
theorem residual_plancherel_explicit
    (hP : CriticalLineMellinPlancherel)
    {N : ℕ} (c : Fin N → ℝ) :
    (∫ x : ℝ in Ioi 0, ‖residualRepresentativeC c x‖ ^ 2) =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          Complex.normSq
            (1 + riemannZeta (criticalLinePoint t) *
              residualDirichletPolynomial c (criticalLinePoint t)) /
            ((1 / 4 : ℝ) + t ^ 2) := by
  rw [hP c]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact residual_mellin_norm_sq_critical_line c t

#print axioms MCore.RH.R0.residual_mellin_critical_line
#print axioms MCore.RH.R0.residual_plancherel_explicit

end MCore.RH.R0
