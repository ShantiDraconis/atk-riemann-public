import MCore.RH.Analytic.MellinResidual
import MCore.RH.NB.GramEnergy
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.MellinInversion

namespace MCore.RH.R0

open MCore.RH.NB
open MeasureTheory Set Complex

/-- Critical-line parameterization used by the Mellin--Plancherel identity. -/
noncomputable def criticalLinePoint (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)

/-- Logarithmic pullback at the critical exponent Re(s)=1/2. -/
noncomputable def criticalLogPullback
    {N : ℕ} (c : Fin N → ℝ) (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) *
    residualRepresentativeC c (Real.exp (-u))

/-- Residual vector in the frozen real L2 carrier. -/
noncomputable def concreteResidual
    {N : ℕ} (c : Fin N → ℝ) : concreteNBData.H :=
  concreteNBData.chi -
    concreteNBData.coefficientApproximantAt concreteGeneratorFamily N c

/--
The only genuinely Plancherel-specific bridge in D3.  Everything on the
right is already a concrete Mellin transform of the literal residual.
-/
def CriticalLineMellinPlancherel : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    ‖concreteResidual c‖ ^ 2 =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          Complex.normSq
            (mellin (residualRepresentativeC c) (criticalLinePoint t))

/-- The critical-line residual Mellin value is completely explicit. -/
theorem mellin_residual_criticalLine
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    mellin (residualRepresentativeC c) (criticalLinePoint t) =
      (1 + riemannZeta (criticalLinePoint t) *
        concreteDirichletPolynomial c (criticalLinePoint t)) /
      (criticalLinePoint t) := by
  apply mellin_residualRepresentativeC c (criticalLinePoint t)
  · norm_num [criticalLinePoint]
  · norm_num [criticalLinePoint]

/-- Norm-square of a critical-line point. -/
theorem criticalLinePoint_normSq (t : ℝ) :
    Complex.normSq (criticalLinePoint t) = (1 / 4 : ℝ) + t ^ 2 := by
  simp [criticalLinePoint, mul_comm, Complex.normSq_add_mul_I]
  ring

/-- Pointwise explicit D3 integrand. -/
theorem residualMellinNormSq_explicit
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    Complex.normSq
      (mellin (residualRepresentativeC c) (criticalLinePoint t)) =
      Complex.normSq
        (1 + riemannZeta (criticalLinePoint t) *
          concreteDirichletPolynomial c (criticalLinePoint t)) /
        ((1 / 4 : ℝ) + t ^ 2) := by
  rw [mellin_residual_criticalLine c t]
  rw [Complex.normSq_div]
  rw [criticalLinePoint_normSq]

/-- D3 follows from the sole Plancherel bridge plus the explicit residual Mellin formula. -/
theorem residual_mellin_plancherel_explicit
    (hP : CriticalLineMellinPlancherel)
    {N : ℕ} (c : Fin N → ℝ) :
    ‖concreteResidual c‖ ^ 2 =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          Complex.normSq
            (1 + riemannZeta (criticalLinePoint t) *
              concreteDirichletPolynomial c (criticalLinePoint t)) /
            ((1 / 4 : ℝ) + t ^ 2) := by
  rw [hP c]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact residualMellinNormSq_explicit c t

#print axioms MCore.RH.R0.mellin_residual_criticalLine
#print axioms MCore.RH.R0.residualMellinNormSq_explicit
#print axioms MCore.RH.R0.residual_mellin_plancherel_explicit

end MCore.RH.R0
