import MCore.RH.Analytic.ResidualMellinAlgebra
import Mathlib.Data.Complex.Norm

namespace MCore.RH.R0

open Complex MeasureTheory

/-- Critical-line parameter s = 1/2 + i t. -/
noncomputable def criticalLine (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)

@[simp] theorem criticalLine_re (t : ℝ) :
    (criticalLine t).re = 1 / 2 := by
  simp [criticalLine]

@[simp] theorem criticalLine_im (t : ℝ) :
    (criticalLine t).im = t := by
  simp [criticalLine]

theorem criticalLine_re_pos (t : ℝ) :
    0 < (criticalLine t).re := by
  simp [criticalLine]
  norm_num

theorem criticalLine_re_lt_one (t : ℝ) :
    (criticalLine t).re < 1 := by
  simp [criticalLine]
  norm_num

theorem criticalLine_normSq (t : ℝ) :
    Complex.normSq (criticalLine t) = 1 / 4 + t ^ 2 := by
  rw [criticalLine, mul_comm Complex.I (t : ℂ)]
  simpa [Complex.normSq_add_mul_I] using
    (Complex.normSq_add_mul_I (1 / 2 : ℝ) t)

/-- Pointwise critical-line Mellin formula for the residual. -/
theorem mellin_concreteResidualC_criticalLine
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    mellin (concreteResidualC c) (criticalLine t) =
      (1 + riemannZeta (criticalLine t) *
        concreteDirichletPolynomial c (criticalLine t)) /
        criticalLine t := by
  exact mellin_concreteResidualC c (criticalLine t)
    (criticalLine_re_pos t) (criticalLine_re_lt_one t)

/-- Squared-modulus form of the critical-line residual Mellin formula. -/
theorem normSq_mellin_concreteResidualC_criticalLine
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    Complex.normSq (mellin (concreteResidualC c) (criticalLine t)) =
      Complex.normSq
        (1 + riemannZeta (criticalLine t) *
          concreteDirichletPolynomial c (criticalLine t)) /
        (1 / 4 + t ^ 2) := by
  rw [mellin_concreteResidualC_criticalLine c t]
  rw [Complex.normSq_div, criticalLine_normSq]

/--
The remaining D3 functional-analytic producer: Mellin Plancherel on the critical line
for the concrete residual. The exact global normalization is fixed here and must be
proved from Mathlib's Fourier normalization, not assumed elsewhere.
-/
def MellinPlancherelResidual : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    ‖concreteNBData.chi - concreteFiniteCombination c‖ ^ 2 =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          Complex.normSq
            (mellin (concreteResidualC c) (criticalLine t))

/-- D3 follows immediately from the Plancherel producer plus the pointwise formula. -/
theorem d3_residual_identity_of_plancherel
    (hP : MellinPlancherelResidual)
    {N : ℕ} (c : Fin N → ℝ) :
    ‖concreteNBData.chi - concreteFiniteCombination c‖ ^ 2 =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          Complex.normSq
            (1 + riemannZeta (criticalLine t) *
              concreteDirichletPolynomial c (criticalLine t)) /
            (1 / 4 + t ^ 2) := by
  rw [hP c]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact normSq_mellin_concreteResidualC_criticalLine c t

#print axioms MCore.RH.R0.mellin_concreteResidualC_criticalLine
#print axioms MCore.RH.R0.normSq_mellin_concreteResidualC_criticalLine
#print axioms MCore.RH.R0.d3_residual_identity_of_plancherel

end MCore.RH.R0
