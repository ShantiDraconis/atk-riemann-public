import MCore.RH.Analytic.MellinResidual
import MCore.RH.R0.GramInverse

namespace MCore.RH.R0

open Complex MeasureTheory

/-- Critical-line parameter. -/
noncomputable def criticalLine (t : ℝ) : ℂ :=
  (1 / 2 : ℝ) + Complex.I * t

/-- Spectral residual density predicted by Mellin-Plancherel. -/
noncomputable def residualSpectralDensity
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : ℝ :=
  Complex.normSq
    (1 + riemannZeta (criticalLine t) *
      concreteDirichletPolynomial c (criticalLine t)) /
    ((1 / 4 : ℝ) + t ^ 2)

/-- Exact Plancherel bridge still needed for D3. -/
def ResidualMellinPlancherelBridge : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    ‖concreteNBData.chi - concreteFiniteCombination c‖ ^ 2 =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ, residualSpectralDensity c t

/-- D3 is exactly the single Mellin-Plancherel bridge. -/
theorem d3_of_residualMellinPlancherel
    (h : ResidualMellinPlancherelBridge)
    {N : ℕ} (c : Fin N → ℝ) :
    ‖concreteNBData.chi - concreteFiniteCombination c‖ ^ 2 =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          Complex.normSq
            (1 + riemannZeta (criticalLine t) *
              concreteDirichletPolynomial c (criticalLine t)) /
            ((1 / 4 : ℝ) + t ^ 2) := by
  exact h c

/-- Pointwise critical-line residual formula from D1 + D2. -/
theorem mellin_residual_on_critical_line
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    mellin (concreteResidualC c) (criticalLine t) =
      (1 + riemannZeta (criticalLine t) *
        concreteDirichletPolynomial c (criticalLine t)) /
      (criticalLine t) := by
  have hs0 : 0 < (criticalLine t).re := by
    simp [criticalLine]
  have hs1 : (criticalLine t).re < 1 := by
    simp [criticalLine]
  exact mellin_concreteResidualC c (criticalLine t) hs0 hs1

/-- Denominator on the critical line is exactly 1/4+t^2. -/
theorem criticalLine_normSq (t : ℝ) :
    Complex.normSq (criticalLine t) = (1 / 4 : ℝ) + t ^ 2 := by
  simp [criticalLine, Complex.normSq_apply]
  ring

#print axioms MCore.RH.R0.mellin_residual_on_critical_line
#print axioms MCore.RH.R0.criticalLine_normSq
#print axioms MCore.RH.R0.d3_of_residualMellinPlancherel

end MCore.RH.R0
