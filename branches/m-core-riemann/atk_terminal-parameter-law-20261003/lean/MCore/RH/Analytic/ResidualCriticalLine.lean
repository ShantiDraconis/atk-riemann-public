import MCore.RH.Analytic.ResidualMellin

namespace MCore.RH.R0

open Complex

/-- The critical-line parameter used by the Plancherel reduction. -/
noncomputable def criticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℝ) + t * I

@[simp] theorem criticalLinePoint_re (t : ℝ) :
    (criticalLinePoint t).re = 1 / 2 := by
  simp [criticalLinePoint]

@[simp] theorem criticalLinePoint_im (t : ℝ) :
    (criticalLinePoint t).im = t := by
  simp [criticalLinePoint]

theorem criticalLinePoint_ne_zero (t : ℝ) :
    criticalLinePoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [criticalLinePoint] at hre

/-- Exact Mellin residual formula on the critical line. -/
theorem mellin_residual_criticalLine
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    mellin (residualRepresentativeC c) (criticalLinePoint t) =
      (1 + riemannZeta (criticalLinePoint t) *
        residualDirichletPolynomial c (criticalLinePoint t)) /
        criticalLinePoint t := by
  apply mellin_residual_closed_form
  · norm_num [criticalLinePoint]
  · norm_num [criticalLinePoint]

/-- The critical-line denominator has the expected squared norm. -/
theorem normSq_criticalLinePoint (t : ℝ) :
    ‖criticalLinePoint t‖ ^ 2 = 1 / 4 + t ^ 2 := by
  rw [Complex.sq_norm]
  simp [criticalLinePoint]
  ring

/-- Spectral density appearing in D3 after substituting the residual Mellin formula. -/
noncomputable def residualSpectralDensity
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : ℝ :=
  ‖1 + riemannZeta (criticalLinePoint t) *
      residualDirichletPolynomial c (criticalLinePoint t)‖ ^ 2 /
    (1 / 4 + t ^ 2)

/-- Pointwise squared-norm form of the D3 integrand. -/
theorem normSq_mellin_residual_criticalLine
    {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    ‖mellin (residualRepresentativeC c) (criticalLinePoint t)‖ ^ 2 =
      residualSpectralDensity c t := by
  rw [mellin_residual_criticalLine]
  rw [norm_div, div_pow, normSq_criticalLinePoint]
  rfl

#print axioms MCore.RH.R0.mellin_residual_criticalLine
#print axioms MCore.RH.R0.normSq_mellin_residual_criticalLine

end MCore.RH.R0
