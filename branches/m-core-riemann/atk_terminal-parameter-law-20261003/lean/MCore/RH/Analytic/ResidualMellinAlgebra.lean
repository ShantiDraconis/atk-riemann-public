import MCore.RH.Analytic.MellinStripConvergence
import MCore.RH.Analytic.MellinRhoClosedForm
import MCore.RH.Analytic.MellinTarget

open scoped BigOperators

namespace MCore.RH.R0

open Complex MeasureTheory Set

/-- Canonical finite Dirichlet polynomial attached to coefficient vector c. -/
noncomputable def concreteDirichletPolynomial
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ) : ℂ :=
  ∑ i : Fin N,
    (c i : ℂ) * (((rhoIndex i : ℕ) : ℂ) ^ (-s))

/-- Complex representative of the finite rho combination. -/
noncomputable def concreteCombinationC
    {N : ℕ} (c : Fin N → ℝ) (x : ℝ) : ℂ :=
  ∑ i : Fin N, (c i : ℂ) * rhoRepresentativeC i x

/-- Complex residual representative chi - sum c_i rho_i. -/
noncomputable def concreteResidualC
    {N : ℕ} (c : Fin N → ℝ) (x : ℝ) : ℂ :=
  chiRepresentativeC x - concreteCombinationC c x

/-- Mellin convergence of the finite rho combination on 0<Re(s)<1. -/
theorem concreteCombinationC_mellinConvergent
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (concreteCombinationC c) s := by
  classical
  unfold concreteCombinationC
  apply integrable_finsetSum
  intro i hi
  simpa [MellinConvergent, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    (rhoRepresentativeC_mellinConvergent i s hs0 hs1).const_smul (c i : ℂ)

/-- Mellin transform of the finite rho combination. -/
theorem mellin_concreteCombinationC
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (concreteCombinationC c) s =
      - riemannZeta s / s * concreteDirichletPolynomial c s := by
  classical
  unfold concreteCombinationC concreteDirichletPolynomial
  rw [mellin]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← mellin]
    rw [mellin_const_smul]
    rw [mellin_rho_realized i s hs0 hs1]
    simp only [smul_eq_mul]
    ring
  · intro i hi
    simpa [MellinConvergent, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (rhoRepresentativeC_mellinConvergent i s hs0 hs1).const_smul (c i : ℂ)

/-- Mellin convergence of the concrete residual. -/
theorem concreteResidualC_mellinConvergent
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (concreteResidualC c) s := by
  unfold concreteResidualC
  exact (hasMellin_sub
    (chiRepresentativeC_mellinConvergent s hs0 hs1)
    (concreteCombinationC_mellinConvergent c s hs0 hs1)).1

/-- D3 algebraic half: exact pointwise Mellin formula for the residual. -/
theorem mellin_concreteResidualC
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (concreteResidualC c) s =
      (1 + riemannZeta s * concreteDirichletPolynomial c s) / s := by
  unfold concreteResidualC
  have hsub := (hasMellin_sub
    (chiRepresentativeC_mellinConvergent s hs0 hs1)
    (concreteCombinationC_mellinConvergent c s hs0 hs1)).2
  rw [hsub]
  rw [mellin_chiRepresentativeC s hs0]
  rw [mellin_concreteCombinationC c s hs0 hs1]
  have hsne : s ≠ 0 := ne_zero_of_re_pos hs0
  field_simp [hsne]
  ring

#print axioms MCore.RH.R0.mellin_concreteCombinationC
#print axioms MCore.RH.R0.mellin_concreteResidualC

end MCore.RH.R0
