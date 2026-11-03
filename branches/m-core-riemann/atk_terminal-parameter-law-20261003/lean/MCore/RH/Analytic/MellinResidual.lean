import MCore.RH.Analytic.MellinStripConvergence
import MCore.RH.Analytic.MellinRhoClosedForm
import MCore.RH.Analytic.MellinTarget

open scoped BigOperators

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- Finite Dirichlet polynomial attached to concrete coefficients. -/
noncomputable def concreteDirichletPolynomial
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ) : ℂ :=
  ∑ i : Fin N,
    (c i : ℂ) * (((rhoIndex i : ℕ) : ℂ) ^ (-s))

/-- Literal complex representative of the finite residual chi - sum c_i rho_i. -/
noncomputable def residualRepresentativeC
    {N : ℕ} (c : Fin N → ℝ) (x : ℝ) : ℂ :=
  chiRepresentativeC x -
    ∑ i : Fin N, (c i : ℂ) * rhoRepresentativeC i x

/-- Mellin convergence of a finite concrete generator combination. -/
theorem finiteGeneratorSum_mellinConvergent
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent
      (fun x : ℝ => ∑ i : Fin N, (c i : ℂ) * rhoRepresentativeC i x) s := by
  rw [MellinConvergent]
  have hi : ∀ i : Fin N,
      IntegrableOn
        (fun x : ℝ =>
          (x : ℂ) ^ (s - 1) •
            ((c i : ℂ) * rhoRepresentativeC i x))
        (Ioi 0) := by
    intro i
    have h := (rho_mellinConvergent i s hs0 hs1).const_smul (c i : ℂ)
    simpa [MellinConvergent, smul_eq_mul, mul_assoc] using h
  simpa [Finset.smul_sum, smul_eq_mul, mul_assoc] using
    (integral_finsetSum Finset.univ (fun i _ => hi i))

/-- Mellin transform commutes with the finite concrete generator sum. -/
theorem mellin_finiteGeneratorSum
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin
      (fun x : ℝ => ∑ i : Fin N, (c i : ℂ) * rhoRepresentativeC i x) s =
      ∑ i : Fin N, (c i : ℂ) * mellin (rhoRepresentativeC i) s := by
  unfold mellin
  have hi : ∀ i : Fin N,
      IntegrableOn
        (fun x : ℝ =>
          (x : ℂ) ^ (s - 1) *
            ((c i : ℂ) * rhoRepresentativeC i x))
        (Ioi 0) := by
    intro i
    have h := (rho_mellinConvergent i s hs0 hs1).const_smul (c i : ℂ)
    simpa [MellinConvergent, smul_eq_mul, mul_assoc] using h
  rw [show
      (fun x : ℝ =>
        (x : ℂ) ^ (s - 1) •
          (∑ i : Fin N, (c i : ℂ) * rhoRepresentativeC i x)) =
      (fun x : ℝ => ∑ i : Fin N,
        (x : ℂ) ^ (s - 1) *
          ((c i : ℂ) * rhoRepresentativeC i x)) by
        funext x; simp [smul_eq_mul, Finset.mul_sum]]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hiMem
  rw [← integral_const_mul]
  rfl

/-- Mellin convergence of the finite residual on the open strip. -/
theorem residual_mellinConvergent
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (residualRepresentativeC c) s := by
  unfold residualRepresentativeC
  have hchi := chi_mellinConvergent s hs0
  have hsum := finiteGeneratorSum_mellinConvergent c s hs0 hs1
  simpa only [MellinConvergent, smul_sub] using hchi.sub hsum

/-- D3 algebraic core: exact Mellin transform of the residual. -/
theorem mellin_residual_closed_form
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (residualRepresentativeC c) s =
      (1 + riemannZeta s * concreteDirichletPolynomial c s) / s := by
  have hchi := chi_mellinConvergent s hs0
  have hsum := finiteGeneratorSum_mellinConvergent c s hs0 hs1
  have hsub := hasMellin_sub hchi hsum
  have hsumM := mellin_finiteGeneratorSum c s hs0 hs1
  rw [show mellin (residualRepresentativeC c) s =
      mellin chiRepresentativeC s -
        mellin (fun x : ℝ => ∑ i : Fin N,
          (c i : ℂ) * rhoRepresentativeC i x) s by
      exact hsub.2]
  rw [mellin_chiRepresentativeC s hs0, hsumM]
  simp_rw [mellin_rho_realized _ s hs0 hs1]
  unfold concreteDirichletPolynomial
  have hsne : s ≠ 0 := ne_zero_of_re_pos hs0
  field_simp [hsne]
  ring

#print axioms MCore.RH.R0.finiteGeneratorSum_mellinConvergent
#print axioms MCore.RH.R0.residual_mellinConvergent
#print axioms MCore.RH.R0.mellin_residual_closed_form

end MCore.RH.R0
