import MCore.RH.Analytic.MellinStripConvergence
import MCore.RH.Analytic.MellinRhoClosedForm
import MCore.RH.Analytic.MellinTarget

open scoped BigOperators

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- Complex finite Nyman--Beurling combination attached to real coefficients. -/
noncomputable def complexFiniteCombination
    {N : ℕ} (c : Fin N → ℝ) (x : ℝ) : ℂ :=
  ∑ i : Fin N, (c i : ℂ) * rhoRepresentativeC i x

/-- Finite Dirichlet polynomial carried by the concrete coefficient vector. -/
noncomputable def residualDirichletPolynomial
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ) : ℂ :=
  ∑ i : Fin N, (c i : ℂ) * (((rhoIndex i : ℕ) : ℂ) ^ (-s))

/-- Literal complex residual chi - sum c_i rho_i. -/
noncomputable def residualRepresentativeC
    {N : ℕ} (c : Fin N → ℝ) (x : ℝ) : ℂ :=
  chiRepresentativeC x - complexFiniteCombination c x

/-- Every finite complex generator combination is Mellin-convergent on the critical strip. -/
theorem complexFiniteCombination_mellinConvergent
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (complexFiniteCombination c) s := by
  classical
  unfold complexFiniteCombination
  have h : ∀ S : Finset (Fin N),
      MellinConvergent
        (fun x : ℝ => ∑ i ∈ S, (c i : ℂ) * rhoRepresentativeC i x) s := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simp [MellinConvergent]
    | @insert a S ha ih =>
        have haConv :
            MellinConvergent
              (fun x : ℝ => (c a : ℂ) * rhoRepresentativeC a x) s := by
          simpa [smul_eq_mul] using
            (rhoRepresentativeC_mellinConvergent a s hs0 hs1).const_smul (c a : ℂ)
        have hadd := (hasMellin_add haConv ih).1
        simpa [Finset.sum_insert ha, add_comm, add_left_comm, add_assoc] using hadd
  simpa using h Finset.univ

/-- Mellin transform of the finite concrete combination. -/
theorem mellin_complexFiniteCombination
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (complexFiniteCombination c) s =
      - (riemannZeta s / s) * residualDirichletPolynomial c s := by
  classical
  unfold complexFiniteCombination residualDirichletPolynomial
  have h : ∀ S : Finset (Fin N),
      mellin (fun x : ℝ => ∑ i ∈ S, (c i : ℂ) * rhoRepresentativeC i x) s =
        - (riemannZeta s / s) *
          ∑ i ∈ S, (c i : ℂ) * (((rhoIndex i : ℕ) : ℂ) ^ (-s)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simp [mellin]
    | @insert a S ha ih =>
        have haConv :
            MellinConvergent
              (fun x : ℝ => (c a : ℂ) * rhoRepresentativeC a x) s := by
          simpa [smul_eq_mul] using
            (rhoRepresentativeC_mellinConvergent a s hs0 hs1).const_smul (c a : ℂ)
        have hSConv :
            MellinConvergent
              (fun x : ℝ => ∑ i ∈ S, (c i : ℂ) * rhoRepresentativeC i x) s := by
          have hall := complexFiniteCombination_mellinConvergent
            (N := N) c s hs0 hs1
          -- recover the restricted finite-sum convergence directly
          induction S using Finset.induction_on with
          | empty => simp [MellinConvergent]
          | @insert b T hb hT =>
              have hbConv :
                  MellinConvergent
                    (fun x : ℝ => (c b : ℂ) * rhoRepresentativeC b x) s := by
                simpa [smul_eq_mul] using
                  (rhoRepresentativeC_mellinConvergent b s hs0 hs1).const_smul (c b : ℂ)
              exact by
                have := (hasMellin_add hbConv hT).1
                simpa [Finset.sum_insert hb, add_comm, add_left_comm, add_assoc] using this
        have hadd := (hasMellin_add haConv hSConv).2
        rw [mellin_const_smul] at hadd
        rw [mellin_rho_realized a s hs0 hs1] at hadd
        rw [ih] at hadd
        simpa [Finset.sum_insert ha, smul_eq_mul] using hadd
  simpa using h Finset.univ

/-- The concrete residual is Mellin-convergent on the critical strip. -/
theorem residualRepresentativeC_mellinConvergent
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (residualRepresentativeC c) s := by
  unfold residualRepresentativeC
  exact (hasMellin_sub
    (chiRepresentativeC_mellinConvergent s hs0 hs1)
    (complexFiniteCombination_mellinConvergent c s hs0 hs1)).1

/-- D3 algebraic half: exact Mellin formula for the residual. -/
theorem mellin_residual_closed_form
    {N : ℕ} (c : Fin N → ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (residualRepresentativeC c) s =
      (1 + riemannZeta s * residualDirichletPolynomial c s) / s := by
  unfold residualRepresentativeC
  have hsub := (hasMellin_sub
    (chiRepresentativeC_mellinConvergent s hs0 hs1)
    (complexFiniteCombination_mellinConvergent c s hs0 hs1)).2
  rw [mellin_chiRepresentativeC s hs0] at hsub
  rw [mellin_complexFiniteCombination c s hs0 hs1] at hsub
  rw [hsub]
  have hsne : s ≠ 0 := ne_zero_of_re_pos hs0
  field_simp [hsne]
  ring

#print axioms MCore.RH.R0.complexFiniteCombination_mellinConvergent
#print axioms MCore.RH.R0.mellin_complexFiniteCombination
#print axioms MCore.RH.R0.mellin_residual_closed_form

end MCore.RH.R0
