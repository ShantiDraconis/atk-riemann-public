import MCore.RH.NB.CoefficientEndpoint
import MCore.RH.NB.GramNormalEquations

open scoped BigOperators

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

noncomputable def gramEntry
    (rho : D.GeneratorFamily) {N : ℕ} (i j : Fin N) : ℝ :=
  @inner ℝ D.H _ (rho i) (rho j)

noncomputable def targetEntry
    (rho : D.GeneratorFamily) {N : ℕ} (i : Fin N) : ℝ :=
  @inner ℝ D.H _ D.chi (rho i)

noncomputable def coefficientEnergy
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) : ℝ :=
  ‖D.chi‖ ^ 2
    - 2 * (∑ i : Fin N, c i * D.targetEntry rho i)
    + ∑ i : Fin N, ∑ j : Fin N,
        c i * c j * D.gramEntry rho i j

theorem coefficient_error_sq_eq_energy
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) :
    ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 =
      D.coefficientEnergy rho N c := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_sub_self]
  simp only [coefficientApproximantAt, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  unfold coefficientEnergy targetEntry gramEntry
  rw [real_inner_self_eq_norm_sq]
  have hcross :
      (∑ i : Fin N, c i * @inner ℝ D.H _ (rho i) D.chi) =
      ∑ i : Fin N, c i * @inner ℝ D.H _ D.chi (rho i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
  have hgram :
      (∑ i : Fin N, ∑ j : Fin N,
        c i * (c j * @inner ℝ D.H _ (rho j) (rho i))) =
      ∑ i : Fin N, ∑ j : Fin N,
        c i * c j * @inner ℝ D.H _ (rho i) (rho j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm]
    ring
  rw [hcross, hgram]
  ring

theorem coefficientEnergy_of_normal_equations
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ)
    (hnormal :
      ∀ j : Fin N,
        (∑ i : Fin N, c i * D.gramEntry rho i j) =
          D.targetEntry rho j) :
    D.coefficientEnergy rho N c =
      ‖D.chi‖ ^ 2 - ∑ i : Fin N, c i * D.targetEntry rho i := by
  have hquad :
      (∑ i : Fin N, ∑ j : Fin N,
        c i * c j * D.gramEntry rho i j) =
      ∑ j : Fin N, c j * D.targetEntry rho j := by
    calc
      (∑ i : Fin N, ∑ j : Fin N,
        c i * c j * D.gramEntry rho i j)
          =
        ∑ j : Fin N, c j *
          (∑ i : Fin N, c i * D.gramEntry rho i j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ∑ j : Fin N, c j * D.targetEntry rho j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hnormal j]
  unfold coefficientEnergy
  rw [hquad]
  ring

theorem exists_optimal_coefficients_reduced_energy
    (rho : D.GeneratorFamily) (N : ℕ) :
    ∃ c : Fin N → ℝ,
      D.DN rho N =
        ‖D.chi‖ ^ 2 - ∑ i : Fin N, c i * D.targetEntry rho i ∧
      ∀ j : Fin N,
        (∑ i : Fin N, c i * D.gramEntry rho i j) =
          D.targetEntry rho j := by
  rcases D.exists_optimal_coefficients_DN_normal_equations rho N with
    ⟨c, herr, hnormal⟩
  refine ⟨c, ?_, ?_⟩
  · have henergy :
      D.coefficientEnergy rho N c = D.DN rho N := by
      rw [← D.coefficient_error_sq_eq_energy rho N c]
      exact herr
    have hreduced :=
      D.coefficientEnergy_of_normal_equations rho N c ?_
    · linarith
    · simpa [gramEntry, targetEntry] using hnormal
  · simpa [gramEntry, targetEntry] using hnormal

#print axioms coefficient_error_sq_eq_energy
#print axioms coefficientEnergy_of_normal_equations
#print axioms exists_optimal_coefficients_reduced_energy

end NBHilbertData
end MCore.RH.NB
