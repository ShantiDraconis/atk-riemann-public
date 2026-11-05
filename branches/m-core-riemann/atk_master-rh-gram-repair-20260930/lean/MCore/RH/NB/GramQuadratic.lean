import MCore.RH.NB.CoefficientEndpoint
import MCore.RH.NB.GramNormalEquations

open scoped BigOperators

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- Unsymmetrized exact quadratic form of the finite coefficient error. -/
noncomputable def gramQuadraticError
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) : ℝ :=
  ‖D.chi‖ ^ 2
    - (∑ i : Fin N, c i * @inner ℝ D.H _ D.chi (rho i))
    - (∑ i : Fin N, c i * @inner ℝ D.H _ (rho i) D.chi)
    + (∑ i : Fin N, ∑ j : Fin N,
        c i * c j * @inner ℝ D.H _ (rho i) (rho j))

/-- Exact Hilbert-space expansion of the squared approximation error. -/
theorem coefficient_error_sq_eq_gramQuadraticError
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) :
    ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 =
      D.gramQuadraticError rho N c := by
  rw [← real_inner_self_eq_norm_sq]
  simp [gramQuadraticError, coefficientApproximantAt,
    inner_sub_sub_self, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm,
    Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/-- Symmetric Gram form matching the numerical engine: ||chi||^2 - 2 b^T c + c^T G c. -/
noncomputable def symmetricGramEnergy
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) : ℝ :=
  ‖D.chi‖ ^ 2
    - 2 * (∑ i : Fin N, c i * @inner ℝ D.H _ D.chi (rho i))
    + (∑ i : Fin N, ∑ j : Fin N,
        c i * c j * @inner ℝ D.H _ (rho i) (rho j))

/-- Over the real Hilbert space, the unsymmetrized and symmetric energies coincide. -/
theorem gramQuadraticError_eq_symmetricGramEnergy
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) :
    D.gramQuadraticError rho N c = D.symmetricGramEnergy rho N c := by
  have hcomm :
      (∑ i : Fin N, c i * @inner ℝ D.H _ (rho i) D.chi) =
      (∑ i : Fin N, c i * @inner ℝ D.H _ D.chi (rho i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm (rho i) D.chi]
  unfold gramQuadraticError symmetricGramEnergy
  rw [hcomm]
  ring

/-- Direct exact identity in the same quadratic form used by the Gram engine. -/
theorem coefficient_error_sq_eq_symmetricGramEnergy
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) :
    ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 =
      D.symmetricGramEnergy rho N c := by
  rw [D.coefficient_error_sq_eq_gramQuadraticError rho N c,
      D.gramQuadraticError_eq_symmetricGramEnergy rho N c]

/-- The canonical finite defect DN_N is attained by the symmetric Gram energy. -/
theorem exists_coefficients_realizing_DN_as_gram_energy
    (rho : D.GeneratorFamily) (N : ℕ) :
    ∃ c : Fin N → ℝ,
      D.symmetricGramEnergy rho N c = D.DN rho N := by
  rcases D.exists_optimal_coefficients_DN rho N with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  calc
    D.symmetricGramEnergy rho N c =
        ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 :=
      (D.coefficient_error_sq_eq_symmetricGramEnergy rho N c).symm
    _ = D.DN rho N := hc

/-- DN_N is the global minimum value of the finite symmetric Gram energy. -/
theorem DN_le_symmetricGramEnergy
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) :
    D.DN rho N ≤ D.symmetricGramEnergy rho N c := by
  rw [← D.coefficient_error_sq_eq_symmetricGramEnergy rho N c]
  exact D.DN_le_coefficient_error_sq rho N c

#print axioms coefficient_error_sq_eq_gramQuadraticError
#print axioms gramQuadraticError_eq_symmetricGramEnergy
#print axioms coefficient_error_sq_eq_symmetricGramEnergy
#print axioms exists_coefficients_realizing_DN_as_gram_energy
#print axioms DN_le_symmetricGramEnergy

end NBHilbertData
end MCore.RH.NB
