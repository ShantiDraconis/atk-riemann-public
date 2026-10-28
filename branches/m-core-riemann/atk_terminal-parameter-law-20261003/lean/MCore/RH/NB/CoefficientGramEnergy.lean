import MCore.RH.NB.CoefficientPythagoras

open scoped BigOperators

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- Finite Gram quadratic energy of a coefficient vector. -/
noncomputable def coefficientGramEnergy
    (rho : D.GeneratorFamily)
    (N : ℕ)
    (r : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    r i * r j * @inner ℝ D.H _ (rho i) (rho j)

/--
The Hilbert norm of a coefficient combination is exactly its Gram quadratic
form.  This is the finite-dimensional bridge needed for a Möbius-plus-correction
analysis.
-/
theorem norm_coefficientApproximant_sq_eq_gramEnergy
    (rho : D.GeneratorFamily)
    (N : ℕ)
    (r : Fin N → ℝ) :
    ‖D.coefficientApproximantAt rho N r‖ ^ 2 =
      D.coefficientGramEnergy rho N r := by
  rw [← real_inner_self_eq_norm_sq]
  unfold coefficientApproximantAt coefficientGramEnergy
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  congr 1
  funext i
  congr 1
  funext j
  rw [real_inner_comm (rho j) (rho i)]
  ring

/--
Difference of two coefficient approximants is itself the approximant of the
coefficient difference.
-/
theorem coefficientApproximantAt_sub
    (rho : D.GeneratorFamily)
    (N : ℕ)
    (c d : Fin N → ℝ) :
    D.coefficientApproximantAt rho N c -
      D.coefficientApproximantAt rho N d =
    D.coefficientApproximantAt rho N (fun i => c i - d i) := by
  unfold coefficientApproximantAt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [sub_smul]

/--
Therefore the squared Hilbert distance between two coefficient vectors is
exactly the Gram energy of their coefficient difference.
-/
theorem coefficient_distance_sq_eq_gramEnergy_difference
    (rho : D.GeneratorFamily)
    (N : ℕ)
    (c d : Fin N → ℝ) :
    ‖D.coefficientApproximantAt rho N c -
      D.coefficientApproximantAt rho N d‖ ^ 2 =
    D.coefficientGramEnergy rho N (fun i => c i - d i) := by
  rw [D.coefficientApproximantAt_sub rho N c d]
  exact D.norm_coefficientApproximant_sq_eq_gramEnergy rho N _

#print axioms MCore.RH.NB.NBHilbertData.norm_coefficientApproximant_sq_eq_gramEnergy
#print axioms MCore.RH.NB.NBHilbertData.coefficient_distance_sq_eq_gramEnergy_difference

end NBHilbertData
end MCore.RH.NB
