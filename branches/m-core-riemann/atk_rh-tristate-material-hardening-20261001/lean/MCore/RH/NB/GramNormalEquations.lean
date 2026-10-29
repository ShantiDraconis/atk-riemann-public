import MCore.RH.NB.CoefficientRealization

open scoped BigOperators

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
The projection coefficients satisfy the finite Gram normal equations exactly.
No invertibility of the Gram matrix is assumed: this is just orthogonality of
the Hilbert projection rewritten in coefficient coordinates.
-/
theorem exists_optimal_coefficients_normal_equations
    (rho : D.GeneratorFamily) (N : ℕ) :
    ∃ c : Fin N → ℝ,
      ‖D.chi - D.coefficientApproximantAt rho N c‖ = D.dN rho N ∧
      ∀ j : Fin N,
        (∑ i : Fin N,
          c i * @inner ℝ D.H _ (rho i) (rho j)) =
        @inner ℝ D.H _ D.chi (rho j) := by
  let p : D.V rho N := D.P rho N D.chi
  rcases D.exists_coefficients_of_mem_V rho N p with ⟨c, hc⟩
  refine ⟨c, ?_, ?_⟩
  · rw [hc]
    rfl
  · intro j
    have horth :
        @inner ℝ D.H _
          (D.chi - (p : D.H)) (rho j) = 0 := by
      dsimp [p]
      exact D.residual_inner_eq_zero rho N D.chi (rho j)
        (D.generator_mem_V rho N j)
    rw [← hc] at horth
    have h :
        @inner ℝ D.H _ D.chi (rho j) -
          (∑ i : Fin N,
            c i * @inner ℝ D.H _ (rho i) (rho j)) = 0 := by
      simpa [coefficientApproximantAt, inner_sub_left, sum_inner,
        real_inner_smul_left] using horth
    linarith

/--
Squared optimality and the Gram normal equations are simultaneously realized
by one finite coefficient vector.
-/
theorem exists_optimal_coefficients_DN_normal_equations
    (rho : D.GeneratorFamily) (N : ℕ) :
    ∃ c : Fin N → ℝ,
      ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 = D.DN rho N ∧
      ∀ j : Fin N,
        (∑ i : Fin N,
          c i * @inner ℝ D.H _ (rho i) (rho j)) =
        @inner ℝ D.H _ D.chi (rho j) := by
  rcases D.exists_optimal_coefficients_normal_equations rho N with
    ⟨c, herr, hnormal⟩
  refine ⟨c, ?_, hnormal⟩
  unfold DN
  rw [herr]

#print axioms exists_optimal_coefficients_normal_equations
#print axioms exists_optimal_coefficients_DN_normal_equations

end NBHilbertData
end MCore.RH.NB
