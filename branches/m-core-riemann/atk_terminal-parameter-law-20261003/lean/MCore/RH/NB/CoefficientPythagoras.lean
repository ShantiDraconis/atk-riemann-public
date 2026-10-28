import MCore.RH.NB.GramNormalEquations

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
Exact Pythagorean decomposition of any finite coefficient error into:
1. the canonical optimal projection defect DN_N, and
2. the squared distance from the chosen coefficient approximant to the
   orthogonal projection itself.

This is the quantitative bridge needed to analyze explicit Möbius-like
coefficient families against the true finite optimum.
-/
theorem coefficient_error_sq_eq_DN_add_projection_gap
    (rho : D.GeneratorFamily)
    (N : ℕ)
    (c : Fin N → ℝ) :
    ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 =
      D.DN rho N +
      ‖(D.P rho N D.chi : D.H) -
        D.coefficientApproximantAt rho N c‖ ^ 2 := by
  let p : D.H := (D.P rho N D.chi : D.H)
  let v : D.H := D.coefficientApproximantAt rho N c
  have hv : v ∈ D.V rho N := by
    simpa [v] using D.coefficientApproximantAt_mem_V rho N c
  have hp : p ∈ D.V rho N := by
    simpa [p] using D.P_mem rho N D.chi
  have hpv : p - v ∈ D.V rho N :=
    (D.V rho N).sub_mem hp hv
  have horth :
      @inner ℝ D.H _ (D.chi - p) (p - v) = 0 := by
    exact D.residual_inner_eq_zero rho N D.chi (p - v) hpv
  have hdecomp :
      D.chi - v = (D.chi - p) + (p - v) := by
    abel
  rw [hdecomp, norm_add_sq_real, horth]
  simp [DN, dN, p, v]

/--
Consequent sharp upper bound: controlling the projection gap by epsilon_N
controls the explicit family error by DN_N + epsilon_N.
-/
theorem coefficient_error_sq_le_DN_add
    (rho : D.GeneratorFamily)
    (N : ℕ)
    (c : Fin N → ℝ)
    (eps : ℝ)
    (hgap :
      ‖(D.P rho N D.chi : D.H) -
        D.coefficientApproximantAt rho N c‖ ^ 2 ≤ eps) :
    ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2
      ≤ D.DN rho N + eps := by
  rw [D.coefficient_error_sq_eq_DN_add_projection_gap rho N c]
  exact add_le_add_left hgap _

/--
Exact excess-risk identity: the penalty paid by any explicit coefficient
family above the optimum is precisely the squared projection gap.
-/
theorem coefficient_excess_error_eq_projection_gap
    (rho : D.GeneratorFamily)
    (N : ℕ)
    (c : Fin N → ℝ) :
    ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 -
      D.DN rho N =
      ‖(D.P rho N D.chi : D.H) -
        D.coefficientApproximantAt rho N c‖ ^ 2 := by
  rw [D.coefficient_error_sq_eq_DN_add_projection_gap rho N c]
  ring

#print axioms MCore.RH.NB.NBHilbertData.coefficient_error_sq_eq_DN_add_projection_gap
#print axioms MCore.RH.NB.NBHilbertData.coefficient_excess_error_eq_projection_gap

end NBHilbertData
end MCore.RH.NB
