import MCore.RH.NB.Distance
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open scoped BigOperators

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- A coefficient vector over the first N generators. This is data, not a density hypothesis. -/
noncomputable def coefficientApproximantAt
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) : D.H :=
  ∑ i, c i • rho i

/-- Every coefficient vector produces an element of the canonical finite span V_N. -/
theorem coefficientApproximantAt_mem_V
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) :
    D.coefficientApproximantAt rho N c ∈ D.V rho N := by
  classical
  unfold coefficientApproximantAt
  exact (D.V rho N).sum_mem (fun i _ =>
    (D.V rho N).smul_mem (c i) (D.generator_mem_V rho N i))

/-- Conversely, every vector of V_N is represented by a finite coefficient vector.
Thus coefficient space is not a restricted sub-route: it is exactly V_N. -/
theorem exists_coefficients_of_mem_V
    (rho : D.GeneratorFamily) (N : ℕ) (v : D.V rho N) :
    ∃ c : Fin N → ℝ, D.coefficientApproximantAt rho N c = (v : D.H) := by
  classical
  have hv :
      (v : D.H) ∈
        Submodule.span ℝ (Set.range (fun i : Fin N => rho i)) := by
    simpa [V, finiteGenerators] using v.property
  rw [Submodule.mem_span_range_iff_exists_fun] at hv
  rcases hv with ⟨c, hc⟩
  exact ⟨c, by simpa [coefficientApproximantAt] using hc⟩

/-- The finite-stage projection error is no larger than the error of any coefficient vector. -/
theorem dN_le_coefficient_error
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) :
    D.dN rho N ≤ ‖D.chi - D.coefficientApproximantAt rho N c‖ := by
  have hmem := D.coefficientApproximantAt_mem_V rho N c
  have hb :
      BddBelow
        (Set.range
          (fun w : D.V rho N => ‖D.chi - (w : D.H)‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _
  unfold dN
  rw [D.P_minimal rho N D.chi]
  exact ciInf_le hb ⟨D.coefficientApproximantAt rho N c, hmem⟩

/-- The orthogonal projection itself has a finite coefficient representation.
Hence the optimum over V_N is actually attained by a coefficient vector. -/
theorem exists_optimal_coefficients
    (rho : D.GeneratorFamily) (N : ℕ) :
    ∃ c : Fin N → ℝ,
      ‖D.chi - D.coefficientApproximantAt rho N c‖ = D.dN rho N := by
  let p : D.V rho N := D.P rho N D.chi
  rcases D.exists_coefficients_of_mem_V rho N p with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [hc]
  rfl

/-- Squared version: DN_N is exactly realized by a finite coefficient vector. -/
theorem exists_optimal_coefficients_DN
    (rho : D.GeneratorFamily) (N : ℕ) :
    ∃ c : Fin N → ℝ,
      ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 = D.DN rho N := by
  rcases D.exists_optimal_coefficients rho N with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  unfold DN
  rw [hc]

/-- Any explicit coefficient error gives an upper bound on the canonical squared defect. -/
theorem DN_le_coefficient_error_sq
    (rho : D.GeneratorFamily) (N : ℕ) (c : Fin N → ℝ) :
    D.DN rho N ≤ ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 := by
  have hle := D.dN_le_coefficient_error rho N c
  have hdn := D.dN_nonneg rho N
  have herr : 0 ≤ ‖D.chi - D.coefficientApproximantAt rho N c‖ := norm_nonneg _
  unfold DN
  nlinarith

#print axioms coefficientApproximantAt_mem_V
#print axioms exists_coefficients_of_mem_V
#print axioms dN_le_coefficient_error
#print axioms exists_optimal_coefficients
#print axioms exists_optimal_coefficients_DN
#print axioms DN_le_coefficient_error_sq

end NBHilbertData
end MCore.RH.NB
