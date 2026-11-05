import MCore.RH.NB.CoefficientRealization
import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
The canonical finite-span endpoint is exactly arbitrary approximation by an
explicit finite coefficient vector. No extra hypothesis or restricted route
is introduced.
-/
theorem finiteSpanApproximatesChi_iff_exists_coefficients
    (rho : D.GeneratorFamily) :
    D.FiniteSpanApproximatesChi rho ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ c : Fin N → ℝ,
          ‖D.chi - D.coefficientApproximantAt rho N c‖ < ε := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, v, hv⟩
    rcases D.exists_coefficients_of_mem_V rho N v with ⟨c, hc⟩
    refine ⟨N, c, ?_⟩
    rw [hc]
    exact hv
  · intro h ε hε
    rcases h ε hε with ⟨N, c, hc⟩
    refine ⟨N, ⟨D.coefficientApproximantAt rho N c,
      D.coefficientApproximantAt_mem_V rho N c⟩, ?_⟩
    exact hc

/-- Exact coefficient-vector formulation of the zero-defect endpoint. -/
theorem DNLimit_eq_zero_iff_exists_coefficients
    (rho : D.GeneratorFamily) :
    D.DNLimit rho = 0 ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ c : Fin N → ℝ,
          ‖D.chi - D.coefficientApproximantAt rho N c‖ < ε := by
  calc
    D.DNLimit rho = 0 ↔ D.FiniteSpanApproximatesChi rho :=
      (D.finiteSpanApproximatesChi_iff_DNLimit_eq_zero rho).symm
    _ ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ c : Fin N → ℝ,
          ‖D.chi - D.coefficientApproximantAt rho N c‖ < ε :=
      D.finiteSpanApproximatesChi_iff_exists_coefficients rho

/-- Equivalent convergence formulation, still with no new open proposition. -/
theorem DNToZero_iff_exists_coefficients
    (rho : D.GeneratorFamily) :
    D.DNToZero rho ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ c : Fin N → ℝ,
          ‖D.chi - D.coefficientApproximantAt rho N c‖ < ε := by
  calc
    D.DNToZero rho ↔ D.FiniteSpanApproximatesChi rho :=
      (D.finiteSpanApproximatesChi_iff_DNToZero rho).symm
    _ ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ c : Fin N → ℝ,
          ‖D.chi - D.coefficientApproximantAt rho N c‖ < ε :=
      D.finiteSpanApproximatesChi_iff_exists_coefficients rho

#print axioms finiteSpanApproximatesChi_iff_exists_coefficients
#print axioms DNLimit_eq_zero_iff_exists_coefficients
#print axioms DNToZero_iff_exists_coefficients

end NBHilbertData
end MCore.RH.NB
