import MCore.RH.NB.ZeroLimitFrontier
import MCore.RH.R0.RhoConcrete

open scoped BigOperators

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
The finite linear combination determined by an explicit coefficient table.
At stage `N`, only the first `N` generators occur.
-/
noncomputable def finiteCoefficientApproximant
    (rho : D.GeneratorFamily)
    (c : ℕ → ℕ → ℝ)
    (N : ℕ) : D.H :=
  ∑ n : Fin N, (c N n) • rho n

/--
Every explicit finite coefficient approximant belongs to the canonical
finite span `V_N`.
-/
theorem finiteCoefficientApproximant_mem_V
    (rho : D.GeneratorFamily)
    (c : ℕ → ℕ → ℝ)
    (N : ℕ) :
    D.finiteCoefficientApproximant rho c N ∈ D.V rho N := by
  classical
  unfold finiteCoefficientApproximant
  exact (D.V rho N).sum_mem (fun n _ =>
    (D.V rho N).smul_mem (c N n) (D.generator_mem_V rho N n))

/--
A single explicit coefficient family whose L2 error tends to zero is a
genuine producer for the finite-span density frontier.
-/
theorem finiteSpanApproximatesChi_of_coefficient_error_tendsto_zero
    (rho : D.GeneratorFamily)
    (c : ℕ → ℕ → ℝ)
    (hzero :
      Filter.Tendsto
        (fun N => ‖D.chi - D.finiteCoefficientApproximant rho c N‖)
        Filter.atTop
        (nhds 0)) :
    D.FiniteSpanApproximatesChi rho := by
  intro ε hε
  have hevent :
      ∀ᶠ N in Filter.atTop,
        ‖D.chi - D.finiteCoefficientApproximant rho c N‖ < ε :=
    (tendsto_order.1 hzero).2 ε hε
  rcases Filter.eventually_atTop.1 hevent with ⟨N0, hN0⟩
  refine ⟨N0, ⟨D.finiteCoefficientApproximant rho c N0,
    D.finiteCoefficientApproximant_mem_V rho c N0⟩, ?_⟩
  simpa using hN0 N0 (le_rfl)

/--
The same explicit L2 convergence closes the canonical `DNLimit = 0`
frontier through the already-certified finite-span equivalence.
-/
theorem DNLimit_eq_zero_of_coefficient_error_tendsto_zero
    (rho : D.GeneratorFamily)
    (c : ℕ → ℕ → ℝ)
    (hzero :
      Filter.Tendsto
        (fun N => ‖D.chi - D.finiteCoefficientApproximant rho c N‖)
        Filter.atTop
        (nhds 0)) :
    D.DNLimit rho = 0 :=
  D.DNLimit_eq_zero_of_finiteSpanApproximatesChi rho
    (D.finiteSpanApproximatesChi_of_coefficient_error_tendsto_zero rho c hzero)

end NBHilbertData
end MCore.RH.NB

namespace MCore.RH.R0

open MCore.RH.NB

/--
Concrete terminal adapter: an explicit coefficient family on the certified
Báez-Duarte generators closes the concrete DN limit as soon as its L2 error
is proved to tend to zero.
-/
theorem concreteDNLimit_eq_zero_of_coefficient_error_tendsto_zero
    (c : ℕ → ℕ → ℝ)
    (hzero :
      Filter.Tendsto
        (fun N =>
          ‖concreteNBData.chi -
            concreteNBData.finiteCoefficientApproximant
              concreteGeneratorFamily c N‖)
        Filter.atTop
        (nhds 0)) :
    concreteNBData.DNLimit concreteGeneratorFamily = 0 :=
  concreteNBData.DNLimit_eq_zero_of_coefficient_error_tendsto_zero
    concreteGeneratorFamily c hzero

end MCore.RH.R0
