import MCore.RH.NB.GramEnergy

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
Exact terminal reformulation of the zero-defect endpoint.

No new open proposition is introduced. The canonical condition
`DNLimit rho = 0` is equivalent to the existence, at arbitrarily small
scales, of a finite coefficient vector that:
1. solves the projection Gram normal equations; and
2. has reduced projection energy below epsilon squared.
-/
theorem DNLimit_eq_zero_iff_normal_equation_energy
    (rho : D.GeneratorFamily) :
    D.DNLimit rho = 0 ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ c : Fin N → ℝ,
          (∀ j : Fin N,
            (∑ i : Fin N, c i * D.gramEntry rho i j) =
              D.targetEntry rho j) ∧
          ‖D.chi‖ ^ 2 -
              (∑ i : Fin N, c i * D.targetEntry rho i) < ε ^ 2 := by
  constructor
  · intro hlim ε hε
    have hzero : D.DNToZero rho :=
      (D.DNToZero_iff_DNLimit_eq_zero rho).2 hlim
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hevent : ∀ᶠ N in Filter.atTop, D.DN rho N < ε ^ 2 :=
      (tendsto_order.1 hzero).2 (ε ^ 2) hεsq
    rcases Filter.eventually_atTop.1 hevent with ⟨N0, hN0⟩
    rcases D.exists_optimal_coefficients_reduced_energy rho N0 with
      ⟨c, hred, hnormal⟩
    refine ⟨N0, c, hnormal, ?_⟩
    rw [← hred]
    exact hN0 N0 (le_rfl)
  · intro h
    apply (D.finiteSpanApproximatesChi_iff_DNLimit_eq_zero rho).1
    apply (D.finiteSpanApproximatesChi_iff_exists_coefficients rho).2
    intro ε hε
    rcases h ε hε with ⟨N, c, hnormal, hred⟩
    refine ⟨N, c, ?_⟩
    have henergy :
        D.coefficientEnergy rho N c =
          ‖D.chi‖ ^ 2 -
            (∑ i : Fin N, c i * D.targetEntry rho i) :=
      D.coefficientEnergy_of_normal_equations rho N c hnormal
    have herr :
        ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 =
          D.coefficientEnergy rho N c :=
      D.coefficient_error_sq_eq_energy rho N c
    have hsq :
        ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2 < ε ^ 2 := by
      calc
        ‖D.chi - D.coefficientApproximantAt rho N c‖ ^ 2
            = D.coefficientEnergy rho N c := herr
        _ = ‖D.chi‖ ^ 2 -
              (∑ i : Fin N, c i * D.targetEntry rho i) := henergy
        _ < ε ^ 2 := hred
    have hnorm :
        0 ≤ ‖D.chi - D.coefficientApproximantAt rho N c‖ :=
      norm_nonneg _
    nlinarith

#print axioms DNLimit_eq_zero_iff_normal_equation_energy

end NBHilbertData
end MCore.RH.NB
