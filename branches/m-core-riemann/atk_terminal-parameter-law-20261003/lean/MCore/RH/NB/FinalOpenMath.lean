import MCore.RH.NB.ExactFinalProducer

namespace MCore.RH.NB.Final

/-- Exact remaining RH mathematical content after all certified reductions. -/
def OpenMathResidual
    (D : NBHilbertData) (rho : D.GeneratorFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∃ c : Fin N → ℝ,
      (∀ j : Fin N,
        (∑ i : Fin N, c i * D.gramEntry rho i j) =
          D.targetEntry rho j) ∧
      ‖D.chi‖ ^ 2 -
        (∑ i : Fin N, c i * D.targetEntry rho i) < ε ^ 2

theorem residual_closes_final
    (D : NBHilbertData) (rho : D.GeneratorFamily)
    (h : OpenMathResidual D rho) :
    FinalExternalCertificate D rho :=
  finalExternal_of_normal_equation_energy D rho h

end MCore.RH.NB.Final
