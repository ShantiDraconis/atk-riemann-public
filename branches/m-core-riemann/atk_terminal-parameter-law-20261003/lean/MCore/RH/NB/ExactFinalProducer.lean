import MCore.RH.NB.FinalExternal
import MCore.RH.NB.QuantitativeUpperBound
import MCore.RH.NB.GramEndpoint

namespace MCore.RH.NB
namespace Final

/-- Exact mathematical producer for the final RH zero-limit root.
    The only new content required is an explicit nonnegative majorant eps
    dominating DN and tending to zero. -/
theorem finalExternal_of_vanishingUpperBound
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h : D.VanishingUpperBound rho) :
    FinalExternalCertificate D rho :=
  D.DNToZero_of_vanishingUpperBound rho h

theorem finalRoot_of_vanishingUpperBound
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h : D.VanishingUpperBound rho) :
    FINAL_ROOT D rho :=
  finalExternal_to_FINAL_ROOT D rho
    (finalExternal_of_vanishingUpperBound D rho h)

/-- Equivalent finite-dimensional Gram producer.  For every epsilon, it is
    enough to solve the projection normal equations and make the reduced energy
    smaller than epsilon squared. -/
theorem finalExternal_of_normal_equation_energy
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ c : Fin N → ℝ,
          (∀ j : Fin N,
            (∑ i : Fin N, c i * D.gramEntry rho i j) =
              D.targetEntry rho j) ∧
          ‖D.chi‖ ^ 2 -
              (∑ i : Fin N, c i * D.targetEntry rho i) < ε ^ 2) :
    FinalExternalCertificate D rho := by
  apply FINAL_ROOT_to_finalExternal D rho
  exact (D.DNLimit_eq_zero_iff_normal_equation_energy rho).2 h

#print axioms MCore.RH.NB.Final.finalExternal_of_normal_equation_energy

#print axioms MCore.RH.NB.Final.finalExternal_of_vanishingUpperBound
#print axioms MCore.RH.NB.Final.finalRoot_of_vanishingUpperBound

end Final
end MCore.RH.NB
