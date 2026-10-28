import MCore.K8
import MCore.RH.R0.HardFrontier

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
Quantitative rate hypothesis stated independently of RH.
This is exactly the missing uniform logarithmic bound, written as data.
-/
def ConcreteLogRate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ,
      concreteNBData.DN concreteGeneratorFamily N ≤
        C / Real.log ((N : ℝ) + 2)

/-- The quantitative rate alone is exactly sufficient for the hard frontier. -/
theorem concreteLogRate_implies_ConcreteUniformLogDNBound
    (hRate : ConcreteLogRate) :
    ConcreteUniformLogDNBound := by
  rcases hRate with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N
  simpa [logMajorant] using hbound N

/--
Honest conditional decomposition: RH is carried explicitly, but the
construction of the material producer uses only the quantitative rate.
Thus this theorem does not assert or conceal RH -> O(1/log N).
-/
theorem RH_and_logRate_imply_ConcreteUniformLogDNBound
    (hRH : RiemannHypothesis)
    (hRate : ConcreteLogRate) :
    ConcreteUniformLogDNBound := by
  exact concreteLogRate_implies_ConcreteUniformLogDNBound hRate

/-- Same statement through the repository's exact Mathlib RH alias. -/
theorem OfficialSpecRH_and_logRate_imply_ConcreteUniformLogDNBound
    (hRH : MCore.OfficialSpecRH)
    (hRate : ConcreteLogRate) :
    ConcreteUniformLogDNBound := by
  exact concreteLogRate_implies_ConcreteUniformLogDNBound hRate

#print axioms MCore.RH.R0.concreteLogRate_implies_ConcreteUniformLogDNBound
#print axioms MCore.RH.R0.RH_and_logRate_imply_ConcreteUniformLogDNBound
#print axioms MCore.RH.R0.OfficialSpecRH_and_logRate_imply_ConcreteUniformLogDNBound

end MCore.RH.R0
