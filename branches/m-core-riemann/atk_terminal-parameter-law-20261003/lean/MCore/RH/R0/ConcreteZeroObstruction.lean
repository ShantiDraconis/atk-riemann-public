import MCore.RH.NB.OrthogonalWitnessObstruction
import MCore.RH.NB.LogMajorantTendsto

namespace MCore.RH.R0

open MCore.RH.NB

/--
Concrete obstruction package: a nonzero vector orthogonal to every concrete
generator and visible to chi is incompatible with the uniform logarithmic
producer.
-/
theorem no_ConcreteUniformLogDNBound_of_orthogonal_witness
    (w : concreteNBData.H)
    (hw : w ≠ 0)
    (hchi : inner ℝ concreteNBData.chi w ≠ 0)
    (hgen : ∀ n : ℕ, inner ℝ (concreteGeneratorFamily n) w = 0) :
    ¬ ConcreteUniformLogDNBound := by
  intro hU
  have hzero :
      concreteNBData.DNToZero concreteGeneratorFamily :=
    ConcreteUniformLogDNBound_implies_DN_tendsto_zero hU
  exact
    (concreteNBData.not_DNToZero_of_orthogonal_witness
      concreteGeneratorFamily w hw hchi hgen) hzero

#print axioms MCore.RH.R0.no_ConcreteUniformLogDNBound_of_orthogonal_witness

end MCore.RH.R0
