import MCore.RH.NB.ZeroLimitFrontier
import MCore.RH.R0.RhoConcrete
import MCore.Frontier.MultistateSN

namespace MCore.RH.R01

open MCore.RH.NB
open MCore.RH.R0
open MCore.RiemannMultistate

/--
Canonical material producer for the current RH frontier.
This is exactly the geometric density statement recorded in GATE_LEDGER.json.
No quantitative rate and no alternate presentation is built into the definition.
-/
def ConcreteProducer : Prop :=
  concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily

/-- The canonical R01 producer is exactly equivalent to vanishing of DNLimit. -/
theorem concreteProducer_iff_DNLimit_eq_zero :
    ConcreteProducer ↔
      concreteNBData.DNLimit concreteGeneratorFamily = 0 := by
  exact concreteNBData.finiteSpanApproximatesChi_iff_DNLimit_eq_zero
    concreteGeneratorFamily

/-- Equivalent convergence form of the same single material producer. -/
theorem concreteProducer_iff_DNToZero :
    ConcreteProducer ↔
      concreteNBData.DNToZero concreteGeneratorFamily := by
  exact concreteNBData.finiteSpanApproximatesChi_iff_DNToZero
    concreteGeneratorFamily

/--
A weighted-decay presentation does not close R01 merely by existing.
It must provide an explicit kernel-checked bridge to the canonical concrete
finite-span density proposition.
-/
structure WeightedDecayBridge where
  decay : WeightedModularBilinearDecay ℝ
  toConcreteProducer : ConcreteProducer

/-- Any genuine bridge from weighted decay to the canonical producer closes the
zero-limit frontier, but this theorem does not manufacture such a bridge. -/
theorem DNLimit_eq_zero_of_weightedDecayBridge
    (B : WeightedDecayBridge) :
    concreteNBData.DNLimit concreteGeneratorFamily = 0 := by
  exact concreteNBData.DNLimit_eq_zero_of_finiteSpanApproximatesChi
    concreteGeneratorFamily B.toConcreteProducer

/-- Same bridge stated in convergence language. -/
theorem DNToZero_of_weightedDecayBridge
    (B : WeightedDecayBridge) :
    concreteNBData.DNToZero concreteGeneratorFamily := by
  exact concreteNBData.DNToZero_of_finiteSpanApproximatesChi
    concreteGeneratorFamily B.toConcreteProducer

#print axioms MCore.RH.R01.concreteProducer_iff_DNLimit_eq_zero
#print axioms MCore.RH.R01.concreteProducer_iff_DNToZero
#print axioms MCore.RH.R01.DNLimit_eq_zero_of_weightedDecayBridge
#print axioms MCore.RH.R01.DNToZero_of_weightedDecayBridge

end MCore.RH.R01
