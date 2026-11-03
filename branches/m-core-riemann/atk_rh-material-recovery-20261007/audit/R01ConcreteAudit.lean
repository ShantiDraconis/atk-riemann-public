import MCore.Frontier.R01Concrete

namespace MCore.RH.R01.Audit

open MCore.RH.R01
open MCore.RH.R0

/--
Fail-closed audit of the current single RH material frontier.
This file certifies only the exact equivalences and bridge interfaces.
It deliberately does not inhabit ConcreteProducer.
-/
def MATERIAL_OPEN_GAPS : Nat := 1

def CURRENT_OPEN_PRODUCER : Prop :=
  ConcreteProducer

theorem current_open_producer_iff_DNLimit_zero :
    CURRENT_OPEN_PRODUCER ↔
      concreteNBData.DNLimit concreteGeneratorFamily = 0 :=
  concreteProducer_iff_DNLimit_eq_zero

theorem current_open_producer_iff_DNToZero :
    CURRENT_OPEN_PRODUCER ↔
      concreteNBData.DNToZero concreteGeneratorFamily :=
  concreteProducer_iff_DNToZero

#print axioms MCore.RH.R01.Audit.current_open_producer_iff_DNLimit_zero
#print axioms MCore.RH.R01.Audit.current_open_producer_iff_DNToZero

end MCore.RH.R01.Audit
