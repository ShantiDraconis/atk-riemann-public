import MCore.RH.R0.HardFrontier

namespace MCore.RH.R0

/--
Single material producer type for the RH lane.
No new hypothesis is introduced: this is definitionally the canonical hard frontier.
-/
abbrev RHMaterialProducer : Prop := ConcreteUniformLogDNBound

/-- Exact terminal consumer for the unique material producer. -/
theorem rh_material_producer_closes_terminal
    (h : RHMaterialProducer) :
    RiemannTerminalCertifies :=
  terminal_of_concreteUniformLogDNBound h

/-- A nonempty proof object of the material producer is sufficient for the endpoint. -/
theorem rh_material_producer_nonempty_closes_terminal
    (h : Nonempty RHMaterialProducer) :
    RiemannTerminalCertifies :=
  rh_material_producer_closes_terminal (Classical.choice h)

/-- Fail-closed: this file consumes the producer but never manufactures it. -/
def rhMaterialProducerState : String :=
  "OPEN_MATH: inhabit RHMaterialProducer = ConcreteUniformLogDNBound"

#print axioms MCore.RH.R0.rh_material_producer_closes_terminal
#print axioms MCore.RH.R0.rh_material_producer_nonempty_closes_terminal

end MCore.RH.R0
