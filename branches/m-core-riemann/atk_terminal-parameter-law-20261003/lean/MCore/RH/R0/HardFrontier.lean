import MCore.RH.R0.ConcreteLogMajorantProducer

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/-- Canonical hard frontier for the RH lane.
An inhabitant is exactly a concrete, uniform logarithmic upper bound
for the certified DN sequence. -/
def ConcreteUniformLogDNBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ,
      concreteNBData.DN concreteGeneratorFamily N ≤
        logMajorant K N

theorem concreteUniformLogDNBound_iff_nonempty :
    ConcreteUniformLogDNBound ↔ Nonempty ConcreteLogDNBound := by
  constructor
  · rintro ⟨K, hK, hdn⟩
    exact ⟨{ K := K, hK := hK, dn_le := hdn }⟩
  · intro h
    exact nonempty_concreteLogDNBound_iff.mp h

theorem terminal_of_concreteUniformLogDNBound
    (h : ConcreteUniformLogDNBound) :
    RiemannTerminalCertifies := by
  exact concreteLogDNBound_to_RiemannTerminalCertifies
    (Classical.choice (concreteUniformLogDNBound_iff_nonempty.mp h))

/-- Fail-closed status marker. There is intentionally no theorem
producing ConcreteUniformLogDNBound. Producing it is the remaining
mathematical step. -/
def rhHardFrontierStatus : String :=
  "OPEN_MATH: ConcreteUniformLogDNBound"

#print axioms MCore.RH.R0.concreteUniformLogDNBound_iff_nonempty
#print axioms MCore.RH.R0.terminal_of_concreteUniformLogDNBound

end MCore.RH.R0
