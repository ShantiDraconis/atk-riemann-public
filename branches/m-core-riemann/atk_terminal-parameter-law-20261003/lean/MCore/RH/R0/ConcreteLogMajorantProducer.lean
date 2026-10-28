import MCore.RH.NB.LogMajorantFinalProducer
import MCore.RH.R0.ConcreteVanishingProducer

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
Concrete one-field material certificate for the RH terminal producer.

All analytic bookkeeping (nonnegativity of eps and eps -> 0) is discharged
by the already-proved logarithmic majorant lemmas.  The only non-structural
field is the uniform concrete DN estimate.
-/
structure ConcreteLogDNBound where
  K : ℝ
  hK : 0 ≤ K
  dn_le :
    ∀ N : ℕ,
      concreteNBData.DN concreteGeneratorFamily N ≤
        logMajorant K N

/-- Convert the one-field concrete estimate into the generic log-majorant certificate. -/
def ConcreteLogDNBound.toLogMajorantCertificate
    (h : ConcreteLogDNBound) :
    LogMajorantCertificate concreteNBData concreteGeneratorFamily :=
  {
    K := h.K
    hK := h.hK
    dn_le := h.dn_le
  }

/-- Exact construction of the missing VanishingUpperBound from the concrete log estimate. -/
noncomputable def ConcreteLogDNBound.toConcreteVanishingUpperBound
    (h : ConcreteLogDNBound) :
    ConcreteVanishingUpperBound :=
  vanishingUpperBound_of_logMajorant
    concreteNBData concreteGeneratorFamily
    h.toLogMajorantCertificate

theorem concreteLogDNBound_to_FINAL_ROOT
    (h : ConcreteLogDNBound) :
    MCore.RH.NB.Final.FINAL_ROOT concreteNBData concreteGeneratorFamily :=
  concreteVanishingUpperBound_to_FINAL_ROOT
    h.toConcreteVanishingUpperBound

theorem concreteLogDNBound_to_ConcreteGramResidual
    (h : ConcreteLogDNBound) :
    ConcreteGramResidual :=
  concreteVanishingUpperBound_to_ConcreteGramResidual
    h.toConcreteVanishingUpperBound

theorem concreteLogDNBound_to_FiniteSpanApproximatesChi
    (h : ConcreteLogDNBound) :
    concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily :=
  concreteVanishingUpperBound_to_FiniteSpanApproximatesChi
    h.toConcreteVanishingUpperBound

theorem concreteLogDNBound_to_RiemannTerminalCertifies
    (h : ConcreteLogDNBound) :
    RiemannTerminalCertifies :=
  concreteVanishingUpperBound_to_RiemannTerminalCertifies
    h.toConcreteVanishingUpperBound

/--
Producer-first normal form: the existence of this concrete certificate is
exactly the existence of a nonnegative constant K satisfying the logarithmic
DN upper bound for every N.
-/
theorem nonempty_concreteLogDNBound_iff :
    Nonempty ConcreteLogDNBound ↔
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ N : ℕ,
          concreteNBData.DN concreteGeneratorFamily N ≤
            logMajorant K N := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.K, h.hK, h.dn_le⟩
  · rintro ⟨K, hK, hdn⟩
    exact ⟨{ K := K, hK := hK, dn_le := hdn }⟩

#print axioms MCore.RH.R0.ConcreteLogDNBound.toConcreteVanishingUpperBound
#print axioms MCore.RH.R0.concreteLogDNBound_to_FINAL_ROOT
#print axioms MCore.RH.R0.concreteLogDNBound_to_ConcreteGramResidual
#print axioms MCore.RH.R0.concreteLogDNBound_to_FiniteSpanApproximatesChi
#print axioms MCore.RH.R0.concreteLogDNBound_to_RiemannTerminalCertifies
#print axioms MCore.RH.R0.nonempty_concreteLogDNBound_iff

end MCore.RH.R0
