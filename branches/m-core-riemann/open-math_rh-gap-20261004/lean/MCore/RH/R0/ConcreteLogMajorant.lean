import MCore.RH.NB.LogMajorantFinalProducer
import MCore.RH.R0.ConcreteFinalProducer

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/-- Concrete logarithmic majorant target for the certified Báez--Duarte family.
    This fixes all generic parameters of LogMajorantCertificate. -/
abbrev ConcreteLogMajorantCertificate :=
  LogMajorantCertificate concreteNBData concreteGeneratorFamily

/-- The concrete logarithmic majorant certificate closes the concrete final root
    with no additional mathematical premise. -/
theorem concreteLogMajorant_to_FINAL_ROOT
    (h : ConcreteLogMajorantCertificate) :
    FINAL_ROOT concreteNBData concreteGeneratorFamily :=
  FINAL_ROOT_of_logMajorant concreteNBData concreteGeneratorFamily h

/-- Expanded theorem form of the sole quantitative residue on this route. -/
theorem concrete_log_bound_closes_FINAL_ROOT
    (K : ℝ)
    (hK : 0 ≤ K)
    (hbound :
      ∀ N : ℕ,
        concreteNBData.DN concreteGeneratorFamily N ≤
          logMajorant K N) :
    FINAL_ROOT concreteNBData concreteGeneratorFamily := by
  exact concreteLogMajorant_to_FINAL_ROOT
    { K := K
      hK := hK
      dn_le := hbound }

/-- Explicitly expose the concrete inequality in ordinary notation. -/
theorem concrete_log_bound_expanded_closes_FINAL_ROOT
    (K : ℝ)
    (hK : 0 ≤ K)
    (hbound :
      ∀ N : ℕ,
        concreteNBData.DN concreteGeneratorFamily N ≤
          K / Real.log ((N : ℝ) + 2)) :
    FINAL_ROOT concreteNBData concreteGeneratorFamily := by
  apply concrete_log_bound_closes_FINAL_ROOT K hK
  intro N
  simpa [logMajorant] using hbound N

#print axioms MCore.RH.R0.concreteLogMajorant_to_FINAL_ROOT
#print axioms MCore.RH.R0.concrete_log_bound_closes_FINAL_ROOT
#print axioms MCore.RH.R0.concrete_log_bound_expanded_closes_FINAL_ROOT

end MCore.RH.R0
