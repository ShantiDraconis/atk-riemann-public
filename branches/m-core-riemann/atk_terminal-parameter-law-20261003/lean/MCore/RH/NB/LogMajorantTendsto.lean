import MCore.RH.R0.HardFrontier

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
A concrete uniform logarithmic DN bound forces the concrete DN sequence
to converge to zero.  This is one-way only: no converse rate theorem is
claimed here.
-/
theorem ConcreteUniformLogDNBound_implies_DN_tendsto_zero
    (h : ConcreteUniformLogDNBound) :
    Filter.Tendsto
      (fun N => concreteNBData.DN concreteGeneratorFamily N)
      Filter.atTop
      (nhds 0) := by
  obtain ⟨K, hK, hle⟩ := h
  have h0 :
      ∀ N : ℕ, 0 ≤ concreteNBData.DN concreteGeneratorFamily N :=
    fun N => concreteNBData.DN_nonneg concreteGeneratorFamily N
  have hT :
      Filter.Tendsto (logMajorant K) Filter.atTop (nhds 0) :=
    logMajorant_tendsto_zero K
  exact squeeze_zero h0 hle hT

#print axioms MCore.RH.R0.ConcreteUniformLogDNBound_implies_DN_tendsto_zero

end MCore.RH.R0
