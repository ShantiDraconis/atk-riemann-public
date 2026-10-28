import MCore.RH.R0.ExplicitCoefficientLogRate

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
Weighted critical-line error rate for explicit finite coefficient families.

This avoids the false pointwise requirement of uniformly bounding 1/zeta
arbitrarily close to zeros on Re(s)=1/2.  The quantity here is exactly the
kind of weighted L2 error that the Mellin-Plancherel identity must control.

The integral representation itself is not asserted in this file; this is the
kernel-side quantitative target to be produced by a future formal Mellin layer.
-/
structure CriticalLineWeightedErrorRate where
  K : ℝ
  hK : 0 ≤ K
  coeff : (N : ℕ) → Fin N → ℝ
  error_sq_le :
    ∀ N : ℕ,
      ‖concreteNBData.chi -
        concreteNBData.coefficientApproximantAt
          concreteGeneratorFamily N (coeff N)‖ ^ 2 ≤
        logMajorant K N

/-- The corrected weighted-error target is definitionally sufficient for the
already-closed explicit coefficient producer. -/
def CriticalLineWeightedErrorRate.toConcreteCoefficientLogRate
    (h : CriticalLineWeightedErrorRate) :
    ConcreteCoefficientLogRate :=
  { K := h.K
    hK := h.hK
    coeff := h.coeff
    error_sq_le := h.error_sq_le }

theorem CriticalLineWeightedErrorRate.toUniformLogDNBound
    (h : CriticalLineWeightedErrorRate) :
    ConcreteUniformLogDNBound :=
  h.toConcreteCoefficientLogRate.toUniformLogDNBound

#print axioms MCore.RH.R0.CriticalLineWeightedErrorRate.toConcreteCoefficientLogRate
#print axioms MCore.RH.R0.CriticalLineWeightedErrorRate.toUniformLogDNBound

end MCore.RH.R0
