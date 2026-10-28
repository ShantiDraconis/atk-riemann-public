import MCore.RH.NB.ExplicitCoefficientProducer
import Mathlib.NumberTheory.ArithmeticFunction

namespace RH

open Filter Topology
open MCore.RH.NB
open MCore.RH.R0

/--
Explicit damped Möbius coefficient family selected by the finite-N audit.

For stage N and arithmetic index n+1:
  c_N(n) = -mu(n+1) * (1 - log(n+1)/log N)^(3/16)

The small stages N < 2 are set to zero only to avoid the log(1) denominator.
No convergence theorem is asserted here.
-/
noncomputable def dampedMobius316
    (N n : ℕ) : ℝ :=
  if 2 ≤ N then
    -(((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ)) *
      Real.rpow
        (1 - Real.log ((n + 1 : ℕ) : ℝ) / Real.log (N : ℝ))
        ((3 : ℝ) / 16)
  else
    0

/-- Literal L2 error sequence for the fixed alpha=3/16 candidate. -/
noncomputable def dampedMobius316Error (N : ℕ) : ℝ :=
  ‖concreteNBData.chi -
    concreteNBData.finiteCoefficientApproximant
      concreteGeneratorFamily dampedMobius316 N‖

/--
This is the exact kernel-pressure theorem for the selected explicit family:
only the genuine asymptotic L2 estimate is left as input.
-/
theorem DNLimit_eq_zero_of_dampedMobius316
    (hzero :
      Tendsto dampedMobius316Error atTop (nhds 0)) :
    concreteNBData.DNLimit concreteGeneratorFamily = 0 := by
  apply concreteDNLimit_eq_zero_of_coefficient_error_tendsto_zero
    dampedMobius316
  simpa [dampedMobius316Error] using hzero

#check dampedMobius316
#check dampedMobius316Error
#print axioms DNLimit_eq_zero_of_dampedMobius316

end RH
