import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic

open Finset Nat

namespace MCore.RH.R2

/--
The divisor sum of the Möbius function is the Dirichlet identity.
This is the exact arithmetic cancellation used by the raw Möbius
Nyman--Beurling approximants; no RH input occurs here.
-/
theorem sum_moebius_divisors_eq_indicator (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then (1 : ℤ) else 0 := by
  calc
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d)
        =
        ((ArithmeticFunction.moebius *
          (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n) := by
          symm
          exact ArithmeticFunction.coe_mul_zeta_apply
    _ = (1 : ArithmeticFunction ℤ) n := by
          rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = if n = 1 then (1 : ℤ) else 0 := by
          rfl

#print axioms sum_moebius_divisors_eq_indicator

end MCore.RH.R2
