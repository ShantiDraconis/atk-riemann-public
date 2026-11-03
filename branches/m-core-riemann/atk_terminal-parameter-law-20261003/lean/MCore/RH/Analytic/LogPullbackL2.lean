import MCore.RH.Analytic.D3PlancherelReduction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral

namespace MCore.RH.R0

open MeasureTheory Set

/-- Logarithmic pullback used by Mellin on the critical line. -/
noncomputable def logPullback (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  Real.exp (-(u / 2)) • f (Real.exp (-u))

/--
The logarithmic pullback is an exact L2 isometry at sigma = 1/2.
This is the Jacobian identity behind Mellin--Plancherel.
-/
theorem logPullback_normSq_integral (f : ℝ → ℂ) :
    (∫ u : ℝ, ‖logPullback f u‖ ^ 2) =
      ∫ x : ℝ in Ioi 0, ‖f x‖ ^ 2 := by
  rw [← integral_neg_eq_self]
  have hpoint :
      (fun u : ℝ => ‖logPullback f (-u)‖ ^ 2) =
        fun u : ℝ => Real.exp u * ‖f (Real.exp u)‖ ^ 2 := by
    funext u
    unfold logPullback
    simp only [neg_div, neg_neg, Real.norm_eq_abs, norm_smul]
    rw [abs_of_pos (Real.exp_pos _)]
    rw [show -(-u / 2) = u / 2 by ring]
    rw [sq, mul_assoc]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hpoint]
  simpa [smul_eq_mul] using
    (integral_comp_exp (fun x : ℝ => ‖f x‖ ^ 2))

/-- Critical residual specialization. -/
theorem residual_logPullback_normSq_integral
    {N : ℕ} (c : Fin N → ℝ) :
    (∫ u : ℝ, ‖logPullback (residualRepresentativeC c) u‖ ^ 2) =
      ∫ x : ℝ in Ioi 0, ‖residualRepresentativeC c x‖ ^ 2 := by
  exact logPullback_normSq_integral _

#print axioms MCore.RH.R0.logPullback_normSq_integral

end MCore.RH.R0
