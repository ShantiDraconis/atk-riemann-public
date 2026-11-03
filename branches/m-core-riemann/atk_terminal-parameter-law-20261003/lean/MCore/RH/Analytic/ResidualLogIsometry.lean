import MCore.RH.Analytic.MellinPlancherelBridge
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- Pointwise norm-square identity for the logarithmic Mellin pullback. -/
theorem normSq_residualLogTransform
    {N : ℕ} (c : Fin N → ℝ) (u : ℝ) :
    Complex.normSq (residualLogTransform c u) =
      Real.exp (-u) *
        Complex.normSq (residualRepresentativeC c (Real.exp (-u))) := by
  unfold residualLogTransform
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  have hexp :
      Real.exp (-(1 / 2 : ℝ) * u) * Real.exp (-(1 / 2 : ℝ) * u) =
        Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- D3 bridge: x = exp(-u) is exactly an L2 isometry with the half-density weight. -/
theorem residualLogL2Isometry_realized :
    ResidualLogL2Isometry := by
  intro N c
  let g : ℝ → ℝ := fun x =>
    Complex.normSq (residualRepresentativeC c x)
  have hexp := integral_comp_exp g
  calc
    (∫ x : ℝ in Ioi 0, Complex.normSq (residualRepresentativeC c x))
        = ∫ u : ℝ, Real.exp u * g (Real.exp u) := by
            simpa [g, smul_eq_mul] using hexp.symm
    _ = ∫ u : ℝ, Real.exp (-u) * g (Real.exp (-u)) := by
          rw [← integral_neg_eq_self]
          apply integral_congr_ae
          filter_upwards with u
          simp [g]
    _ = ∫ u : ℝ, Complex.normSq (residualLogTransform c u) := by
          apply integral_congr_ae
          filter_upwards with u
          rw [normSq_residualLogTransform c u]

#print axioms MCore.RH.R0.normSq_residualLogTransform
#print axioms MCore.RH.R0.residualLogL2Isometry_realized

end MCore.RH.R0
