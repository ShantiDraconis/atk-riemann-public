import MCore.RH.Analytic.CriticalEvaluationKernel
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MCore.RH.R0

open Complex

/-- A zeta zero strictly inside the critical strip but off the critical line. -/
structure OffLineStripZero where
  rho : ℂ
  hzero : riemannZeta rho = 0
  hpos : 0 < rho.re
  hlt : rho.re < 1
  hoff : rho.re ≠ 1 / 2

/-- A zero in the right half of the critical strip. -/
structure RightStripZero where
  rho : ℂ
  hzero : riemannZeta rho = 0
  hright : 1 / 2 < rho.re
  hlt : rho.re < 1

/-- Positive-strip points are never nonpositive integers. -/
theorem strip_point_ne_neg_nat
    {s : ℂ} (hs : 0 < s.re) :
    ∀ n : ℕ, s ≠ -n := by
  intro n h
  have hre := congrArg Complex.re h
  simp at hre
  have hn : (0 : ℝ) ≤ n := by positivity
  linarith

/-- A point strictly left of the critical line reflects to the right half-strip. -/
theorem reflect_left_strip_zero
    (z : OffLineStripZero) (hleft : z.rho.re < 1 / 2) :
    RightStripZero := by
  refine {
    rho := 1 - z.rho
    hzero := ?_
    hright := ?_
    hlt := ?_
  }
  · have hfe := riemannZeta_one_sub
      (strip_point_ne_neg_nat z.hpos)
      (by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith [z.hlt])
    rw [z.hzero, mul_zero] at hfe
    exact hfe
  · simp
    linarith
  · simp
    linarith [z.hpos]

/-- Every off-line zero in the strip yields a zero in the right half-strip. -/
theorem offLineStripZero_to_right
    (z : OffLineStripZero) :
    RightStripZero := by
  by_cases hright : 1 / 2 < z.rho.re
  · exact {
      rho := z.rho
      hzero := z.hzero
      hright := hright
      hlt := z.hlt
    }
  · have hle : z.rho.re ≤ 1 / 2 := le_of_not_gt hright
    have hleft : z.rho.re < 1 / 2 := lt_of_le_of_ne hle z.hoff
    exact reflect_left_strip_zero z hleft

#print axioms MCore.RH.R0.strip_point_ne_neg_nat
#print axioms MCore.RH.R0.reflect_left_strip_zero
#print axioms MCore.RH.R0.offLineStripZero_to_right

end MCore.RH.R0
