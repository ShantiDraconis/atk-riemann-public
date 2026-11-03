import Mathlib.Analysis.Complex.Norm

namespace MCore.RH.R0

open Complex

noncomputable def criticalLine (t : ℝ) : ℂ :=
  (1 / 2 : ℝ) + t * I

@[simp] theorem criticalLine_re (t : ℝ) :
    (criticalLine t).re = 1 / 2 := by
  simp [criticalLine]

@[simp] theorem criticalLine_im (t : ℝ) :
    (criticalLine t).im = t := by
  simp [criticalLine]

theorem criticalLine_norm_sq (t : ℝ) :
    ‖criticalLine t‖ ^ 2 = 1 / 4 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [criticalLine]
  ring

#print axioms MCore.RH.R0.criticalLine_norm_sq

end MCore.RH.R0
