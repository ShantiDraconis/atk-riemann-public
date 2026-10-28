import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import IndeterminateRiemann.Transform

/-!
# A non-zero value of ζ under the transform

`riemannZeta_two : riemannZeta 2 = π ^ 2 / 6` is Mathlib's
(`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`).
-/

namespace IndeterminateRiemann

open Real in
/-- ζ(2) = π²/6 ≠ 0 is sent to 1: the transform only says "not a zero". -/
theorem transform_zeta_two : IndeterminateTransform (riemannZeta 2) = 1 := by
  apply indeterminate_invariance
  rw [riemannZeta_two]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact div_ne_zero (pow_ne_zero 2 hpi) (by norm_num)

end IndeterminateRiemann
