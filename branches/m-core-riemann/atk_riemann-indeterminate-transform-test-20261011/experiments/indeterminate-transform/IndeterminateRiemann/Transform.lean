import Mathlib.Analysis.Complex.Basic

/-!
# The proposed transform, with the single change needed to compile

Same body and same proof as `SDCore.IndeterminateTransform` /
`SDCore.indeterminate_invariance`. The only change is `noncomputable`:
in Mathlib both `DecidableEq ℂ` and division on `ℂ` are noncomputable, so a
plain `def` cannot be compiled.

The extra lemmas make explicit what the transform is in Lean.
-/

namespace IndeterminateRiemann

/-- The proposed operator "I = 0/0". -/
noncomputable def IndeterminateTransform (z : ℂ) : ℂ :=
  if z = 0 then 0 else z / z

/-- Original theorem, original proof. -/
theorem indeterminate_invariance (z : ℂ) (h : z ≠ 0) :
    IndeterminateTransform z = 1 := by
  dsimp [IndeterminateTransform]
  split_ifs with h0
  · contradiction
  · exact div_self h

/-- In Lean, `0 / 0 = 0` by definition of division. -/
theorem zero_div_zero : (0 : ℂ) / 0 = 0 := div_zero 0

/-- Hence the transform is literally `z / z`; the `if` adds nothing. -/
theorem transform_eq_div_self (z : ℂ) : IndeterminateTransform z = z / z := by
  by_cases h : z = 0
  · simp [IndeterminateTransform, h]
  · simp [IndeterminateTransform, h]

/-- It only records whether `z` is zero. -/
theorem transform_eq_zero_iff (z : ℂ) : IndeterminateTransform z = 0 ↔ z = 0 := by
  by_cases h : z = 0
  · simp [IndeterminateTransform, h]
  · simp [IndeterminateTransform, h]

/-- Its only values are `0` and `1`. -/
theorem transform_values (z : ℂ) :
    IndeterminateTransform z = 0 ∨ IndeterminateTransform z = 1 := by
  by_cases h : z = 0
  · left
    simp [IndeterminateTransform, h]
  · right
    exact indeterminate_invariance z h

end IndeterminateRiemann
