import MCore.RH.R0.TargetClosedFormReduction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

namespace MCore.RH.R0

open MeasureTheory Set

/-- On one positive integer block, fractional part is literally t-k. -/
theorem fract_eq_sub_nat_on_Ico
    (k : ℕ) (t : ℝ) (ht : t ∈ Ico (k : ℝ) (k + 1 : ℝ)) :
    Int.fract t = t - k := by
  rw [Int.fract]
  rw [Int.floor_eq_on_Ico (k : ℤ) t]
  · norm_num
  · simpa using ht

/--
Exact contribution of one unit block to the universal fractional tail.
-/
theorem fractionalTail_block
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ t : ℝ in Ioc (k : ℝ) (k + 1 : ℝ),
      Int.fract t / (t ^ 2)) =
      Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) -
        1 / (((k + 1 : ℕ) : ℝ)) := by
  rw [← integral_Ico_eq_integral_Ioc]
  have hpt :
      ∀ t ∈ Ico (k : ℝ) (k + 1 : ℝ),
        Int.fract t / (t ^ 2) =
          t⁻¹ - (k : ℝ) * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
      exact hk0.trans_le ht.1
    rw [fract_eq_sub_nat_on_Ico k t ht]
    rw [show t ^ (-2 : ℝ) = 1 / (t ^ 2) by
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      field_simp]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ico hpt]
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast Nat.le_add_right k 1)]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_inv_of_pos]
    · rw [intervalIntegral.integral_const_mul]
      rw [Real.integral_rpow]
      · field_simp
        ring_nf
        rw [Real.log_div (by positivity) (by positivity)]
        ring
      · right
        constructor
        · norm_num
        · rw [Set.mem_uIcc]
          push_neg
          constructor <;> positivity
    · positivity
    · positivity
  · exact intervalIntegrable_inv_iff.mpr (by
      rw [Set.mem_uIcc]
      push_neg
      constructor <;> positivity)
  · exact (Real.intervalIntegrable_rpow' (by norm_num : (-2 : ℝ) ≠ -1) (by
      rw [Set.mem_uIcc]
      push_neg
      constructor <;> positivity)).const_mul _

#print axioms MCore.RH.R0.fractionalTail_block

end MCore.RH.R0
