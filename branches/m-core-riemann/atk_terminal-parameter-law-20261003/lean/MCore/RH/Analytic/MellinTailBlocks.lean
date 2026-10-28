import MCore.RH.Analytic.MellinNearZero

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- Complex unit-block tail term for the fractional-part Mellin transform. -/
noncomputable def complexTailTerm (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in n..(n + 1),
    ((t : ℂ) ^ (-s - 1)) * ((t : ℂ) - n)

/-- On each positive integer block, the fractional-part integrand is the block term. -/
theorem fractionalTail_complex_block
    (n : ℕ) (hn : 0 < n) (s : ℂ) :
    (∫ t : ℝ in n..(n + 1),
      ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ)) =
      complexTailTerm n s := by
  unfold complexTailTerm
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by positivity)] at ht
  have hfloor : ⌊t⌋ = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast ht.1
    · exact_mod_cast ht.2
  rw [Int.fract, hfloor]
  norm_cast

/-- Exact complex Euler block formula. -/
theorem complexTailTerm_formula
    (n : ℕ) (hn : 0 < n) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    complexTailTerm n s =
      ((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s) -
      (n : ℂ) *
        (((n + 1 : ℂ) ^ (-s) - (n : ℂ) ^ (-s)) / (-s)) := by
  unfold complexTailTerm
  calc
    (∫ t : ℝ in n..(n + 1),
      ((t : ℂ) ^ (-s - 1)) * ((t : ℂ) - n)) =
      (∫ t : ℝ in n..(n + 1), (t : ℂ) ^ (-s)) -
        (n : ℂ) * (∫ t : ℝ in n..(n + 1), (t : ℂ) ^ (-s - 1)) := by
          rw [intervalIntegral.integral_sub]
          · rw [intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le (by positivity)] at ht
            have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast hn) ht.1
            rw [mul_sub, mul_comm _ (t : ℂ), ← cpow_add ht0.ne']
            congr 1 <;> ring
          · exact intervalIntegral.intervalIntegrable_cpow'
              (by simp only [neg_re]; linarith [show (0:ℝ) < n by exact_mod_cast hn])
          · exact (intervalIntegral.intervalIntegrable_cpow'
              (Or.inr ⟨by simpa using hs0, by
                rw [Set.mem_uIcc]; push_neg
                constructor <;> positivity⟩)).const_mul _
    _ = _ := by
      rw [integral_cpow, integral_cpow]
      · ring
      · right
        constructor
        · intro h
          apply hs0
          linear_combination h
        · rw [Set.mem_uIcc]
          push_neg
          constructor <;> positivity
      · right
        constructor
        · intro h
          apply hs1
          linear_combination h
        · rw [Set.mem_uIcc]
          push_neg
          constructor <;> positivity

#print axioms MCore.RH.R0.complexTailTerm_formula

end MCore.RH.R0
