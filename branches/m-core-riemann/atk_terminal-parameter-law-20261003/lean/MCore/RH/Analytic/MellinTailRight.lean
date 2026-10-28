import MCore.RH.Analytic.MellinTailRightReduction
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace MCore.RH.R0

open Finset Filter MeasureTheory Topology Complex Asymptotics Set

/-- Partial sums of the constant coefficient sequence grow exactly linearly. -/
theorem one_partial_sum_bigO :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, (1 : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  have hEq :
      (fun n : ℕ => ∑ k ∈ Icc 1 n, (1 : ℝ)) =
        fun n : ℕ => (n : ℝ) := by
    funext n
    simp
  rw [hEq]
  simpa [Real.rpow_one] using (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)

/-- Abel summation representation of zeta by the floor function on Re(s)>1. -/
theorem riemannZeta_eq_floor_integral
    (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s =
      s * ∫ t : ℝ in Ioi 1,
        ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have h := LSeries_eq_mul_integral_of_nonneg
    (fun _ : ℕ => (1 : ℝ))
    (r := (1 : ℝ)) zero_le_one hs
    one_partial_sum_bigO (fun _ => zero_le_one)
  have hL :
      LSeries (fun _ : ℕ => (1 : ℂ)) s = riemannZeta s := by
    simpa using LSeries_one_eq_riemannZeta hs
  rw [hL] at h
  simpa using h

/-- The floor function is t - fract(t), cast to C. -/
theorem natFloor_cast_eq_sub_fract
    {t : ℝ} (ht : 0 ≤ t) :
    (((⌊t⌋₊ : ℕ) : ℂ)) = (t : ℂ) - (Int.fract t : ℂ) := by
  have hfloor : ((⌊t⌋₊ : ℕ) : ℤ) = ⌊t⌋ := by
    exact Int.natCast_floor_eq_floor ht
  rw [Int.fract]
  push_cast [hfloor]
  ring

/-- D1.1 closed directly from Abel summation. -/
theorem tailFormulaRight_realized : TailFormulaRight := by
  intro s hs
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : s ≠ 1 := by
    intro h; subst s; norm_num at hs
  have hz := riemannZeta_eq_floor_integral s hs
  have hmain :
      riemannZeta s =
        s * ((∫ t : ℝ in Ioi 1,
          (t : ℂ) ^ (-s)) -
          (∫ t : ℝ in Ioi 1,
            ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ))) := by
    rw [hz]
    congr 1
    rw [← integral_sub]
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [natFloor_cast_eq_sub_fract ht0.le]
      rw [sub_mul]
      have hpow :
          (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
        rw [← cpow_one (t : ℂ), ← cpow_add (ofReal_ne_zero.mpr ht0.ne')]
        congr 1
        ring
      rw [hpow]
      ring
    · exact integrableOn_Ioi_cpow_of_lt
        (by simp only [neg_re]; linarith) zero_lt_one
    · have hpow :
          IntegrableOn
            (fun t : ℝ => (t : ℂ) ^ (-s - 1))
            (Ioi 1) :=
        integrableOn_Ioi_cpow_of_lt
          (by simp only [sub_re, neg_re, one_re]; linarith)
          zero_lt_one
      apply Integrable.mono' hpow.norm
      · exact AEStronglyMeasurable.mul
          hpow.aestronglyMeasurable
          ((measurable_id.fract).ofReal.aestronglyMeasurable.restrict)
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        rw [norm_mul]
        have hfract : ‖(Int.fract t : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Int.fract_nonneg t)]
          exact (Int.fract_lt_one t).le
        calc
          ‖(t : ℂ) ^ (-s - 1)‖ * ‖(Int.fract t : ℂ)‖
              ≤ ‖(t : ℂ) ^ (-s - 1)‖ * 1 :=
            mul_le_mul_of_nonneg_left hfract (norm_nonneg _)
          _ = ‖(t : ℂ) ^ (-s - 1)‖ := by ring
  have hpowint :
      (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt
      (by simp only [neg_re]; linarith) zero_lt_one]
    simp
    field_simp [hs1]
    ring
  rw [hpowint] at hmain
  have := hmain
  field_simp [hs0, hs1] at this ⊢
  linear_combination this

#print axioms MCore.RH.R0.riemannZeta_eq_floor_integral
#print axioms MCore.RH.R0.tailFormulaRight_realized

end MCore.RH.R0
