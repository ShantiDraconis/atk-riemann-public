import MCore.RH.R0.GramIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace MCore.RH.R0

open MeasureTheory Set

/-- Multiplicative fractional-part autocorrelation kernel. -/
noncomputable def fractionalAutocorrelation (r : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0,
    (Int.fract (r * t) * Int.fract t) / (t ^ 2)

/-- Inversion x -> 1/x puts each concrete Gram entry into the arithmetic kernel form. -/
theorem concreteGramMatrix_inversion
    (N : ℕ) (i j : Fin N) :
    concreteGramMatrix N i j =
      ∫ t : ℝ in Ioi 0,
        (Int.fract (t / (((rhoIndex i : ℕ) : ℝ))) *
          Int.fract (t / (((rhoIndex j : ℕ) : ℝ)))) / (t ^ 2) := by
  rw [concreteGramMatrix_eq_setIntegral N i j]
  have hinv := integral_comp_rpow_Ioi
    (g := fun x : ℝ => rhoRepresentative i x * rhoRepresentative j x)
    (p := (-1 : ℝ)) (by norm_num : (-1 : ℝ) ≠ 0)
  symm at hinv
  calc
    (∫ x : ℝ in Ioi 0, rhoRepresentative i x * rhoRepresentative j x)
        = ∫ t : ℝ in Ioi 0,
            (|-1 : ℝ| * t ^ ((-1 : ℝ) - 1)) *
              (rhoRepresentative i (t ^ (-1 : ℝ)) *
                rhoRepresentative j (t ^ (-1 : ℝ))) := by
            simpa [smul_eq_mul] using hinv
    _ = ∫ t : ℝ in Ioi 0,
        (Int.fract (t / (((rhoIndex i : ℕ) : ℝ))) *
          Int.fract (t / (((rhoIndex j : ℕ) : ℝ)))) / (t ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      simp [rhoRepresentative, rhoBase, Real.rpow_neg_one, ht0.ne', abs_of_nonneg]
      field_simp

/-- C5: every Gram entry is one scaled value of the same autocorrelation function. -/
theorem concreteGramMatrix_eq_fractionalAutocorrelation
    (N : ℕ) (i j : Fin N) :
    concreteGramMatrix N i j =
      (1 / (((rhoIndex i : ℕ) : ℝ))) *
        fractionalAutocorrelation
          ((((rhoIndex i : ℕ) : ℝ)) / (((rhoIndex j : ℕ) : ℝ))) := by
  rw [concreteGramMatrix_inversion N i j]
  let a : ℝ := ((rhoIndex i : ℕ) : ℝ)
  let b : ℝ := ((rhoIndex j : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; exact_mod_cast rhoIndex_pos i
  have hb : 0 < b := by dsimp [b]; exact_mod_cast rhoIndex_pos j
  have hchange := integral_comp_mul_left_Ioi'
    (g := fun t : ℝ =>
      (Int.fract (t / a) * Int.fract (t / b)) / t ^ 2)
    (a := 0) ha
  rw [mul_zero] at hchange
  rw [← hchange]
  rw [integral_const_mul]
  change a *
      (∫ t : ℝ in Ioi 0,
        (Int.fract ((a * t) / a) * Int.fract ((a * t) / b)) /
          ((a * t) ^ 2)) = _
  apply Eq.trans ?_ rfl
  rw [setIntegral_congr_fun measurableSet_Ioi]
  · intro t ht
    have ht0 : 0 < t := ht
    have hane : a ≠ 0 := ha.ne'
    simp [fractionalAutocorrelation, hane]
    field_simp
    ring
  · dsimp [a, b]

/-- Reciprocity forced by symmetry of the original Gram kernel. -/
theorem fractionalAutocorrelation_reciprocity
    (r : ℝ) (hr : 0 < r) :
    fractionalAutocorrelation r =
      r * fractionalAutocorrelation (1 / r) := by
  unfold fractionalAutocorrelation
  have hchange := integral_comp_mul_left_Ioi'
    (g := fun t : ℝ =>
      (Int.fract (r * t) * Int.fract t) / t ^ 2)
    (a := 0) hr
  rw [mul_zero] at hchange
  rw [← hchange]
  rw [integral_const_mul]
  apply congrArg (fun z : ℝ => r * z)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hne : r ≠ 0 := hr.ne'
  simp [hne]
  field_simp
  ring

#print axioms MCore.RH.R0.concreteGramMatrix_eq_fractionalAutocorrelation
#print axioms MCore.RH.R0.fractionalAutocorrelation_reciprocity

end MCore.RH.R0
