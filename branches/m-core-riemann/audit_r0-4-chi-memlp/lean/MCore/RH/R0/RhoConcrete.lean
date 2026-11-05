import MCore.RH.R0.ChiMemLp
import Mathlib.MeasureTheory.Function.Floor

namespace MCore.RH.R0

open MeasureTheory

/-- Concrete Nyman--Beurling generator `rho_n(x) = fract(1/(n*x))`.
The natural-number parameter is kept explicit so that the later finite-span
identification cannot silently change the generator family. -/
noncomputable def rhoRepresentative (n : ℕ) (x : BaseDomain) : ℝ :=
  Int.fract (1 / ((n : ℝ) * x))

/-- Every concrete generator is measurable. -/
theorem rhoRepresentative_measurable (n : ℕ) : Measurable (rhoRepresentative n) := by
  unfold rhoRepresentative
  fun_prop

/-- Fractional-part nonnegativity. -/
theorem rhoRepresentative_nonneg (n : ℕ) (x : BaseDomain) :
    0 ≤ rhoRepresentative n x := by
  exact Int.fract_nonneg _

/-- Fractional parts are strictly below one. -/
theorem rhoRepresentative_lt_one (n : ℕ) (x : BaseDomain) :
    rhoRepresentative n x < 1 := by
  exact Int.fract_lt_one _

/-- Pointwise absolute bound used on the finite near-origin piece. -/
theorem abs_rhoRepresentative_le_one (n : ℕ) (x : BaseDomain) :
    |rhoRepresentative n x| ≤ 1 := by
  rw [abs_of_nonneg (rhoRepresentative_nonneg n x)]
  exact (rhoRepresentative_lt_one n x).le

/-- The zero index degenerates to the zero function under Lean's totalized
 division. Positivity of the index is imposed for the intended NB family. -/
@[simp] theorem rhoRepresentative_zero (x : BaseDomain) :
    rhoRepresentative 0 x = 0 := by
  simp [rhoRepresentative]

/-- On the analytic tail `1/n < x`, the argument of `fract` lies in `[0,1)`,
so the concrete generator is exactly the reciprocal tail. This is the key
semantic reduction needed before proving square-integrability. -/
theorem rhoRepresentative_eq_reciprocal_of_tail
    (n : ℕ) (hn : 0 < n) (x : BaseDomain)
    (hx : (1 : ℝ) / (n : ℝ) < x) :
    rhoRepresentative n x = 1 / ((n : ℝ) * x) := by
  unfold rhoRepresentative
  rw [Int.fract_eq_self]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrecip : (1 : ℝ) / (n : ℝ) * (n : ℝ) = 1 := by
    field_simp
  have hnx : (1 : ℝ) < (n : ℝ) * x := by
    calc
      (1 : ℝ) = (1 / (n : ℝ)) * (n : ℝ) := hrecip.symm
      _ < x * (n : ℝ) := mul_lt_mul_of_pos_right hx hnR
      _ = (n : ℝ) * x := by ring
  have hnx0 : (0 : ℝ) < (n : ℝ) * x := lt_trans zero_lt_one hnx
  constructor
  · positivity
  · rw [div_lt_one hnx0]
    exact hnx

end MCore.RH.R0
