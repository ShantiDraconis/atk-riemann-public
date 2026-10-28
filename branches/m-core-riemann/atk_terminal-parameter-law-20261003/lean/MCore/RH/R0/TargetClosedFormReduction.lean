import MCore.RH.R0.GramIntegral
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace MCore.RH.R0

open MeasureTheory Set

/-- Universal fractional-part tail constant appearing in every target entry. -/
noncomputable def fractionalTailConstant : ℝ :=
  ∫ t : ℝ in Ioi 1, Int.fract t / (t ^ 2)

/-- The exact universal identity needed to introduce Euler--Mascheroni. -/
def FractionalTailEulerIdentity : Prop :=
  fractionalTailConstant = 1 - Real.eulerMascheroniConstant

/--
After x -> 1/(a t), every target entry has the same universal tail.
This is the exact change-of-variable statement C4 needs.
-/
def TargetEntryTransform : Prop :=
  ∀ (N : ℕ) (i : Fin N),
    let a : ℝ := ((rhoIndex i : ℕ) : ℝ)
    concreteTargetVector N i =
      Real.log a / a + fractionalTailConstant / a

/-- C4 follows mechanically from the transform plus the universal tail identity. -/
theorem target_closed_form_of_transform_tail
    (htransform : TargetEntryTransform)
    (htail : FractionalTailEulerIdentity)
    (N : ℕ) (i : Fin N) :
    concreteTargetVector N i =
      (Real.log ((rhoIndex i : ℕ) : ℝ) + 1 -
        Real.eulerMascheroniConstant) /
      (((rhoIndex i : ℕ) : ℝ)) := by
  have ha : (0 : ℝ) < ((rhoIndex i : ℕ) : ℝ) := by
    exact_mod_cast rhoIndex_pos i
  have h := htransform N i
  dsimp at h
  rw [htail] at h
  rw [concreteTargetVector_apply]
  calc
    concreteNBData.targetEntry concreteGeneratorFamily i
        = Real.log ((rhoIndex i : ℕ) : ℝ) / ((rhoIndex i : ℕ) : ℝ) +
          (1 - Real.eulerMascheroniConstant) / ((rhoIndex i : ℕ) : ℝ) := h
    _ = (Real.log ((rhoIndex i : ℕ) : ℝ) + 1 -
          Real.eulerMascheroniConstant) / ((rhoIndex i : ℕ) : ℝ) := by
      field_simp
      ring

/-- The interval (1/a,1) contributes exactly log(a)/a once fract(t)=t there. -/
def TargetElementaryIntervalIdentity : Prop :=
  ∀ a : ℝ, 1 ≤ a →
    (1 / a) *
      (∫ t : ℝ in Ioo (1 / a) 1, Int.fract t / (t ^ 2)) =
      Real.log a / a


/-- The elementary lower interval contributes exactly log(a)/a. -/
theorem target_elementary_interval_identity_realized :
    TargetElementaryIntervalIdentity := by
  intro a ha
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hdiv0 : 0 < 1 / a := one_div_pos.mpr ha0
  have hcongr :
      (∫ t : ℝ in Ioo (1 / a) 1, Int.fract t / (t ^ 2)) =
        ∫ t : ℝ in Ioo (1 / a) 1, t⁻¹ := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have ht0 : 0 < t := hdiv0.trans ht.1
    have ht1 : t < 1 := ht.2
    change Int.fract t / t ^ 2 = t⁻¹
    rw [Int.fract_eq_self.2 ⟨ht0.le, ht1⟩]
    field_simp [ht0.ne']
    ring
  rw [hcongr]
  rw [← integral_Ioc_eq_integral_Ioo]
  have hdiv1 : 1 / a ≤ (1 : ℝ) := by
    rw [div_le_iff₀ ha0]
    simpa using ha
  have hint :
      (∫ t : ℝ in Ioc (1 / a) 1, t⁻¹) =
        Real.log a := by
    rw [← intervalIntegral.integral_of_le hdiv1]
    rw [intervalIntegral.integral_inv_of_pos hdiv0 zero_lt_one]
    rw [one_div_div]
    simp [ha0.ne']
  rw [hint]
  ring

#print axioms MCore.RH.R0.target_elementary_interval_identity_realized
#print axioms MCore.RH.R0.target_closed_form_of_transform_tail

end MCore.RH.R0
