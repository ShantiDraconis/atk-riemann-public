import MCore.RH.R0.RhoConcrete

namespace MCore.RH.R0

open MeasureTheory Set

/-- Public measurable representative lemma for downstream A1 bridges. -/
theorem rhoRepresentative_measurable_public (n : ℕ) :
    Measurable (rhoRepresentative n) := by
  unfold rhoRepresentative rhoBase rhoIndex
  exact (measurable_const.div (measurable_const.mul measurable_id)).fract

/-- Uniform lower bound from fractional-part arithmetic. -/
theorem rhoRepresentative_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ rhoRepresentative n x := by
  exact Int.fract_nonneg _

/-- Uniform strict upper bound from fractional-part arithmetic. -/
theorem rhoRepresentative_lt_one (n : ℕ) (x : ℝ) :
    rhoRepresentative n x < 1 := by
  exact Int.fract_lt_one _

/-- Convenient weak upper bound. -/
theorem rhoRepresentative_le_one (n : ℕ) (x : ℝ) :
    rhoRepresentative n x ≤ 1 := by
  exact le_of_lt (rhoRepresentative_lt_one n x)

/-- Exact tail formula used by weighted-integrability arguments. -/
theorem rhoRepresentative_tail (n : ℕ) {x : ℝ} (hx : 1 < x) :
    rhoRepresentative n x = 1 / (((rhoIndex n : ℕ) : ℝ) * x) := by
  unfold rhoRepresentative rhoBase
  apply Int.fract_eq_self.2
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < ((rhoIndex n : ℕ) : ℝ) := by
    exact_mod_cast rhoIndex_pos n
  have hden : 0 < ((rhoIndex n : ℕ) : ℝ) * x := mul_pos ha0 hx0
  constructor
  · exact le_of_lt (one_div_pos.mpr hden)
  · rw [div_lt_one hden]
    have ha : (1 : ℝ) ≤ ((rhoIndex n : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.2 (rhoIndex_pos n)
    nlinarith

/-- Existing L2 membership, re-exported under an A1-facing name. -/
theorem rhoRepresentative_memLp_two_public (n : ℕ) :
    MemLp (rhoRepresentative n) twoExponent zeroInfinityMeasure :=
  rho_memLp_two n

#print axioms MCore.RH.R0.rhoRepresentative_measurable_public
#print axioms MCore.RH.R0.rhoRepresentative_tail
#print axioms MCore.RH.R0.rhoRepresentative_memLp_two_public

end MCore.RH.R0
