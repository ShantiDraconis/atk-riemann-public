import MCore.RH.Analytic.MellinConcrete
import MCore.RH.R0.RhoBasicFacts
import MCore.RH.R0.ChiMemLp
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace MCore.RH.R0

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology

/-- Complex rho is locally integrable on the positive half-line. -/
theorem rhoRepresentativeC_locallyIntegrableOn (n : ℕ) :
    LocallyIntegrableOn (rhoRepresentativeC n) (Ioi 0) := by
  refine (locallyIntegrableOn_const (s := Ioi (0 : ℝ)) (1 : ℂ)).mono
    ?_ ?_
  · exact
      (Complex.continuous_ofReal.measurable.comp
        (rhoRepresentative_measurable_public n)).aestronglyMeasurable
  · filter_upwards with x
    simpa [rhoRepresentativeC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rhoRepresentative_nonneg n x)] using
      (rhoRepresentative_le_one n x)

/-- Complex chi is locally integrable on the positive half-line. -/
theorem chiRepresentativeC_locallyIntegrableOn :
    LocallyIntegrableOn chiRepresentativeC (Ioi 0) := by
  refine (locallyIntegrableOn_const (s := Ioi (0 : ℝ)) (1 : ℂ)).mono
    ?_ ?_
  · exact
      (Complex.continuous_ofReal.measurable.comp
        chiRepresentative_measurable).aestronglyMeasurable
  · filter_upwards with x
    simpa [chiRepresentativeC, Complex.norm_real] using chiRepresentative_norm_le_one x

/-- Near zero every concrete generator is O(1). -/
theorem rhoRepresentativeC_isBigO_nhdsGT (n : ℕ) :
    rhoRepresentativeC n =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (0 : ℝ)) := by
  apply IsBigO.of_bound'
  filter_upwards with x
  rw [rhoRepresentativeC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (rhoRepresentative_nonneg n x)]
  simpa using rhoRepresentative_le_one n x

/-- At infinity every concrete generator is O(x^-1). -/
theorem rhoRepresentativeC_isBigO_atTop (n : ℕ) :
    rhoRepresentativeC n =O[atTop] (fun x : ℝ => x ^ (-1 : ℝ)) := by
  apply IsBigO.of_bound'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have ha : (1 : ℝ) ≤ ((rhoIndex n : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (rhoIndex_pos n)
  rw [rhoRepresentativeC, rhoRepresentative_tail n hx,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, Real.rpow_neg_one]
  have hden : 0 < ((rhoIndex n : ℕ) : ℝ) * x := mul_pos (by positivity) hx0
  have hxinv : |x⁻¹| = x⁻¹ := abs_of_pos (inv_pos.mpr hx0)
  rw [hxinv]
  simpa [one_div] using
    (one_div_le_one_div_of_le hx0 (by nlinarith :
      x ≤ ((rhoIndex n : ℕ) : ℝ) * x))

/-- Near zero the target is O(1). -/
theorem chiRepresentativeC_isBigO_nhdsGT :
    chiRepresentativeC =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (0 : ℝ)) := by
  apply IsBigO.of_bound'
  filter_upwards with x
  simpa [chiRepresentativeC, Complex.norm_real] using chiRepresentative_norm_le_one x

/-- At infinity the target vanishes, hence is O(x^-1). -/
theorem chiRepresentativeC_isBigO_atTop :
    chiRepresentativeC =O[atTop] (fun x : ℝ => x ^ (-1 : ℝ)) := by
  have hzero :
      chiRepresentativeC =ᶠ[atTop] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp [chiRepresentativeC, chiRepresentative, not_lt_of_ge hx]
  exact hzero.trans_isBigO (Asymptotics.isBigO_zero _ _)

/-- rho_n has a convergent Mellin transform throughout the critical strip. -/
theorem rhoRepresentativeC_mellinConvergent
    (n : ℕ) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (rhoRepresentativeC n) s := by
  exact mellinConvergent_of_isBigO_rpow
    (a := 1) (b := 0)
    (rhoRepresentativeC_locallyIntegrableOn n)
    (by simpa using rhoRepresentativeC_isBigO_atTop n)
    hs1
    (by simpa using rhoRepresentativeC_isBigO_nhdsGT n)
    hs0

/-- chi has a convergent Mellin transform throughout the critical strip. -/
theorem chiRepresentativeC_mellinConvergent
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent chiRepresentativeC s := by
  exact mellinConvergent_of_isBigO_rpow
    (a := 1) (b := 0)
    chiRepresentativeC_locallyIntegrableOn
    (by simpa using chiRepresentativeC_isBigO_atTop)
    hs1
    (by simpa using chiRepresentativeC_isBigO_nhdsGT)
    hs0

#print axioms MCore.RH.R0.rhoRepresentativeC_mellinConvergent
#print axioms MCore.RH.R0.chiRepresentativeC_mellinConvergent

end MCore.RH.R0
