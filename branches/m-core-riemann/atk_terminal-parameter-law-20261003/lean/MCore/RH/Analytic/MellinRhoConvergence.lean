import MCore.RH.Analytic.MellinRhoClosedForm
import MCore.RH.R0.RhoBasicFacts
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace MCore.RH.R0

open Complex Set Filter MeasureTheory Asymptotics

theorem rhoRepresentativeC_locallyIntegrable (n : ℕ) :
    LocallyIntegrableOn (rhoRepresentativeC n) (Ioi 0) := by
  refine (locallyIntegrableOn_const (s := Ioi (0 : ℝ)) (1 : ℂ)).mono_enorm
    ((rhoRepresentative_measurable_public n).ofReal.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [enorm_le_iff_norm_le, rhoRepresentativeC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (rhoRepresentative_nonneg n x)]
  exact rhoRepresentative_le_one n x

theorem rhoRepresentativeC_isBigO_nhdsGT (n : ℕ) :
    rhoRepresentativeC n =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (0 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  rw [Real.rpow_zero, rhoRepresentativeC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (rhoRepresentative_nonneg n x)]
  exact rhoRepresentative_le_one n x

theorem rhoRepresentativeC_isBigO_atTop (n : ℕ) :
    rhoRepresentativeC n =O[atTop] (fun x : ℝ => x ^ (-1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [rhoRepresentativeC, rhoRepresentative_tail n hx, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg_one hx0.le]
  have ha : (1 : ℝ) ≤ ((rhoIndex n : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (rhoIndex_pos n)
  have hden : 0 < ((rhoIndex n : ℕ) : ℝ) * x := by positivity
  rw [one_div, one_div]
  exact inv_le_inv₀ hden hx0 |>.2 (by nlinarith)

theorem rhoRepresentativeC_mellinConvergent
    (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (rhoRepresentativeC n) s := by
  exact mellinConvergent_of_isBigO_rpow
    (rhoRepresentativeC_locallyIntegrable n)
    (a := (1 : ℝ)) (b := (0 : ℝ))
    (rhoRepresentativeC_isBigO_atTop n) hs1
    (rhoRepresentativeC_isBigO_nhdsGT n) hs0

#print axioms MCore.RH.R0.rhoRepresentativeC_mellinConvergent

end MCore.RH.R0
