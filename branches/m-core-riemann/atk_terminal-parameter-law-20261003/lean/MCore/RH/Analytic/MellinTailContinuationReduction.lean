import MCore.RH.Analytic.RegularizedZeta
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

namespace MCore.RH.R0

open Complex Set Filter Topology

/-- The complex fractional tail as a function of the Mellin parameter. -/
noncomputable def fractionalTailComplex (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 1,
    ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ)

/-- Positive real half-plane, the natural holomorphy domain of the tail integral. -/
def positiveHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

/-- The only analytic producer still needed for D1.2. -/
def TailMellinAnalytic : Prop :=
  ∀ s : ℂ, s ∈ positiveHalfPlane →
    AnalyticAt ℂ fractionalTailComplex s

/-- The pole-free zeta continuation is analytic throughout the positive half-plane. -/
theorem continuedFractionalTail_analyticOn :
    AnalyticOnNhd ℂ continuedFractionalTail positiveHalfPlane := by
  intro s hs
  exact continuedFractionalTail_analyticAt hs

/-- The fractional tail is analytic on the positive half-plane once its local Mellin producer exists. -/
theorem fractionalTailComplex_analyticOn
    (h : TailMellinAnalytic) :
    AnalyticOnNhd ℂ fractionalTailComplex positiveHalfPlane := by
  intro s hs
  exact h s hs

/-- The two analytic functions agree near s=2 by the Re(s)>1 Abel formula. -/
theorem fractionalTail_eventuallyEq_continued :
    fractionalTailComplex =ᶠ[𝓝 (2 : ℂ)] continuedFractionalTail := by
  have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  filter_upwards [hmem] with s hs
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : s ≠ 1 := by
    intro h; subst s; norm_num at hs
  rw [continuedFractionalTail_eq_zeta hs0 hs1]
  exact tailFormulaRight_realized s hs

/-- Identity theorem on the convex positive half-plane. -/
theorem fractionalTail_eq_continued
    (h : TailMellinAnalytic) :
    EqOn fractionalTailComplex continuedFractionalTail positiveHalfPlane := by
  have hF := fractionalTailComplex_analyticOn h
  have hG := continuedFractionalTail_analyticOn
  have hpre : IsPreconnected positiveHalfPlane := by
    exact (Complex.convex_halfSpace_re_gt (r := 0)).isPreconnected
  have h2 : (2 : ℂ) ∈ positiveHalfPlane := by
    norm_num [positiveHalfPlane]
  exact hF.eqOn_of_preconnected_of_eventuallyEq
    hG hpre h2 fractionalTail_eventuallyEq_continued

/-- D1.2: analytic continuation of the Euler tail formula to Re(s)>0 away from s=1. -/
theorem tailAnalyticContinuation_of_mellin
    (h : TailMellinAnalytic) :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      fractionalTailComplex s =
        1 / (s - 1) - riemannZeta s / s := by
  intro s hs hs1
  have heq := fractionalTail_eq_continued h (show s ∈ positiveHalfPlane by exact hs)
  rw [heq]
  exact continuedFractionalTail_eq_zeta (ne_zero_of_re_pos hs) hs1

#print axioms MCore.RH.R0.fractionalTail_eq_continued
#print axioms MCore.RH.R0.tailAnalyticContinuation_of_mellin

end MCore.RH.R0
