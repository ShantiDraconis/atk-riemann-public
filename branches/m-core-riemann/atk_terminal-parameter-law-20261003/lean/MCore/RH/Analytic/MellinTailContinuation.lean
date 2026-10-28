import MCore.RH.Analytic.MellinTailContinuationReduction
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace MCore.RH.R0

open Complex Set Filter Topology MeasureTheory Asymptotics

/-- Fractional-part tail kernel, cut off below 1. -/
noncomputable def fractionalTailKernel (t : ℝ) : ℂ :=
  Set.indicator (Ioi 1) (fun x : ℝ => (Int.fract x : ℂ)) t

theorem fractionalTailKernel_aestronglyMeasurable :
    AEStronglyMeasurable fractionalTailKernel := by
  exact ((measurable_id.fract).ofReal.indicator measurableSet_Ioi).aestronglyMeasurable

theorem fractionalTailKernel_norm_le_one (t : ℝ) :
    ‖fractionalTailKernel t‖ ≤ 1 := by
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [fractionalTailKernel, Set.indicator_of_mem ht]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  · rw [fractionalTailKernel, Set.indicator_of_not_mem ht, norm_zero]
    norm_num

/-- The cutoff fractional-part kernel is locally integrable on (0,∞). -/
theorem fractionalTailKernel_locallyIntegrable :
    LocallyIntegrableOn fractionalTailKernel (Ioi 0) := by
  refine (locallyIntegrableOn_const (s := Ioi (0 : ℝ)) (1 : ℂ)).mono_enorm
    fractionalTailKernel_aestronglyMeasurable ?_
  filter_upwards with t
  rw [enorm_le_iff_norm_le]
  simpa using fractionalTailKernel_norm_le_one t

/-- At infinity the cutoff fractional-part kernel is O(1). -/
theorem fractionalTailKernel_isBigO_atTop :
    fractionalTailKernel =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Eventually.of_forall ?_⟩
  intro t
  simpa using fractionalTailKernel_norm_le_one t

/-- Near 0 from the right the cutoff kernel is identically zero. -/
theorem fractionalTailKernel_eventually_zero_nhdsGT :
    fractionalTailKernel =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
  have hI : Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsGT_iff_exists_Ioc_subset]
    exact ⟨1, zero_lt_one, subset_rfl⟩
  filter_upwards [hI] with t ht
  rw [fractionalTailKernel, Set.indicator_of_not_mem]
  simpa only [mem_Ioi, not_lt] using ht.2

/-- Hence the cutoff kernel satisfies any polynomial bound near 0; exponent 0 is enough here. -/
theorem fractionalTailKernel_isBigO_nhdsGT :
    fractionalTailKernel =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (0 : ℝ)) := by
  exact fractionalTailKernel_eventually_zero_nhdsGT.trans_isBigO
    (Asymptotics.isBigO_zero _ _)

/-- The set-integral tail is exactly the Mellin transform of the cutoff kernel at -s. -/
theorem fractionalTailComplex_eq_mellin (s : ℂ) :
    fractionalTailComplex s = mellin fractionalTailKernel (-s) := by
  rw [fractionalTailComplex, mellin, fractionalTailKernel]
  simp_rw [← indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi]
  rw [inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  rfl

/-- The Mellin transform of the cutoff fractional-part kernel is holomorphic for Re(z)<0. -/
theorem fractionalTailKernel_mellin_differentiableAt
    {z : ℂ} (hz : z.re < 0) :
    DifferentiableAt ℂ (mellin fractionalTailKernel) z := by
  let b : ℝ := z.re - 1
  exact mellin_differentiableAt_of_isBigO_rpow
    fractionalTailKernel_locallyIntegrable
    (a := (0 : ℝ)) (b := b)
    (by simpa only [neg_zero, Real.rpow_zero] using fractionalTailKernel_isBigO_atTop)
    hz
    (by
      exact fractionalTailKernel_eventually_zero_nhdsGT.trans_isBigO
        (Asymptotics.isBigO_zero _ _))
    (by
      dsimp [b]
      linarith)

/-- Pointwise differentiability of the fractional tail on Re(s)>0. -/
theorem fractionalTailComplex_differentiableAt
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ fractionalTailComplex s := by
  have hneg : (-s).re < 0 := by
    simpa only [neg_re, neg_lt_zero] using hs
  have hdiff :
      DifferentiableAt ℂ (fun z : ℂ => mellin fractionalTailKernel (-z)) s := by
    exact (fractionalTailKernel_mellin_differentiableAt hneg).comp s
      differentiableAt_id.neg
  apply hdiff.congr_of_eventuallyEq
  exact Eventually.of_forall (fun z => (fractionalTailComplex_eq_mellin z).symm)

/-- Material producer for D1.2: the fractional tail is analytic throughout Re(s)>0. -/
theorem tailMellinAnalytic_realized : TailMellinAnalytic := by
  intro s hs
  have hspos : 0 < s.re := by
    simpa [positiveHalfPlane] using hs
  apply DifferentiableOn.analyticAt (s := positiveHalfPlane)
  · intro z hz
    have hzpos : 0 < z.re := by
      simpa [positiveHalfPlane] using hz
    exact (fractionalTailComplex_differentiableAt hzpos).differentiableWithinAt
  · exact (isOpen_lt continuous_const continuous_re).mem_nhds hspos

/-- D1.2 is fully realized from the concrete Mellin producer. -/
theorem tailAnalyticContinuation_realized :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      fractionalTailComplex s =
        1 / (s - 1) - riemannZeta s / s := by
  exact tailAnalyticContinuation_of_mellin tailMellinAnalytic_realized

#print axioms MCore.RH.R0.fractionalTailKernel_locallyIntegrable
#print axioms MCore.RH.R0.fractionalTailKernel_mellin_differentiableAt
#print axioms MCore.RH.R0.tailMellinAnalytic_realized
#print axioms MCore.RH.R0.tailAnalyticContinuation_realized

end MCore.RH.R0
