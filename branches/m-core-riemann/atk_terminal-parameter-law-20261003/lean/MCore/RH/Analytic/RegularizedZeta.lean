import MCore.RH.Analytic.MellinTailRight
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.RemovableSingularity

namespace MCore.RH.R0

open Complex Set Filter Topology

/-- Riemann zeta with its simple pole at 1 removed. -/
noncomputable def regularizedZeta (s : ℂ) : ℂ :=
  Function.update
    (fun z : ℂ => riemannZeta z - 1 / (z - 1))
    1
    (Real.eulerMascheroniConstant : ℂ)
    s

@[simp] theorem regularizedZeta_one :
    regularizedZeta 1 = (Real.eulerMascheroniConstant : ℂ) := by
  simp [regularizedZeta]

theorem regularizedZeta_eq
    {s : ℂ} (hs : s ≠ 1) :
    regularizedZeta s = riemannZeta s - 1 / (s - 1) := by
  simp [regularizedZeta, hs]

/-- The regularized zeta function is continuous at the removed pole. -/
theorem regularizedZeta_continuousAt_one :
    ContinuousAt regularizedZeta 1 := by
  rw [regularizedZeta, continuousAt_update_same]
  exact tendsto_riemannZeta_sub_one_div

/-- The regularized zeta function is analytic at s=1 by removability. -/
theorem regularizedZeta_analyticAt_one :
    AnalyticAt ℂ regularizedZeta 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [mem_compl_singleton_iff] at hs
    apply DifferentiableAt.congr_of_eventuallyEq
    · exact (differentiableAt_riemannZeta hs).sub
        ((differentiableAt_const _).div
          (differentiableAt_id.sub_const _)
          (sub_ne_zero.mpr hs))
    · filter_upwards [eventually_ne_nhds hs] with t ht
      simp [regularizedZeta, ht]
  · exact regularizedZeta_continuousAt_one

/-- Away from 1 the regularized expression is holomorphic by ordinary zeta analyticity. -/
theorem regularizedZeta_analyticAt
    {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ regularizedZeta s := by
  let U : Set ℂ := {1}ᶜ
  apply DifferentiableOn.analyticAt (s := U)
  · intro z hz
    have hz1 : z ≠ 1 := by
      simpa [U] using hz
    have hbase :
        DifferentiableAt ℂ
          (fun w : ℂ => riemannZeta w - 1 / (w - 1)) z := by
      exact (differentiableAt_riemannZeta hz1).sub
        ((differentiableAt_const _).div
          (differentiableAt_id.sub_const _)
          (sub_ne_zero.mpr hz1))
    have hreg : DifferentiableAt ℂ regularizedZeta z := by
      apply hbase.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz1] with t ht
      simp [regularizedZeta, ht]
    exact hreg.differentiableWithinAt
  · exact isOpen_compl_singleton.mem_nhds hs

/-- The pole-removed zeta is analytic everywhere. -/
theorem regularizedZeta_analytic :
    ∀ s : ℂ, AnalyticAt ℂ regularizedZeta s := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact regularizedZeta_analyticAt_one
  · exact regularizedZeta_analyticAt hs

/-- Pole-free continuation of the right-tail formula. -/
noncomputable def continuedFractionalTail (s : ℂ) : ℂ :=
  (1 - regularizedZeta s) / s

/-- On the positive half-plane the continued expression is analytic. -/
theorem continuedFractionalTail_analyticAt
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ continuedFractionalTail s := by
  unfold continuedFractionalTail
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  exact AnalyticAt.div
    (analyticAt_const.sub (regularizedZeta_analytic s))
    analyticAt_id
    hs0

/-- Away from s=1 this is exactly the familiar zeta expression. -/
theorem continuedFractionalTail_eq_zeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    continuedFractionalTail s =
      1 / (s - 1) - riemannZeta s / s := by
  rw [continuedFractionalTail, regularizedZeta_eq hs1]
  field_simp [hs0, hs1]
  ring

#print axioms MCore.RH.R0.regularizedZeta_analyticAt_one
#print axioms MCore.RH.R0.continuedFractionalTail_analyticAt
#print axioms MCore.RH.R0.continuedFractionalTail_eq_zeta

end MCore.RH.R0
