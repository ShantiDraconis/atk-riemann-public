import MCore.RH.Analytic.MellinPlancherelDecomposition
import Mathlib.Analysis.MellinInversion

namespace MCore.RH.R0

open MeasureTheory Set

/-- Public image identity for u ↦ exp(-u). -/
theorem rexpNeg_image_univ :
    (fun u : ℝ => Real.exp (-u)) '' Set.univ = Set.Ioi 0 := by
  rw [show (fun u : ℝ => Real.exp (-u)) = Real.exp ∘ Neg.neg by rfl]
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

/-- Public injectivity of u ↦ exp(-u). -/
theorem rexpNeg_injOn_univ :
    Set.univ.InjOn (fun u : ℝ => Real.exp (-u)) := by
  intro x hx y hy hxy
  exact neg_injective (Real.exp_injective hxy)

/-- Public derivative formula for u ↦ exp(-u). -/
theorem rexpNeg_hasDerivWithinAt :
    ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun v : ℝ => Real.exp (-v))
        (- Real.exp (-u)) Set.univ u := by
  intro u hu
  exact ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt

/-- The logarithmic coordinate change is exactly L2-isometric on squared norms. -/
theorem logResidualIsometry_realized : LogResidualIsometry := by
  intro N c
  have hmeasure :
      (∫ x : ℝ, Complex.normSq (residualRepresentativeC c x) ∂zeroInfinityMeasure) =
        ∫ x : ℝ in Ioi 0,
          Complex.normSq (residualRepresentativeC c x) := by
    rfl
  rw [hmeasure]
  rw [← rexpNeg_image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ rexpNeg_hasDerivWithinAt rexpNeg_injOn_univ]
  apply integral_congr_ae
  filter_upwards with u
  have hexp : 0 < Real.exp (-u) := Real.exp_pos _
  simp only [logResidualC, Function.comp_apply, abs_neg, abs_of_pos hexp,
    smul_eq_mul]
  rw [Complex.normSq_mul]
  have hscalar :
      Complex.normSq ((Real.exp (-u / 2) : ℝ) : ℂ) = Real.exp (-u) := by
    simp [Complex.normSq_apply]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hscalar]
  ring

#print axioms MCore.RH.R0.rexpNeg_image_univ
#print axioms MCore.RH.R0.logResidualIsometry_realized

end MCore.RH.R0
