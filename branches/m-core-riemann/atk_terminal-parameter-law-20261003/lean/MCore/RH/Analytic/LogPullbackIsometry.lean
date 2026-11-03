import MCore.RH.Analytic.MellinPlancherelReduction
import MCore.RH.R0.LpToAE
import MCore.RH.R0.GramIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.L2Space

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB
open MeasureTheory Set

/-- Literal real representative of the frozen residual. -/
noncomputable def residualRepresentativeR
    {N : ℕ} (c : Fin N → ℝ) (x : ℝ) : ℝ :=
  chiRepresentative x - ∑ i : Fin N, c i * rhoRepresentative i x

/-- The Hilbert residual has the expected literal real representative almost everywhere. -/
theorem concreteResidual_coeFn_ae
    {N : ℕ} (c : Fin N → ℝ) :
    (concreteResidual c : ℝ → ℝ) =ᵐ[zeroInfinityMeasure]
      residualRepresentativeR c := by
  have hcomb :
      concreteNBData.coefficientApproximantAt concreteGeneratorFamily N c =
        concreteFiniteCombination c := by
    rfl
  unfold concreteResidual
  rw [hcomb]
  filter_upwards [
    Lp.coeFn_sub concreteNBData.chi (concreteFiniteCombination c),
    concreteChi_coeFn_ae,
    concreteFiniteCombination_coeFn_ae c] with x hsub hchi hcomb'
  rw [hsub, hchi, hcomb']
  rfl

/-- Complex residual is exactly the real residual embedded in C. -/
theorem residualRepresentativeC_eq_ofReal
    {N : ℕ} (c : Fin N → ℝ) (x : ℝ) :
    residualRepresentativeC c x =
      (residualRepresentativeR c x : ℂ) := by
  unfold residualRepresentativeC rhoCombinationC residualRepresentativeR
  simp [chiRepresentativeC, rhoRepresentativeC]
  ring

/-- L2 norm square of the frozen residual as a literal real integral on (0,infinity). -/
theorem concreteResidual_norm_sq_eq_integral
    {N : ℕ} (c : Fin N → ℝ) :
    ‖concreteResidual c‖ ^ 2 =
      ∫ x : ℝ in Ioi 0, Complex.normSq (residualRepresentativeC c x) := by
  rw [← real_inner_self_eq_norm_sq]
  rw [MeasureTheory.L2.inner_def]
  change
    (∫ x : ℝ in Ioi 0, @inner ℝ ℝ _ _ (concreteResidual c x) (concreteResidual c x)) =
      ∫ x : ℝ in Ioi 0, Complex.normSq (residualRepresentativeC c x)
  apply integral_congr_ae
  filter_upwards [concreteResidual_coeFn_ae c] with x hx
  rw [hx]
  simp only [real_inner_eq_mul]
  rw [residualRepresentativeC_eq_ofReal]
  simp [Complex.normSq, pow_two]

/-- Derivative of u -> exp(-u), copied from the pinned Mellin-inversion change of variables. -/
theorem rexp_neg_deriv :
    ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt
        (Real.exp ∘ Neg.neg)
        (-Real.exp (-u))
        Set.univ u :=
  fun u _ =>
    mul_neg_one (Real.exp (-u)) ▸
      ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt

/-- Image of u -> exp(-u). -/
theorem rexp_neg_image :
    (Real.exp ∘ Neg.neg) '' (Set.univ : Set ℝ) = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

/-- Injectivity of u -> exp(-u). -/
theorem rexp_neg_injOn :
    (Set.univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn
    (Set.univ.mapsTo_univ _)

/-- Pointwise norm-square identity for the critical logarithmic pullback. -/
theorem criticalLogPullback_normSq
    {N : ℕ} (c : Fin N → ℝ) (u : ℝ) :
    Complex.normSq (criticalLogPullback c u) =
      Real.exp (-u) *
        Complex.normSq (residualRepresentativeC c (Real.exp (-u))) := by
  unfold criticalLogPullback
  rw [Complex.normSq_mul]
  have hexp :
      Complex.normSq ((Real.exp (-u / 2) : ℝ) : ℂ) =
        Real.exp (-u) := by
    simp [Complex.normSq, Real.exp_ne_zero]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- Pure change of variables x = exp(-u) for the residual norm square. -/
theorem residual_integral_eq_logPullback
    {N : ℕ} (c : Fin N → ℝ) :
    (∫ x : ℝ in Ioi 0,
      Complex.normSq (residualRepresentativeC c x)) =
      ∫ u : ℝ, Complex.normSq (criticalLogPullback c u) := by
  let g : ℝ → ℝ :=
    fun x => Complex.normSq (residualRepresentativeC c x)
  have hcv :=
    integral_image_eq_integral_abs_deriv_smul
      (s := (Set.univ : Set ℝ))
      MeasurableSet.univ
      rexp_neg_deriv
      rexp_neg_injOn
      g
  rw [rexp_neg_image] at hcv
  rw [hcv]
  apply integral_congr_ae
  filter_upwards with u
  have hpos : 0 < Real.exp (-u) := Real.exp_pos _
  simp only [Function.comp_apply, abs_neg, abs_of_pos hpos, smul_eq_mul, g]
  rw [criticalLogPullback_normSq]

/-- D3.1: complete logarithmic pullback isometry. -/
theorem d3_logPullbackIsometry_realized :
    ∀ {N : ℕ} (c : Fin N → ℝ),
      ‖concreteResidual c‖ ^ 2 =
        ∫ u : ℝ, Complex.normSq (criticalLogPullback c u) := by
  intro N c
  rw [concreteResidual_norm_sq_eq_integral c]
  exact residual_integral_eq_logPullback c

#print axioms MCore.RH.R0.concreteResidual_norm_sq_eq_integral
#print axioms MCore.RH.R0.residual_integral_eq_logPullback
#print axioms MCore.RH.R0.d3_logPullbackIsometry_realized

end MCore.RH.R0
