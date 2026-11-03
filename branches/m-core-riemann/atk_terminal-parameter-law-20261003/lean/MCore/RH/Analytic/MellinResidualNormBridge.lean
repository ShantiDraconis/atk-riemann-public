import MCore.RH.Analytic.MellinPlancherelDecomposition
import MCore.RH.R0.LpToAE
import MCore.RH.R0.GramIntegral
import Mathlib.MeasureTheory.Function.L2Space

namespace MCore.RH.R0

open MeasureTheory Set
open MCore.RH.NB

/-- The Hilbert coefficient approximant is exactly the finite combination used in A1. -/
theorem coefficientApproximantAt_eq_concreteFiniteCombination
    {N : ℕ} (c : Fin N → ℝ) :
    concreteNBData.coefficientApproximantAt
      concreteGeneratorFamily N c =
      concreteFiniteCombination c := by
  rfl

/-- D3.0: the real Hilbert residual norm is the L2 integral of the literal complex residual. -/
theorem d3_residualRepresentativeNorm_realized :
    D3_ResidualRepresentativeNormBridge := by
  intro N c
  let rH : concreteNBData.H :=
    concreteNBData.chi -
      concreteNBData.coefficientApproximantAt
        concreteGeneratorFamily N c
  have hcomb :
      (concreteNBData.coefficientApproximantAt
        concreteGeneratorFamily N c : ℝ → ℝ)
        =ᵐ[zeroInfinityMeasure]
      (fun x : ℝ => ∑ i : Fin N, c i * rhoRepresentative i x) := by
    rw [coefficientApproximantAt_eq_concreteFiniteCombination c]
    exact concreteFiniteCombination_coeFn_ae c
  have hres :
      (rH : ℝ → ℝ) =ᵐ[zeroInfinityMeasure]
      (fun x : ℝ =>
        chiRepresentative x -
          ∑ i : Fin N, c i * rhoRepresentative i x) := by
    filter_upwards [
      Lp.coeFn_sub
        concreteNBData.chi
        (concreteNBData.coefficientApproximantAt
          concreteGeneratorFamily N c),
      concreteChi_coeFn_ae,
      hcomb] with x hsub hchi hc
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hchi, hc]
  change ‖rH‖ ^ 2 =
    ∫ x : ℝ in Ioi 0,
      Complex.normSq (residualRepresentativeC c x)
  rw [← real_inner_self_eq_norm_sq]
  rw [MeasureTheory.L2.inner_def]
  change
    (∫ x : ℝ,
      @inner ℝ ℝ _ ((rH : ℝ → ℝ) x) ((rH : ℝ → ℝ) x)
        ∂zeroInfinityMeasure) =
      ∫ x : ℝ in Ioi 0,
        Complex.normSq (residualRepresentativeC c x)
  change
    (∫ x : ℝ in Ioi 0,
      @inner ℝ ℝ _ ((rH : ℝ → ℝ) x) ((rH : ℝ → ℝ) x) dx) =
      ∫ x : ℝ in Ioi 0,
        Complex.normSq (residualRepresentativeC c x)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hres] with x hx
  simp only [real_inner_eq_mul]
  rw [hx]
  unfold residualRepresentativeC complexFiniteCombinationRepresentative
  simp [chiRepresentativeC, rhoRepresentativeC, Complex.normSq]
  ring

#print axioms MCore.RH.R0.coefficientApproximantAt_eq_concreteFiniteCombination
#print axioms MCore.RH.R0.d3_residualRepresentativeNorm_realized

end MCore.RH.R0
