import MCore.RH.R0.LpToAE
import MCore.RH.R0.WeightedIntegrability
import MCore.RH.R0.WeightedIntegralLinearity
import MCore.RH.R0.WeightedScaling
import MCore.RH.R0.BaseMellinPositive
import MCore.RH.R0.ExponentialUniqueness
import MCore.RH.R0.GramExplicit

namespace MCore.RH.R0

open MCore.RH.NB
open MeasureTheory

/-- Fully assembled A1 producer from the five non-RH ingredients. -/
theorem concreteMomentBridge_realized (N : ℕ) : ConcreteMomentBridge N := by
  unfold ConcreteMomentBridge
  intro c hc s hs0 hs1
  have hae0 := concreteFiniteCombination_eq_zero_ae c hc
  have hae0' :
      (fun x : ℝ => ∑ i : Fin N, c i * rhoRepresentative i x)
        =ᵐ[(volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi 0)] 0 := by
    change
      (fun x : ℝ => ∑ i : Fin N, c i * rhoRepresentative i x)
        =ᵐ[zeroInfinityMeasure] 0
    exact hae0
  have hIntZero :
      (∫ x : ℝ in Set.Ioi 0,
        (∑ i : Fin N, c i * rhoRepresentative i x) * x ^ (s - 1)) = 0 := by
    calc
      (∫ x : ℝ in Set.Ioi 0,
        (∑ i : Fin N, c i * rhoRepresentative i x) * x ^ (s - 1))
          = ∫ x : ℝ in Set.Ioi 0, 0 := by
              apply integral_congr_ae
              filter_upwards [hae0'] with x hx
              rw [hx]
              simp
      _ = 0 := by simp
  rw [weighted_integral_finset_linearity c s hs0 hs1] at hIntZero
  have hscaleAll :
      (∑ i : Fin N, c i *
        (∫ x : ℝ in Set.Ioi 0, rhoRepresentative i x * x ^ (s - 1))) =
      concreteMomentPolynomial c s *
        (∫ x : ℝ in Set.Ioi 0, rhoRepresentative 0 x * x ^ (s - 1)) := by
    let B : ℝ :=
      ∫ x : ℝ in Set.Ioi 0, rhoRepresentative 0 x * x ^ (s - 1)
    have hscale :
        ∀ i : Fin N,
          (∫ x : ℝ in Set.Ioi 0, rhoRepresentative i x * x ^ (s - 1)) =
            mellinScale i s * B := by
      intro i
      simpa [B] using rho_weighted_integral_scaling i s hs0 hs1
    calc
      (∑ i : Fin N, c i *
        (∫ x : ℝ in Set.Ioi 0, rhoRepresentative i x * x ^ (s - 1)))
          = ∑ i : Fin N, c i * (mellinScale i s * B) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hscale i]
      _ = concreteMomentPolynomial c s * B := by
        calc
          (∑ i : Fin N, c i * (mellinScale i s * B))
              = ∑ i : Fin N, (c i * mellinScale i s) * B := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
          _ = (∑ i : Fin N, c i * mellinScale i s) * B := by
                rw [Finset.sum_mul]
          _ = concreteMomentPolynomial c s * B := by
                rfl
  rw [hscaleAll] at hIntZero
  have hbase :
      (∫ x : ℝ in Set.Ioi 0, rhoRepresentative 0 x * x ^ (s - 1)) ≠ 0 :=
    ne_of_gt (base_weighted_integral_pos s hs0 hs1)
  exact (mul_eq_zero.mp hIntZero).resolve_right hbase

/-- A3: finite concrete generators are linearly independent. -/
theorem concreteGeneratorFamily_linearIndependent (N : ℕ) :
    LinearIndependent ℝ (fun i : Fin N => concreteGeneratorFamily i) := by
  exact concreteGeneratorFamily_linearIndependent_of_moments N
    (concreteMomentBridge_realized N)
    (concreteMomentUniqueness_vandermonde N)

/-- B1: finite concrete Gram matrices are positive definite. -/
theorem concreteGramMatrix_posDef (N : ℕ) :
    (concreteGramMatrix N).PosDef := by
  rw [concreteGramMatrix_posDef_iff_linearIndependent]
  exact concreteGeneratorFamily_linearIndependent N

#print axioms MCore.RH.R0.concreteMomentBridge_realized
#print axioms MCore.RH.R0.concreteGeneratorFamily_linearIndependent
#print axioms MCore.RH.R0.concreteGramMatrix_posDef

end MCore.RH.R0
