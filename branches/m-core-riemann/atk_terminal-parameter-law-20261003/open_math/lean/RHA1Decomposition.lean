import MCore.RH.R0.LinearIndependentReduction
import MCore.RH.R0.LpToAE
import MCore.RH.R0.WeightedIntegrability
import MCore.RH.R0.BaseMellinPositive
import MCore.RH.R0.WeightedScaling
import MCore.RH.R0.WeightedIntegralLinearity
import MCore.RH.Analytic.MellinConcrete
import Lean

open scoped BigOperators
open Lean Elab Tactic

namespace MCore.RH.R0

open MeasureTheory Set

elab "a1_gap " name:str : tactic => do
  let g ← getMainGoal
  let fmt ← g.withContext do ppGoal g
  let body := toString fmt
  logInfo m!"[RH-A1-GAP:{name.getString}]\n{body}"
  IO.FS.writeFile s!"/tmp/rh_a1_gap_{name.getString}.txt" body

/-!
# A1 decomposition

This file is intentionally RED and outside the certified proof path.
It exposes every ingredient hidden inside ConcreteMomentBridge.
-/

/-- A1.0: zero in Lp gives an a.e. zero representative for the finite combination. -/
def A1_AEZeroBridge (N : ℕ) : Prop :=
  ∀ c : Fin N → ℝ,
    concreteFiniteCombination c = 0 →
    (fun x : ℝ => ∑ i : Fin N, c i * rhoRepresentative i x) =ᵐ[zeroInfinityMeasure] 0

/-- A1.1: each weighted rho is integrable on the positive half-line for 0<s<1. -/
def A1_WeightedIntegrability : Prop :=
  ∀ (n : ℕ) (s : ℝ), 0 < s → s < 1 →
    IntegrableOn
      (fun x : ℝ => rhoRepresentative n x * x ^ (s - 1))
      (Set.Ioi 0)

/-- A1.2: finite sums may be passed through the weighted integral. -/
def A1_WeightedIntegralLinearity (N : ℕ) : Prop :=
  ∀ (c : Fin N → ℝ) (s : ℝ), 0 < s → s < 1 →
    (∫ x : ℝ in Set.Ioi 0,
      (∑ i : Fin N, c i * rhoRepresentative i x) * x ^ (s - 1)) =
    ∑ i : Fin N, c i *
      (∫ x : ℝ in Set.Ioi 0, rhoRepresentative i x * x ^ (s - 1))

/-- A1.3: real Mellin scaling in exactly the form needed by the moment polynomial. -/
def A1_RealMellinScaling : Prop :=
  ∀ (n : ℕ) (s : ℝ), 0 < s → s < 1 →
    (∫ x : ℝ in Set.Ioi 0, rhoRepresentative n x * x ^ (s - 1)) =
      mellinScale n s *
        (∫ x : ℝ in Set.Ioi 0, rhoRepresentative 0 x * x ^ (s - 1))

/--
A1.4: cancellation lemma. No zeta identity is needed: on the real strip
the base Mellin integral is strictly positive because rho_0 >= 0 and is
positive on a set of positive measure.
-/
def A1_BaseMellinPositive : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    0 < ∫ x : ℝ in Set.Ioi 0, rhoRepresentative 0 x * x ^ (s - 1)

theorem DISCOVER_A1_AE_ZERO (N : ℕ) : A1_AEZeroBridge N := by
  unfold A1_AEZeroBridge
  intro c h
  exact concreteFiniteCombination_eq_zero_ae c h

theorem DISCOVER_A1_WEIGHTED_INTEGRABLE : A1_WeightedIntegrability := by
  unfold A1_WeightedIntegrability
  intro n s hs0 hs1
  exact A1_WeightedIntegrability_realized n s hs0 hs1

theorem DISCOVER_A1_LINEARITY (N : ℕ) : A1_WeightedIntegralLinearity N := by
  unfold A1_WeightedIntegralLinearity
  intro c s hs0 hs1
  exact weighted_integral_finset_linearity c s hs0 hs1

theorem DISCOVER_A1_REAL_SCALING : A1_RealMellinScaling := by
  unfold A1_RealMellinScaling
  intro n s hs0 hs1
  exact A1_RealMellinScaling_realized n s hs0 hs1

theorem DISCOVER_A1_BASE_POSITIVE : A1_BaseMellinPositive := by
  unfold A1_BaseMellinPositive
  intro s hs0 hs1
  exact A1_BaseMellinPositive_realized s hs0 hs1

/-- Once A1.0--A1.4 are proved, the original ConcreteMomentBridge follows. -/
theorem A1_components_to_ConcreteMomentBridge
    (N : ℕ)
    (hae : A1_AEZeroBridge N)
    (hint : A1_WeightedIntegrability)
    (hlin : A1_WeightedIntegralLinearity N)
    (hscale : A1_RealMellinScaling)
    (hpos : A1_BaseMellinPositive) :
    ConcreteMomentBridge N := by
  unfold ConcreteMomentBridge
  intro c hc s hs0 hs1
  have hae0 := hae c hc
  have hIntZero :
      (∫ x : ℝ in Set.Ioi 0,
        (∑ i : Fin N, c i * rhoRepresentative i x) * x ^ (s - 1)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae0] with x hx
    simp [hx]
  rw [hlin c s hs0 hs1] at hIntZero
  have hscaleAll :
      (∑ i : Fin N, c i *
        (∫ x : ℝ in Set.Ioi 0, rhoRepresentative i x * x ^ (s - 1))) =
      concreteMomentPolynomial c s *
        (∫ x : ℝ in Set.Ioi 0, rhoRepresentative 0 x * x ^ (s - 1)) := by
    simp_rw [hscale _ s hs0 hs1]
    simp [concreteMomentPolynomial, Finset.sum_mul]
  rw [hscaleAll] at hIntZero
  have hbase :
      (∫ x : ℝ in Set.Ioi 0, rhoRepresentative 0 x * x ^ (s - 1)) ≠ 0 :=
    ne_of_gt (hpos s hs0 hs1)
  exact (mul_eq_zero.mp hIntZero).resolve_right hbase

end MCore.RH.R0
