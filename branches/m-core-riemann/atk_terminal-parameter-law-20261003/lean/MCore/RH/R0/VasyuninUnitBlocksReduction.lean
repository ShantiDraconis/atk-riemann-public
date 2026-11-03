import MCore.RH.R0.VasyuninCoprimeBasics

namespace MCore.RH.R0

open MeasureTheory Set Filter Topology

/-- The only analytic input needed to pass from finite block sums to V2. -/
def RationalAutocorrelationIntegrable : Prop :=
  ∀ h k : ℕ, 0 < h → 0 < k →
    IntegrableOn (rationalAutocorrelationIntegrand h k) (Ioi 0)

/-- Truncated block sums tend to the full rational autocorrelation integral. -/
theorem rationalAutocorrelation_partial_tendsto
    (hint : RationalAutocorrelationIntegrable)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    Tendsto
      (fun N : ℕ =>
        ∑ n in Finset.range N,
          ∫ t : ℝ in Ioc (n : ℝ) (n + 1),
            rationalAutocorrelationIntegrand h k t)
      atTop
      (𝓝 (fractionalAutocorrelation ((h : ℝ) / (k : ℝ)))) := by
  have hInt := hint h k hh hk
  have hblocks := fun N => rationalAutocorrelation_finite_blocks h k N hInt
  have hlim :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in (0 : ℝ)..(N : ℝ),
            rationalAutocorrelationIntegrand h k t)
        atTop
        (𝓝 (∫ t : ℝ in Ioi 0, rationalAutocorrelationIntegrand h k t)) := by
    exact intervalIntegral_tendsto_integral_Ioi 0 hInt tendsto_natCast_atTop_atTop
  have hlim' :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Ioc 0 N,
            rationalAutocorrelationIntegrand h k t)
        atTop
        (𝓝 (∫ t : ℝ in Ioi 0, rationalAutocorrelationIntegrand h k t)) := by
    simpa [intervalIntegral.integral_of_le (Nat.cast_nonneg _)] using hlim
  rw [fractionalAutocorrelation_eq_rationalIntegral h k]
  exact hlim'.congr' (Eventually.of_forall fun N => (hblocks N).symm)

/-- V2 follows from the single global integrability producer. -/
theorem rationalAutocorrelation_unitBlock_hasSum
    (hint : RationalAutocorrelationIntegrable)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    HasSum
      (fun n : ℕ =>
        ∫ t : ℝ in Ioc (n : ℝ) (n + 1),
          rationalAutocorrelationIntegrand h k t)
      (fractionalAutocorrelation ((h : ℝ) / (k : ℝ))) := by
  have hInt := hint h k hh hk
  have hnorm :
      Summable
        (fun n : ℕ =>
          ‖∫ t : ℝ in Ioc (n : ℝ) (n + 1),
            rationalAutocorrelationIntegrand h k t‖) := by
    have hglobal :
        HasSum
          (fun n : ℕ =>
            ∫ t : ℝ in Ioc (n : ℝ) (n + 1),
              ‖rationalAutocorrelationIntegrand h k t‖)
          (∫ t : ℝ in Ioi 0,
            ‖rationalAutocorrelationIntegrand h k t‖) := by
      -- This countable partition is the remaining measure-theoretic bookkeeping.
      -- It is intentionally isolated to one local proof obligation.
      rw [← hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
      simpa [← rationalAutocorrelation_finite_blocks h k]
        using
          (intervalIntegral_tendsto_integral_Ioi 0 hInt.norm
            tendsto_natCast_atTop_atTop)
    exact (hglobal.summable.mono fun n => norm_integral_le_integral_norm)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hnorm]
  exact rationalAutocorrelation_partial_tendsto hint h k hh hk

#print axioms MCore.RH.R0.rationalAutocorrelation_partial_tendsto
#print axioms MCore.RH.R0.rationalAutocorrelation_unitBlock_hasSum

end MCore.RH.R0
