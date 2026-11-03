import MCore.RH.R0.VasyuninGCD

namespace MCore.RH.R0

open MeasureTheory Set

/-- Coprime positive indices are already reduced. -/
theorem reduced_indices_of_coprime
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    reducedNumerator h k = h ∧ reducedDenominator h k = k := by
  have hgcd : Nat.gcd h k = 1 := hcop.gcd_eq_one
  constructor <;> simp [reducedNumerator, reducedDenominator, hgcd]

/-- Rational autocorrelation integrand used in the coprime Vasyunin calculation. -/
noncomputable def rationalAutocorrelationIntegrand (h k : ℕ) (t : ℝ) : ℝ :=
  (Int.fract (((h : ℝ) / (k : ℝ)) * t) * Int.fract t) / t ^ 2

/-- V1 is definitional once the rational integrand is named. -/
theorem fractionalAutocorrelation_eq_rationalIntegral
    (h k : ℕ) :
    fractionalAutocorrelation ((h : ℝ) / (k : ℝ)) =
      ∫ t : ℝ in Ioi 0, rationalAutocorrelationIntegrand h k t := by
  rfl

/-- Finite block decomposition on (0,N], conditional only on integrability. -/
theorem rationalAutocorrelation_finite_blocks
    (h k N : ℕ)
    (hint : IntegrableOn (rationalAutocorrelationIntegrand h k) (Ioi 0)) :
    (∫ t : ℝ in Ioc 0 N, rationalAutocorrelationIntegrand h k t) =
      ∑ n in Finset.range N,
        ∫ t : ℝ in Ioc (n : ℝ) (n + 1),
          rationalAutocorrelationIntegrand h k t := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hN : (0 : ℝ) ≤ N := by positivity
      have hstep :
          Ioc (0 : ℝ) (N + 1) =
            Ioc (0 : ℝ) N ∪ Ioc (N : ℝ) (N + 1) := by
        ext x
        simp only [mem_Ioc, mem_union]
        constructor
        · intro hx
          by_cases hle : x ≤ N
          · exact Or.inl ⟨hx.1, hle⟩
          · exact Or.inr ⟨lt_of_not_ge hle, hx.2⟩
        · rintro (hx | hx)
          · exact ⟨hx.1, hx.2.trans (by linarith)⟩
          · exact ⟨hx.1.trans_le hN, hx.2⟩
      rw [hstep]
      rw [setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
      · rw [ih]
        simp [Finset.sum_range_succ]
      · exact hint.mono_set (by intro x hx; exact hx.1)
      · exact hint.mono_set (by intro x hx; linarith [hx.1])

#print axioms MCore.RH.R0.reduced_indices_of_coprime
#print axioms MCore.RH.R0.fractionalAutocorrelation_eq_rationalIntegral
#print axioms MCore.RH.R0.rationalAutocorrelation_finite_blocks

end MCore.RH.R0
