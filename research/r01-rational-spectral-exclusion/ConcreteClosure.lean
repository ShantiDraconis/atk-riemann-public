import Closure
import DualMultipliers
import ATK.BarreiraZero

namespace R01

open ATK.Conditional.Riemann ATK.RiemannConcrete ATK.BaezDuarteBridge
open ATK.BarreiraZero ATK.DInfinito

/-- A finite upper certificate for the concrete Gram distance excludes a point. -/
theorem concrete_exclusion {s : ℂ} {N : ℕ} {U : ℝ}
    (hl : 1 / 2 < s.re) (hr : s.re < 1)
    (hcert : DN N ≤ U) (hstrict : U < barreira s) : riemannZeta s ≠ 0 :=
  exclusao hl hr (lt_of_le_of_lt hcert hstrict)

/-- Mellin and reflection specialized to the actual distances. -/
theorem concrete_strip_of_certificates (h : ArbitrarilySmallUpperCertificates DN) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 :=
  strip_of_mellin_certificates DN barreira h (fun _ hl hr => barreira_pos hl hr)
    (fun _ hl hr hz N => barreira_le_DN hz hl hr N)

/-- Arbitrarily small finite certificates force the concrete infimum to vanish. -/
theorem concrete_inf_zero (h : ArbitrarilySmallUpperCertificates DN) : dInf = 0 := by
  apply le_antisymm _ dInf_nonneg
  by_contra! hp
  obtain ⟨N, hN⟩ := h dInf hp
  have hle : dInf ≤ DN N :=
    ciInf_le ⟨0, by rintro _ ⟨n, rfl⟩; exact DN_nonneg n⟩ N
  exact (not_lt_of_ge hle) hN

theorem mathlib_rh_of_concrete_certificates (h : ArbitrarilySmallUpperCertificates DN) :
    RiemannHypothesis :=
  rh_of_dInf_eq_zero (concrete_inf_zero h)

/-- Uniform quantitative R01 for the concrete ATK distances, including N = 0. -/
def ConcreteLogRate : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, DN N ≤ K / Real.log ((N : ℝ) + 2)

/-- The quantitative premise gives a finite witness for every positive tolerance. -/
theorem certificates_of_log_rate (rate : ConcreteLogRate) :
    ArbitrarilySmallUpperCertificates DN := by
  obtain ⟨K, _, hK⟩ := rate
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (K / ε))
  have harg : Real.exp (K / ε) < (N : ℝ) + 2 := by linarith
  have hlog := Real.log_lt_log (Real.exp_pos (K / ε)) harg
  rw [Real.log_exp] at hlog
  have hpos : 0 < Real.log ((N : ℝ) + 2) :=
    Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) N])
  refine ⟨N, (hK N).trans_lt ((div_lt_iff₀ hpos).mpr ?_)⟩
  simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlog

theorem concrete_closure_of_log_rate (rate : ConcreteLogRate) :
    dInf = 0 ∧ RiemannHypothesis := by
  have h := certificates_of_log_rate rate
  exact ⟨concrete_inf_zero h, mathlib_rh_of_concrete_certificates h⟩


/-- Transfer the finite multiplier loss at the fixed cutoff to the concrete R01.
The two premises are the truncation comparison and the uniform witness bound. -/
theorem closure_of_modular_multipliers (C : ℝ) (hC : 0 ≤ C) (v : ℕ → ℕ → ℝ)
    (htransfer : ∀ N : ℕ, 2 ≤ N →
      DN N ≤ multiplierLoss N (100*N^5) 1 (v N) + 1/(N : ℝ))
    (hwitness : ∀ N : ℕ, 2 ≤ N →
      multiplierLoss N (100*N^5) 1 (v N) ≤ C / Real.log ((N : ℝ)+2)) :
    ConcreteLogRate ∧ dInf = 0 ∧ RiemannHypothesis := by
  let K := max (Real.log 3) (C+1)
  have rate : ConcreteLogRate := by
    refine ⟨K, le_trans (by linarith : 0 ≤ C+1) (le_max_right _ _), ?_⟩
    intro N
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hp : 0 < Real.log ((N : ℝ)+2) := Real.log_pos (by linarith)
    by_cases hN : 2 ≤ N
    · have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have he : Real.log ((N : ℝ)+2) ≤ N := by
        have hhalf : 0 < ((N : ℝ)+2)/2 := by linarith
        have h := Real.log_le_sub_one_of_pos hhalf
        rw [Real.log_div (by linarith : (N : ℝ)+2 ≠ 0) (by norm_num)] at h
        have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
        linarith
      have htail : 1/(N : ℝ) ≤ 1/Real.log ((N : ℝ)+2) :=
        one_div_le_one_div_of_le hp he
      calc
        DN N ≤ _ := htransfer N hN
        _ ≤ C/Real.log ((N : ℝ)+2) + 1/Real.log ((N : ℝ)+2) :=
          add_le_add (hwitness N hN) htail
        _ = (C+1)/Real.log ((N : ℝ)+2) := (add_div _ _ _).symm
        _ ≤ K/Real.log ((N : ℝ)+2) := div_le_div_of_nonneg_right (le_max_right _ _) hp.le
    · have hi : N ≤ 1 := by omega
      have hi' : (N : ℝ) ≤ 1 := by exact_mod_cast hi
      have hl : Real.log ((N : ℝ)+2) ≤ Real.log 3 :=
        Real.log_le_log (by linarith) (by linarith)
      apply (DN_le_one N).trans
      apply (le_div_iff₀ hp).mpr
      simpa only [one_mul] using hl.trans (le_max_left _ (C+1))
  exact ⟨rate, concrete_closure_of_log_rate rate⟩

end R01
