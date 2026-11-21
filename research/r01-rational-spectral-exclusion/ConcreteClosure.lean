import Closure
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

end R01
