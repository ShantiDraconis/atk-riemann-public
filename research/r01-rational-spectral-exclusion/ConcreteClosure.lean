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

end R01
