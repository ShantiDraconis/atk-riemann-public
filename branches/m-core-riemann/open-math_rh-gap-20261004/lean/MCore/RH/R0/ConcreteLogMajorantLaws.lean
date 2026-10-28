import MCore.RH.R0.ConcreteLogMajorant

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/-- The logarithmic majorant is monotone in its constant K for every finite N. -/
theorem logMajorant_mono_K
    {K K' : ℝ}
    (hKK' : K ≤ K')
    (N : ℕ) :
    logMajorant K N ≤ logMajorant K' N := by
  unfold logMajorant
  have hlog : 0 ≤ Real.log ((N : ℝ) + 2) := by
    have harg : (1 : ℝ) ≤ (N : ℝ) + 2 := by
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    exact Real.log_nonneg harg
  exact div_le_div_of_nonneg_right hKK' hlog

/-- Any valid concrete logarithmic certificate remains valid after increasing K. -/
def ConcreteLogMajorantCertificate.weakenK
    (h : ConcreteLogMajorantCertificate)
    (K' : ℝ)
    (hKK' : h.K ≤ K') :
    ConcreteLogMajorantCertificate where
  K := K'
  hK := le_trans h.hK hKK'
  dn_le := by
    intro N
    exact (h.dn_le N).trans (logMajorant_mono_K hKK' N)

/-- Upward closure of the concrete producer constants. -/
theorem concrete_log_bound_upward_closed
    (K K' : ℝ)
    (hK : 0 ≤ K)
    (hKK' : K ≤ K')
    (hbound :
      ∀ N : ℕ,
        concreteNBData.DN concreteGeneratorFamily N ≤
          logMajorant K N) :
    ∀ N : ℕ,
      concreteNBData.DN concreteGeneratorFamily N ≤
        logMajorant K' N := by
  intro N
  exact (hbound N).trans (logMajorant_mono_K hKK' N)

/-- A larger admissible K still closes the exact same final root. -/
theorem concrete_log_bound_weakenK_closes_FINAL_ROOT
    (K K' : ℝ)
    (hK : 0 ≤ K)
    (hKK' : K ≤ K')
    (hbound :
      ∀ N : ℕ,
        concreteNBData.DN concreteGeneratorFamily N ≤
          logMajorant K N) :
    FINAL_ROOT concreteNBData concreteGeneratorFamily := by
  exact concrete_log_bound_closes_FINAL_ROOT
    K' (le_trans hK hKK')
    (concrete_log_bound_upward_closed K K' hK hKK' hbound)

#print axioms MCore.RH.R0.logMajorant_mono_K
#print axioms MCore.RH.R0.ConcreteLogMajorantCertificate.weakenK
#print axioms MCore.RH.R0.concrete_log_bound_upward_closed
#print axioms MCore.RH.R0.concrete_log_bound_weakenK_closes_FINAL_ROOT

end MCore.RH.R0
