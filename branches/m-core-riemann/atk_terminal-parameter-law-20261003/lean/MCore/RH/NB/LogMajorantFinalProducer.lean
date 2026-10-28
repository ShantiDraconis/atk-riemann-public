import MCore.RH.NB.ExactFinalProducer
import Mathlib

namespace MCore.RH.NB
namespace Final

noncomputable def logMajorant (K : ℝ) (N : ℕ) : ℝ :=
  K / Real.log ((N : ℝ) + 2)

theorem logMajorant_nonneg
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ N : ℕ, 0 ≤ logMajorant K N := by
  intro N
  unfold logMajorant
  have harg : (1 : ℝ) < (N : ℝ) + 2 := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  exact div_nonneg hK (Real.log_pos harg).le

theorem logMajorant_tendsto_zero
    (K : ℝ) :
    Filter.Tendsto (logMajorant K) Filter.atTop (nhds 0) := by
  unfold logMajorant
  have harg :
      Filter.Tendsto (fun N : ℕ => (N : ℝ) + 2)
        Filter.atTop Filter.atTop := by
    simpa using
      (Filter.Tendsto.atTop_add
        (tendsto_natCast_atTop_atTop : Filter.Tendsto ((↑) : ℕ → ℝ) Filter.atTop Filter.atTop)
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (2 : ℝ)) Filter.atTop (nhds 2)))
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp harg)

structure LogMajorantCertificate
    (D : NBHilbertData)
    (rho : D.GeneratorFamily) where
  K : ℝ
  hK : 0 ≤ K
  dn_le :
    ∀ N : ℕ, D.DN rho N ≤ logMajorant K N

noncomputable def vanishingUpperBound_of_logMajorant
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h : LogMajorantCertificate D rho) :
    D.VanishingUpperBound rho :=
  {
    eps := logMajorant h.K
    eps_nonneg := logMajorant_nonneg h.K h.hK
    dn_le := h.dn_le
    eps_tendsto_zero := logMajorant_tendsto_zero h.K
  }

theorem FINAL_ROOT_of_logMajorant
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h : LogMajorantCertificate D rho) :
    FINAL_ROOT D rho :=
  finalRoot_of_vanishingUpperBound D rho
    (vanishingUpperBound_of_logMajorant D rho h)

#print axioms MCore.RH.NB.Final.logMajorant_tendsto_zero
#print axioms MCore.RH.NB.Final.vanishingUpperBound_of_logMajorant
#print axioms MCore.RH.NB.Final.FINAL_ROOT_of_logMajorant

end Final
end MCore.RH.NB
