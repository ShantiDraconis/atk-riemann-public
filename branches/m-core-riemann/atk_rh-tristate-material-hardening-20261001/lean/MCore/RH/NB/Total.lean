import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

noncomputable def delta (rho : D.GeneratorFamily) : ℝ :=
  D.DNLimit rho

theorem delta_nonneg (rho : D.GeneratorFamily) :
    0 ≤ D.delta rho := by
  exact D.DNLimit_nonneg rho

theorem tendsto_DN_delta (rho : D.GeneratorFamily) :
    Filter.Tendsto (D.DN rho) Filter.atTop (nhds (D.delta rho)) := by
  exact D.tendsto_DN_DNLimit rho

theorem delta_eq_zero_iff_DNToZero (rho : D.GeneratorFamily) :
    D.delta rho = 0 ↔ D.DNToZero rho := by
  unfold delta
  exact (D.DNToZero_iff_DNLimit_eq_zero rho).symm

end NBHilbertData
end MCore.RH.NB
