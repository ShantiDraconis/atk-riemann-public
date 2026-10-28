import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- Canonical name for the certified finite-stage squared-defect infimum. -/
noncomputable def delta (rho : D.GeneratorFamily) : ℝ :=
  D.DNLimit rho

/-- The canonical NB defect limit is nonnegative. -/
theorem delta_nonneg (rho : D.GeneratorFamily) :
    0 ≤ D.delta rho := by
  exact D.DNLimit_nonneg rho

/-- The finite-stage squared defects converge to their canonical infimum. -/
theorem tendsto_DN_delta (rho : D.GeneratorFamily) :
    Filter.Tendsto (D.DN rho) Filter.atTop (nhds (D.delta rho)) := by
  exact D.tendsto_DN_DNLimit rho

/-- Zero canonical defect is exactly the already-defined zero-defect convergence frontier.
This theorem deliberately does not prove either side. -/
theorem delta_eq_zero_iff_DNToZero (rho : D.GeneratorFamily) :
    D.delta rho = 0 ↔ D.DNToZero rho := by
  unfold delta
  exact (D.DNToZero_iff_DNLimit_eq_zero rho).symm

end NBHilbertData
end MCore.RH.NB
