import MCore.RH.NB.Projection

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- Norm of the residual of `chi` after orthogonal projection onto `V_N`. -/
noncomputable def dN (rho : D.GeneratorFamily) (N : ℕ) : ℝ :=
  ‖D.chi - (D.P rho N D.chi : D.H)‖

/-- Squared projection residual. This is the finite-stage NB defect used by the later chain. -/
noncomputable def DN (rho : D.GeneratorFamily) (N : ℕ) : ℝ :=
  (D.dN rho N) ^ 2

/-- The residual norm is nonnegative. -/
theorem dN_nonneg (rho : D.GeneratorFamily) (N : ℕ) :
    0 ≤ D.dN rho N := by
  exact norm_nonneg _

/-- The squared finite-stage defect is nonnegative. -/
theorem DN_nonneg (rho : D.GeneratorFamily) (N : ℕ) :
    0 ≤ D.DN rho N := by
  exact sq_nonneg _

end NBHilbertData
end MCore.RH.NB
