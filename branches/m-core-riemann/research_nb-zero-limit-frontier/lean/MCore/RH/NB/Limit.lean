import MCore.RH.NB.Antitone
import Mathlib.Topology.Order.MonotoneConvergence

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- The finite-stage squared defect sequence is bounded below by zero. -/
theorem DN_bddBelow (rho : D.GeneratorFamily) :
    BddBelow (Set.range (D.DN rho)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact D.DN_nonneg rho N

/-- The canonical finite-stage defect limit is the infimum of the defect sequence. -/
noncomputable def DNLimit (rho : D.GeneratorFamily) : ℝ :=
  ⨅ N : ℕ, D.DN rho N

/-- The certified antitone nonnegative defect sequence converges to its infimum.
This theorem does not assert that the limit is zero. -/
theorem tendsto_DN_DNLimit (rho : D.GeneratorFamily) :
    Filter.Tendsto (D.DN rho) Filter.atTop (nhds (D.DNLimit rho)) := by
  unfold DNLimit
  exact tendsto_atTop_ciInf (D.DN_antitone rho) (D.DN_bddBelow rho)

/-- The canonical defect limit is nonnegative. -/
theorem DNLimit_nonneg (rho : D.GeneratorFamily) :
    0 ≤ D.DNLimit rho := by
  unfold DNLimit
  exact le_ciInf (fun N => D.DN_nonneg rho N)

end NBHilbertData
end MCore.RH.NB
