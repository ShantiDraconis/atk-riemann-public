import MCore.RH.NB.HilbertData
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- `V_N` is finite-dimensional because it is spanned by the finite set of the first N generators. -/
theorem finiteDimensional_V (rho : D.GeneratorFamily) (N : ℕ) :
    Module.Finite ℝ (D.V rho N) := by
  rw [V]
  exact FiniteDimensional.span_of_finite ℝ (D.finite_finiteGenerators rho N)

/-- Finite-dimensional approximation spaces are closed in the ambient Hilbert space. -/
theorem isClosed_V (rho : D.GeneratorFamily) (N : ℕ) :
    IsClosed (D.V rho N : Set D.H) := by
  letI : Module.Finite ℝ (D.V rho N) := D.finiteDimensional_V rho N
  exact Submodule.closed_of_finiteDimensional (D.V rho N)

end NBHilbertData
end MCore.RH.NB
