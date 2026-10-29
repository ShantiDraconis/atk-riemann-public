import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-
Material audit:
DNToZero_of_le_zero consumes a supplied pointwise upper bound. It is valid
transport, not a producer of that bound.
-/
theorem vanishingUpperBound_is_transport
    (rho : D.GeneratorFamily)
    (hupper : ∀ N : ℕ, D.DN rho N ≤ 0) :
    D.DNToZero rho :=
  D.DNToZero_of_le_zero rho hupper

#print axioms MCore.RH.NB.NBHilbertData.vanishingUpperBound_is_transport

end NBHilbertData
end MCore.RH.NB
