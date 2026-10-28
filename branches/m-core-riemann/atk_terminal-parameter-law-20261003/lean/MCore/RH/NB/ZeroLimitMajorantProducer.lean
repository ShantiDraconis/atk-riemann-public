import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- Minimal forward producer for the zero-limit frontier:
any explicit nonnegative upper majorant converging to zero forces DN -> 0. -/
theorem DNToZero_of_vanishing_upper
    (rho : D.GeneratorFamily)
    (eps : ℕ → ℝ)
    (heps : Filter.Tendsto eps Filter.atTop (nhds 0))
    (hupper : ∀ N : ℕ, D.DN rho N ≤ eps N) :
    D.DNToZero rho := by
  unfold DNToZero
  exact squeeze_zero
    (fun N => D.DN_nonneg rho N)
    hupper
    heps

/-- The same minimal producer closes the canonical DNLimit goal directly. -/
theorem DNLimit_eq_zero_of_vanishing_upper
    (rho : D.GeneratorFamily)
    (eps : ℕ → ℝ)
    (heps : Filter.Tendsto eps Filter.atTop (nhds 0))
    (hupper : ∀ N : ℕ, D.DN rho N ≤ eps N) :
    D.DNLimit rho = 0 :=
  (D.DNToZero_iff_DNLimit_eq_zero rho).mp
    (D.DNToZero_of_vanishing_upper rho eps heps hupper)

#print axioms MCore.RH.NB.NBHilbertData.DNToZero_of_vanishing_upper
#print axioms MCore.RH.NB.NBHilbertData.DNLimit_eq_zero_of_vanishing_upper

end NBHilbertData
end MCore.RH.NB
