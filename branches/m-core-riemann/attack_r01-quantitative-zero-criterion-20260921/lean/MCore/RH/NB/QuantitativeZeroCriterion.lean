import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- The canonical infimum is below every finite-stage defect. -/
theorem DNLimit_le_stage
    (rho : D.GeneratorFamily) (N : ℕ) :
    D.DNLimit rho ≤ D.DN rho N := by
  unfold DNLimit
  exact ciInf_le (D.DN_bddBelow rho) N

/-- Quantitative target: finite-stage defects become arbitrarily small.
This is strictly the estimate that the analytic residue argument now has to
supply; all finite-prefix bookkeeping has been removed from the frontier. -/
def DNArbitrarilySmall (rho : D.GeneratorFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, D.DN rho N < ε

/-- Any arbitrarily-small finite-stage estimate forces the canonical limit to
be zero. No RH assumption is used in this order-theoretic step. -/
theorem DNLimit_eq_zero_of_arbitrarily_small
    (rho : D.GeneratorFamily)
    (hsmall : D.DNArbitrarilySmall rho) :
    D.DNLimit rho = 0 := by
  have hnonneg : 0 ≤ D.DNLimit rho := D.DNLimit_nonneg rho
  by_contra hne
  have hpos : 0 < D.DNLimit rho :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  rcases hsmall (D.DNLimit rho) hpos with ⟨N, hN⟩
  have hle : D.DNLimit rho ≤ D.DN rho N :=
    D.DNLimit_le_stage rho N
  exact (not_lt_of_ge hle) hN

/-- Hence the R01 endpoint is reduced to one quantitative estimate. -/
theorem DNToZero_of_arbitrarily_small
    (rho : D.GeneratorFamily)
    (hsmall : D.DNArbitrarilySmall rho) :
    D.DNToZero rho := by
  rw [D.DNToZero_iff_DNLimit_eq_zero rho]
  exact D.DNLimit_eq_zero_of_arbitrarily_small rho hsmall

#print axioms MCore.RH.NB.NBHilbertData.DNLimit_le_stage
#print axioms MCore.RH.NB.NBHilbertData.DNLimit_eq_zero_of_arbitrarily_small
#print axioms MCore.RH.NB.NBHilbertData.DNToZero_of_arbitrarily_small

end NBHilbertData
end MCore.RH.NB
