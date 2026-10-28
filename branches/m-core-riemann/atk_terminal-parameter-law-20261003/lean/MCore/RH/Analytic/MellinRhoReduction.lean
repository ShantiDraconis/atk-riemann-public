import MCore.RH.Analytic.MellinConcrete
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- Complexified raw fractional-part function. -/
noncomputable def fractRepresentativeC (t : ℝ) : ℂ :=
  ((Int.fract t : ℝ) : ℂ)

/-- rho_0 is exactly the inversion pullback of the raw fractional-part function. -/
theorem rhoRepresentativeC_zero_eq_fract_inv :
    rhoRepresentativeC 0 = fun x : ℝ => fractRepresentativeC x⁻¹ := by
  funext x
  simp [rhoRepresentativeC, rhoRepresentative, rhoBase, rhoIndex, fractRepresentativeC, one_div]

/-- D1.0: inversion reduces Mellin(rho_0) to Mellin(fract) at the reflected exponent. -/
theorem mellin_rhoBase_reduction (s : ℂ) :
    mellin (rhoRepresentativeC 0) s =
      mellin fractRepresentativeC (-s) := by
  rw [rhoRepresentativeC_zero_eq_fract_inv]
  exact mellin_comp_inv fractRepresentativeC s

/--
The remaining analytic identity after all change-of-variable structure has been removed.
This is the exact D1 producer needed on the critical strip.
-/
def FractionalZetaMellinIdentity : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    mellin fractRepresentativeC (-s) = - riemannZeta s / s

/-- D1 follows immediately from the single fractional-zeta Mellin identity. -/
theorem mellin_rho_base_of_fractionalZeta
    (h : FractionalZetaMellinIdentity)
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (rhoRepresentativeC 0) s = - riemannZeta s / s := by
  rw [mellin_rhoBase_reduction]
  exact h s hs0 hs1

#print axioms MCore.RH.R0.mellin_rhoBase_reduction
#print axioms MCore.RH.R0.mellin_rho_base_of_fractionalZeta

end MCore.RH.R0
