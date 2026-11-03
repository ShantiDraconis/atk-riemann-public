import MCore.RH.R0.RhoConcrete
import Mathlib.Analysis.MellinInversion

namespace MCore.RH.R0

open MeasureTheory Set
open Complex

/-- Complex-valued representative of the frozen real target. -/
noncomputable def chiRepresentativeC (x : ℝ) : ℂ :=
  (chiRepresentative x : ℂ)

/-- Complex-valued representative of the frozen Báez--Duarte generator. -/
noncomputable def rhoRepresentativeC (n : ℕ) (x : ℝ) : ℂ :=
  (rhoRepresentative n x : ℂ)

/-- The concrete generators are literal dilates of the base generator. -/
theorem rhoRepresentativeC_eq_dilate (n : ℕ) :
    rhoRepresentativeC n =
      fun x => rhoRepresentativeC 0 (((rhoIndex n : ℕ) : ℝ) * x) := by
  funext x
  simp [rhoRepresentativeC, rhoRepresentative, rhoBase, rhoIndex]

/--
Mellin scaling law for the concrete generator family.
This uses only Mathlib's Mellin dilation theorem and the frozen definition
rho_n(x) = fract(1 / ((n+1)x)).
-/
theorem mellin_rhoRepresentativeC_dilate (n : ℕ) (s : ℂ) :
    mellin (rhoRepresentativeC n) s =
      (((rhoIndex n : ℕ) : ℂ) ^ (-s)) *
        mellin (rhoRepresentativeC 0) s := by
  rw [rhoRepresentativeC_eq_dilate n]
  have ha : 0 < (((rhoIndex n : ℕ) : ℝ)) := by
    exact_mod_cast rhoIndex_pos n
  simpa [smul_eq_mul] using
    (mellin_comp_mul_left (rhoRepresentativeC 0) s ha)

#print axioms MCore.RH.R0.rhoRepresentativeC_eq_dilate
#print axioms MCore.RH.R0.mellin_rhoRepresentativeC_dilate

end MCore.RH.R0
