import MCore.RH.Analytic.MellinConcrete
import Mathlib.Analysis.MellinTransform

namespace MCore.RH.R0

open MeasureTheory Set Complex

/-- D2: exact Mellin transform of the frozen target chi = 1_(0,1). -/
theorem mellin_chiRepresentativeC
    (s : ℂ) (hs0 : 0 < s.re) :
    mellin chiRepresentativeC s = 1 / s := by
  have hstd := (hasMellin_one_Ioc (s := s) hs0).2
  rw [← hstd]
  unfold mellin
  apply integral_congr_ae
  have hne_one : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), x ≠ 1 := by
    rw [ae_iff]
    simp [Real.volume_singleton]
  filter_upwards [
    self_mem_ae_restrict measurableSet_Ioi,
    hne_one] with x hx h1
  have hx0 : 0 < x := hx
  have hmemIoc : x ∈ Ioc (0 : ℝ) 1 ↔ x < 1 := by
    constructor
    · intro h
      exact lt_of_le_of_ne h.2 h1
    · intro h
      exact ⟨hx0, h.le⟩
  have hmemIoo : x ∈ Ioo (0 : ℝ) 1 ↔ x < 1 := by
    simp [hx0]
  by_cases hxlt : x < 1
  · simp [chiRepresentativeC, chiRepresentative, hx0, hxlt, hmemIoc.mpr hxlt]
  · have hxge : 1 ≤ x := le_of_not_gt hxlt
    have hxgt : 1 < x := lt_of_le_of_ne hxge (Ne.symm h1)
    simp [chiRepresentativeC, chiRepresentative, hx0, hxlt, hmemIoc, hxgt.not_le]

#print axioms MCore.RH.R0.mellin_chiRepresentativeC

end MCore.RH.R0
