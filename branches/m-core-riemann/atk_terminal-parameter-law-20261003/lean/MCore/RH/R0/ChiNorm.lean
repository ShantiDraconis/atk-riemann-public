import MCore.RH.R0.RhoConcrete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
Exact norm of the concrete Nyman--Beurling target.

The target is the indicator of (0,1) in L²((0,∞), dx), hence has norm one.
No new assumption or axiom is introduced.
-/

namespace MCore.RH.R0

open MeasureTheory Set

theorem chiLpConcrete_eq_indicatorConstLp :
    chiLpConcrete =
      indicatorConstLp twoExponent measurableSet_Ioo chiSupport_measure_ne_top (1 : ℝ) := by
  unfold chiLpConcrete chiLp indicatorConstLp
  apply MemLp.toLp_congr chi_memLp_two
    (memLp_indicator_const twoExponent measurableSet_Ioo (1 : ℝ)
      (Or.inr chiSupport_measure_ne_top))
  rw [chiRepresentative_eq_indicator]
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- The concrete target has exact L² norm one. -/
theorem concreteNBData_chi_norm :
    ‖concreteNBData.chi‖ = 1 := by
  change ‖chiLpConcrete‖ = 1
  rw [chiLpConcrete_eq_indicatorConstLp]
  rw [norm_indicatorConstLp]
  · have hset : (Ioo (0 : ℝ) 1) ∩ Ioi 0 = Ioo 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, h.1⟩
    rw [show zeroInfinityMeasure = volume.restrict (Ioi (0 : ℝ)) by rfl]
    rw [measureReal_restrict_apply measurableSet_Ioo]
    rw [hset]
    rw [Real.volume_real_Ioo]
    norm_num [twoExponent]
  · norm_num [twoExponent]
  · norm_num [twoExponent]

#print axioms MCore.RH.R0.chiLpConcrete_eq_indicatorConstLp
#print axioms MCore.RH.R0.concreteNBData_chi_norm

end MCore.RH.R0
