import MCore.RH.Analytic.MellinTailBlocks
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MCore.RH.R0

open MeasureTheory Set Complex Filter Topology

/-- The block series is the improper tail integral. -/
def ComplexTailIntegralSeriesBridge : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasSum (fun n : ℕ => complexTailTerm (n + 1) s)
      (∫ t : ℝ in Ioi 1,
        ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ))

/-- The explicit block formula telescopes to the zeta expression on Re(s)>1. -/
def ComplexTailSeriesClosedForm : Prop :=
  ∀ s : ℂ, 1 < s.re →
    (∑' n : ℕ, complexTailTerm (n + 1) s) =
      1 / (s - 1) - riemannZeta s / s

/-- Exact D1.1 target in the certified tree. -/
def TailFormulaRight : Prop :=
  ∀ s : ℂ, 1 < s.re →
    (∫ t : ℝ in Ioi 1,
      ((t : ℂ) ^ (-s - 1)) * (Int.fract t : ℂ)) =
      1 / (s - 1) - riemannZeta s / s

theorem tailFormulaRight_of_series
    (hbridge : ComplexTailIntegralSeriesBridge)
    (hclosed : ComplexTailSeriesClosedForm) :
    TailFormulaRight := by
  intro s hs
  rw [← (hbridge s hs).tsum_eq]
  exact hclosed s hs

#print axioms MCore.RH.R0.tailFormulaRight_of_series

end MCore.RH.R0
