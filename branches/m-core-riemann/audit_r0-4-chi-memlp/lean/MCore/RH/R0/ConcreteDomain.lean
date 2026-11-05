import MCore.RH.R0.AmbientCarrier
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace MCore.RH.R0

/-- Concrete base domain for the selected R0 normalization. -/
abbrev BaseDomain := ℝ

/-- The open positive half-line (0,∞), represented as a measurable subset of ℝ. -/
def zeroInfinityDomain : Set BaseDomain := Set.Ioi 0

/-- The target support (0,1) inside the ambient real line. -/
def chiSupport : Set BaseDomain := Set.Ioo 0 1

/-- The concrete indicator representative before passage to an L2 equivalence class.
Real order is noncomputable in Lean's executable kernel, so this mathematical
representative is explicitly marked noncomputable. -/
noncomputable def chiRepresentative (x : BaseDomain) : ℝ :=
  if 0 < x ∧ x < 1 then 1 else 0

@[simp] theorem chiRepresentative_of_mem {x : BaseDomain} (hx : x ∈ chiSupport) :
    chiRepresentative x = 1 := by
  exact if_pos hx

@[simp] theorem chiRepresentative_of_not_mem {x : BaseDomain} (hx : x ∉ chiSupport) :
    chiRepresentative x = 0 := by
  exact if_neg hx

/-- R0.2 records the Lebesgue measure used by the selected concrete model. -/
noncomputable def ambientMeasure : MeasureTheory.Measure BaseDomain :=
  MeasureTheory.volume

end MCore.RH.R0
