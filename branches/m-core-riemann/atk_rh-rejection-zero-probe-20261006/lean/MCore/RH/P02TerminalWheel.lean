import MCore.RH.P02TerminalFreeze

namespace MCore

/-!
# RH terminal wheel / truncation theorem

No new parameter family is introduced. The only dynamical map is the already
frozen terminal reflection `criticalReflect`.
-/

def criticalWheel : ℕ → ℂ → ℂ
  | 0, s => s
  | n + 1, s => criticalWheel n (criticalReflect s)

theorem criticalWheel_zero (s : ℂ) :
    criticalWheel 0 s = s := by
  rfl

theorem criticalWheel_one (s : ℂ) :
    criticalWheel 1 s = criticalReflect s := by
  rfl

theorem criticalWheel_two (s : ℂ) :
    criticalWheel 2 s = s := by
  simpa [criticalWheel] using criticalReflect_involutive s

theorem criticalWheel_add_two (n : ℕ) (s : ℂ) :
    criticalWheel (n + 2) s = criticalWheel n s := by
  have h :
      criticalWheel n (criticalReflect (criticalReflect s)) =
        criticalWheel n s :=
    congrArg (criticalWheel n) (criticalReflect_involutive s)
  simpa [criticalWheel, Nat.add_assoc] using h

/-- Minimal truncation: the first reflected state is already the initial state. -/
def CriticalWheelTruncatesAtLastBit (s : ℂ) : Prop :=
  criticalWheel 1 s = criticalWheel 0 s

theorem criticalWheel_truncates_iff_fixed (s : ℂ) :
    CriticalWheelTruncatesAtLastBit s ↔ criticalReflect s = s := by
  rfl

theorem criticalWheel_truncates_iff_critical_line (s : ℂ) :
    CriticalWheelTruncatesAtLastBit s ↔ s.re = (1 / 2 : ℝ) := by
  simpa [CriticalWheelTruncatesAtLastBit, criticalWheel]
    using criticalReflect_fixed_iff s

def CriticalWheelTerminalClosure : Prop :=
  ∀ s : ℂ, ProbeNontrivialZetaZero s → CriticalWheelTruncatesAtLastBit s

theorem criticalWheelTerminalClosure_iff_orbitCollapse :
    CriticalWheelTerminalClosure ↔ CriticalOrbitCollapse := by
  constructor
  · intro h s hs
    exact (criticalWheel_truncates_iff_fixed s).mp (h s hs)
  · intro h s hs
    exact (criticalWheel_truncates_iff_fixed s).mpr (h s hs)

theorem criticalWheelTerminalClosure_implies_endpoint
    (h : CriticalWheelTerminalClosure) :
    ProbeCriticalLineStatement :=
  criticalOrbitCollapse_implies_probeCriticalLine
    ((criticalWheelTerminalClosure_iff_orbitCollapse).mp h)

/-! Terminal signature cycle: four names, one logical proposition. -/

abbrev Endpoint : Prop := CriticalWheelTerminalClosure
abbrev Gap : Prop := Endpoint
abbrev Habitant : Prop := Gap
abbrev Inhabitant : Prop := Habitant

theorem endpoint_to_gap : Endpoint → Gap := id
theorem gap_to_habitant : Gap → Habitant := id
theorem habitant_to_inhabitant : Habitant → Inhabitant := id
theorem inhabitant_to_endpoint : Inhabitant → Endpoint := id

theorem terminal_cycle_endpoint_gap : Endpoint ↔ Gap := Iff.rfl
theorem terminal_cycle_gap_habitant : Gap ↔ Habitant := Iff.rfl
theorem terminal_cycle_habitant_inhabitant : Habitant ↔ Inhabitant := Iff.rfl
theorem terminal_cycle_inhabitant_endpoint : Inhabitant ↔ Endpoint := Iff.rfl

theorem terminal_cycle_all :
    (Endpoint ↔ Gap) ∧
    (Gap ↔ Habitant) ∧
    (Habitant ↔ Inhabitant) ∧
    (Inhabitant ↔ Endpoint) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/--
A cycle of equivalent names does not by itself create an inhabitant.
The kernel checks this with the countermodel P = False.
-/
theorem terminal_cycle_names_do_not_force_inhabitation :
    ∃ P : Prop,
      let E := P
      let G := E
      let H := G
      let I := H
      (E ↔ G) ∧ (G ↔ H) ∧ (H ↔ I) ∧ (I ↔ E) ∧ ¬ E := by
  refine ⟨False, ?_⟩
  simp

end MCore
