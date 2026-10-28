import MCore.RH.P02TerminalThreeWay

namespace MCore

/-!
# Open/closed terminal duality audit

Here "-" is formalized as logical negation. This file does not add an RH
assumption; it checks the exact logical consequences of identifying open and
closed states.
-/

abbrev OpenMath : Prop := Endpoint
abbrev ClosedMath : Prop := ¬ OpenMath

theorem openMath_eq_not_closedMath :
    OpenMath ↔ ¬ ClosedMath := by
  constructor
  · intro hOpen hClosed
    exact hClosed hOpen
  · intro hNotClosed
    by_contra hOpen
    exact hNotClosed hOpen

theorem closedMath_eq_not_openMath :
    ClosedMath ↔ ¬ OpenMath := Iff.rfl

/--
A simultaneous identification OpenMath ↔ ClosedMath is inconsistent with
ClosedMath := ¬ OpenMath. Thus "open = closed = -open" cannot itself be an
inhabitant-producing proof principle in consistent logic.
-/
theorem open_eq_closed_is_impossible :
    ¬ (OpenMath ↔ ClosedMath) := by
  intro h
  have hNotOpen : ¬ OpenMath := by
    intro hOpen
    exact (h.mp hOpen) hOpen
  have hOpen : OpenMath := h.mpr hNotOpen
  exact hNotOpen hOpen

theorem open_closed_negative_cycle_is_false :
    ¬ ((OpenMath ↔ ClosedMath) ∧ (ClosedMath ↔ ¬ OpenMath)) := by
  intro h
  exact open_eq_closed_is_impossible h.1

/--
The consistent duality is the complement relation:
OpenMath ↔ ¬ ClosedMath and ClosedMath ↔ ¬ OpenMath.
It does not select which side is inhabited.
-/
theorem open_closed_complement_cycle :
    (OpenMath ↔ ¬ ClosedMath) ∧ (ClosedMath ↔ ¬ OpenMath) := by
  exact ⟨openMath_eq_not_closedMath, closedMath_eq_not_openMath⟩

end MCore
