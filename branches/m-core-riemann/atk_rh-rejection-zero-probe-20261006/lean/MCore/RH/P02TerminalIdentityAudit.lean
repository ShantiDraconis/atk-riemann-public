import MCore.RH.P02OpenClosedDuality

namespace MCore

/-!
# Terminal identity / transition audit

A proposition remains equal to itself. What can differ is the tagged stage at
which the same proposition is revisited in the terminal wheel.
-/

theorem openMath_self_identity :
    OpenMath = OpenMath := rfl

theorem closedMath_self_identity :
    ClosedMath = ClosedMath := rfl

theorem not_openMath_ne_itself :
    ¬ (OpenMath ≠ OpenMath) := by
  intro h
  exact h rfl

theorem not_closedMath_ne_itself :
    ¬ (ClosedMath ≠ ClosedMath) := by
  intro h
  exact h rfl

inductive TerminalStage
  | endpoint
  | gap
  | habitant
  | inhabitant
  deriving DecidableEq, Repr

def stageProp : TerminalStage → Prop
  | .endpoint   => Endpoint
  | .gap        => Gap
  | .habitant   => Habitant
  | .inhabitant => Inhabitant

theorem stageProp_all_same
    (s : TerminalStage) :
    stageProp s = Endpoint := by
  cases s <;> rfl

theorem distinct_stages_can_share_same_prop :
    TerminalStage.endpoint ≠ TerminalStage.gap ∧
    stageProp TerminalStage.endpoint = stageProp TerminalStage.gap := by
  exact ⟨by decide, rfl⟩

/--
This captures the intended "same mathematical content revisited at a different
point in the cycle": stages may differ while the proposition is identical.
-/
theorem terminal_revisit_without_self_inequality :
    ∀ s t : TerminalStage,
      stageProp s = stageProp t := by
  intro s t
  rw [stageProp_all_same s, stageProp_all_same t]

end MCore
