import MCore.RH.P02TerminalIdentityAudit

namespace MCore

/-!
# Terminal open-to-closed transition

"OpenMath tends to ClosedMath" is represented as a transition relation between
terminal stages, not as a violation of self-identity.
-/

inductive TerminalStatus
  | open
  | closed
  deriving DecidableEq, Repr

def statusProp : TerminalStatus → Prop
  | .open   => OpenMath
  | .closed => ClosedMath

inductive TerminalTransition : TerminalStatus → TerminalStatus → Prop
  | close : TerminalTransition .open .closed

theorem open_tends_to_closed :
    TerminalTransition .open .closed :=
  TerminalTransition.close

theorem open_status_is_endpoint :
    statusProp .open = Endpoint := rfl

theorem closed_status_is_not_endpoint :
    statusProp .closed = (¬ Endpoint) := rfl

/--
The transition changes the status tag. It does not prove either proposition
inhabited and does not identify Endpoint with its negation.
-/
theorem transition_preserves_logical_distinction :
    TerminalStatus.open ≠ TerminalStatus.closed := by
  decide

/-- The four-stage wheel is still propositionally one endpoint type. -/
def wheelNext : TerminalStage → TerminalStage
  | .endpoint   => .gap
  | .gap        => .habitant
  | .habitant   => .inhabitant
  | .inhabitant => .endpoint

theorem wheelNext_preserves_endpoint_content (s : TerminalStage) :
    stageProp (wheelNext s) = stageProp s := by
  cases s <;> rfl

theorem wheel_four_returns (s : TerminalStage) :
    wheelNext (wheelNext (wheelNext (wheelNext s))) = s := by
  cases s <;> rfl

/--
This is the exact formal shape of "open tends to closed while the terminal
mathematical content cycles": status transition and endpoint-cycle are separate
structures.
-/
theorem terminal_transition_and_cycle :
    TerminalTransition .open .closed ∧
    (∀ s : TerminalStage, stageProp (wheelNext s) = stageProp s) := by
  exact ⟨open_tends_to_closed, wheelNext_preserves_endpoint_content⟩

end MCore
