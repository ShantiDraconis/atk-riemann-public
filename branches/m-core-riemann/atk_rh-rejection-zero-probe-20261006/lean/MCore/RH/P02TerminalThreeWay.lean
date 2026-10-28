import MCore.RH.P02TerminalWheel

namespace MCore

structure TerminalPair where
  num : Nat
  den : Nat
  deriving DecidableEq, Repr

def terminalNormalize (p : TerminalPair) : TerminalPair :=
  ⟨p.den, p.den⟩

def terminalClosed (p : TerminalPair) : Prop :=
  p.num = p.den

def terminalZero : TerminalPair := ⟨0, 0⟩
def terminalOne  : TerminalPair := ⟨0, 1⟩
def terminalTwo  : TerminalPair := ⟨0, 2⟩

theorem terminalNormalize_zero :
    terminalNormalize terminalZero = ⟨0, 0⟩ := rfl

theorem terminalNormalize_one :
    terminalNormalize terminalOne = ⟨1, 1⟩ := rfl

theorem terminalNormalize_two :
    terminalNormalize terminalTwo = ⟨2, 2⟩ := rfl

theorem terminalNormalize_closed (p : TerminalPair) :
    terminalClosed (terminalNormalize p) := by
  rfl

theorem terminalNormalize_idempotent (p : TerminalPair) :
    terminalNormalize (terminalNormalize p) = terminalNormalize p := by
  rfl

inductive TerminalWay
  | zero
  | one
  | two
  deriving DecidableEq, Repr

def terminalWayPair : TerminalWay → TerminalPair
  | .zero => terminalZero
  | .one  => terminalOne
  | .two  => terminalTwo

theorem all_three_ways_close (w : TerminalWay) :
    terminalClosed (terminalNormalize (terminalWayPair w)) := by
  cases w <;> rfl

theorem terminal_three_way_signature :
    terminalNormalize terminalZero = ⟨0,0⟩ ∧
    terminalNormalize terminalOne  = ⟨1,1⟩ ∧
    terminalNormalize terminalTwo  = ⟨2,2⟩ := by
  exact ⟨rfl, rfl, rfl⟩

theorem terminal_signature_does_not_change_endpoint_type :
    Endpoint = CriticalWheelTerminalClosure := rfl

theorem endpoint_gap_habitant_inhabitant_same_type :
    Endpoint = Gap ∧ Gap = Habitant ∧ Habitant = Inhabitant := by
  exact ⟨rfl, rfl, rfl⟩

end MCore
