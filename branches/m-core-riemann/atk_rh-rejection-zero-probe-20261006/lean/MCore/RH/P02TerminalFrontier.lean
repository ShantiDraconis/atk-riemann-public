import MCore.RH.P02DeterministicRejectionZero

namespace MCore

/-!
# RH terminal frontier

Forward-only rule:
- predecessors are frozen;
- no parameter reopening;
- no equivalent/hypothesis wrapper may be promoted as a proof;
- the only admissible mathematical change is a proof of `CriticalOrbitCollapse`.

This file contains no proof hole. It records the exact terminal obligation.
-/

def RHTerminalOpenMath : Prop := CriticalOrbitCollapse

theorem rh_terminal_frontier_exact :
    RHTerminalOpenMath ↔ CriticalOrbitCollapse := Iff.rfl

theorem rh_endpoint_of_terminal
    (h : RHTerminalOpenMath) :
    ProbeCriticalLineStatement :=
  criticalOrbitCollapse_implies_probeCriticalLine h

end MCore
