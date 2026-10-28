import MCore.RH.P02TerminalFrontier

namespace MCore

/-! FINAL_ROOT: zero-hole wrapper over the unique terminal frontier. -/

def RHFinalRoot : Prop := ProbeCriticalLineStatement

theorem rh_final_root_of_terminal
    (h : RHTerminalOpenMath) :
    RHFinalRoot :=
  rh_endpoint_of_terminal h

end MCore
