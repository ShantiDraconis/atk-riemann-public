import MCore.RH.P02FinalRoot

namespace MCore

/-! FINAL_GLOBAL: no new mathematical assumptions beyond the terminal frontier. -/

def RHFinalGlobal : Prop := RHFinalRoot

theorem rh_final_global_of_terminal
    (h : RHTerminalOpenMath) :
    RHFinalGlobal :=
  rh_final_root_of_terminal h

end MCore
