import MCore.RH.P02FinalRoot

namespace MCore

/-!
# RH Global / External certificate surface

Forward-only, placeholder-free. No predecessor is reopened here.
The external endpoint depends exactly on the unique terminal proposition.
-/

def RHGlobalEndpoint : Prop := RHFinalRoot

def RHExternalEndpoint : Prop := RHGlobalEndpoint

theorem rh_global_of_terminal
    (h : RHTerminalOpenMath) :
    RHGlobalEndpoint :=
  rh_final_root_of_terminal h

theorem rh_external_of_terminal
    (h : RHTerminalOpenMath) :
    RHExternalEndpoint :=
  rh_global_of_terminal h

theorem rh_external_exact_dependency :
    RHTerminalOpenMath → RHExternalEndpoint :=
  rh_external_of_terminal

end MCore
