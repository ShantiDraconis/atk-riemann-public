import MCore.RH.P02FinalGlobal

namespace MCore

/-! EXTERNAL endpoint: audit-facing wrapper, zero holes. -/

def RHExternalEndpoint : Prop := RHFinalGlobal

theorem rh_external_endpoint_of_terminal
    (h : RHTerminalOpenMath) :
    RHExternalEndpoint :=
  rh_final_global_of_terminal h

end MCore
