import MCore.RH.P02LastOpenMath
import MCore.RH.P02ExternalEndpoint

namespace MCore

/-!
# RH closed-frontier certificate

This certificate closes the search/bridge mechanics with zero proof holes.
It does not assert `CriticalOrbitCollapse`.
-/

structure RHClosedFrontierCertificate where
  searchTraversalClosed : RHSearchTraversalClosed
  terminalDisposition : rhTerminalDisposition = .unprovenTerminal
  terminalExact : RHTerminalStatement ↔ CriticalOrbitCollapse
  externalConditional :
    RHTerminalStatement → RHExternalEndpoint

def rhClosedFrontierCertificate : RHClosedFrontierCertificate where
  searchTraversalClosed := rh_search_traversal_closed
  terminalDisposition := rh_terminal_disposition_exact
  terminalExact := rh_terminal_statement_exact
  externalConditional := lastBit_endpoint_of_terminal

theorem rh_closed_frontier_zero_reopen :
    RHSearchTraversalClosed :=
  rhClosedFrontierCertificate.searchTraversalClosed

end MCore
