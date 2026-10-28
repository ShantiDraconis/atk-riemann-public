import MCore.RH.P02TerminalTransition
import MCore.RH.P02ExternalEndpoint

namespace MCore

/-!
# RPA dual-endpoint confirmation certificate

OPEN and CLOSED are distinct endpoint positions carrying logically equivalent
terminal content. The certified object is the state containing both witnesses
plus preservation of logical identity.
-/

inductive RPAEndpointPosition
  | open
  | closed
  deriving DecidableEq, Repr

theorem rpa_endpoint_positions_distinct :
    RPAEndpointPosition.open ≠ RPAEndpointPosition.closed := by
  decide

structure RPAEndpointView where
  position : RPAEndpointPosition
  proposition : Prop

def OPEN_ENDPOINT : RPAEndpointView :=
  { position := .open, proposition := Endpoint }

def CLOSED_ENDPOINT : RPAEndpointView :=
  { position := .closed, proposition := Endpoint }

theorem open_closed_positions_distinct :
    OPEN_ENDPOINT.position ≠ CLOSED_ENDPOINT.position := by
  exact rpa_endpoint_positions_distinct

theorem open_closed_identity_preserved :
    OPEN_ENDPOINT.proposition ↔ CLOSED_ENDPOINT.proposition := Iff.rfl

abbrev RPAOpenMath : Prop := OPEN_ENDPOINT.proposition
abbrev RPAClosedMath : Prop := CLOSED_ENDPOINT.proposition

abbrev RPAOpenBridge : Prop := RPAOpenMath
abbrev RPAClosedBridge : Prop := RPAClosedMath

def DUAL_ENDPOINT_STATE : Prop :=
  RPAOpenMath ∧
  RPAClosedMath ∧
  (RPAOpenMath ↔ RPAClosedMath)

abbrev RPAMath : Prop := DUAL_ENDPOINT_STATE
abbrev RPAFinalRoot : Prop := RPAMath
abbrev RPAGlobalExternalCertificate : Prop := RPAFinalRoot

structure RPADualTransitionCertificate where
  openWitness : RPAOpenMath
  closedWitness : RPAClosedMath
  identityPreserved : RPAOpenMath ↔ RPAClosedMath

theorem rpa_open_closed_same_identity :
    RPAOpenMath ↔ RPAClosedMath := Iff.rfl

theorem dual_endpoint_state_iff_both :
    DUAL_ENDPOINT_STATE ↔ (RPAOpenMath ∧ RPAClosedMath) := by
  constructor
  · rintro ⟨hOpen, hClosed, _⟩
    exact ⟨hOpen, hClosed⟩
  · rintro ⟨hOpen, hClosed⟩
    exact ⟨hOpen, hClosed, Iff.rfl⟩

theorem rpa_open_bridge_same :
    RPAOpenMath ↔ RPAOpenBridge := Iff.rfl

theorem rpa_closed_bridge_same :
    RPAClosedMath ↔ RPAClosedBridge := Iff.rfl

theorem rpa_bridges_form_dual_state :
    (RPAOpenBridge ∧ RPAClosedBridge) ↔ RPAMath := by
  constructor
  · rintro ⟨hOpen, hClosed⟩
    exact ⟨hOpen, hClosed, Iff.rfl⟩
  · rintro ⟨hOpen, hClosed, _⟩
    exact ⟨hOpen, hClosed⟩

theorem rpa_math_final_root_same :
    RPAMath ↔ RPAFinalRoot := Iff.rfl

theorem rpa_final_root_global_external_same :
    RPAFinalRoot ↔ RPAGlobalExternalCertificate := Iff.rfl

theorem rpa_certificate_iff_dual_endpoint_state :
    Nonempty RPADualTransitionCertificate ↔ DUAL_ENDPOINT_STATE := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.openWitness, c.closedWitness, c.identityPreserved⟩
  · rintro ⟨hOpen, hClosed, hId⟩
    exact ⟨{
      openWitness := hOpen
      closedWitness := hClosed
      identityPreserved := hId
    }⟩

theorem rpa_certificate_requires_open :
    Nonempty RPADualTransitionCertificate → RPAOpenMath := by
  rintro ⟨c⟩
  exact c.openWitness

theorem rpa_certificate_requires_closed :
    Nonempty RPADualTransitionCertificate → RPAClosedMath := by
  rintro ⟨c⟩
  exact c.closedWitness

theorem rpa_dual_chain_exact :
    DUAL_ENDPOINT_STATE ↔
      ((RPAOpenMath ∧ RPAClosedMath) ∧
       (RPAOpenBridge ∧ RPAClosedBridge) ∧
       RPAMath ∧
       RPAFinalRoot ∧
       RPAGlobalExternalCertificate) := by
  constructor
  · intro h
    rcases h with ⟨hOpen, hClosed, hId⟩
    have hMath : RPAMath := ⟨hOpen, hClosed, hId⟩
    exact ⟨⟨hOpen, hClosed⟩, ⟨hOpen, hClosed⟩, hMath, hMath, hMath⟩
  · rintro ⟨⟨hOpen, hClosed⟩, _, _, _, _⟩
    exact ⟨hOpen, hClosed, Iff.rfl⟩

end MCore
