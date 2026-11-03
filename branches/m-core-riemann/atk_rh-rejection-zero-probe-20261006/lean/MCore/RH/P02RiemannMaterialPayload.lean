import MCore.RH.P02MaterialRigidityLaw

namespace MCore

/-!
# RH material payload

Riemann uses its own material payload. No algebraicity payload from another
lane is reused here.

The payload is inhabited only by a proof that every probe nontrivial zero lies
on the critical line. The dual/lattice layer does not manufacture that proof.
The optional constructor from `RHMaterialRigidityCertificate` below makes the
remaining material law explicit and auditable.
-/

def RiemannHypothesisMaterial : Prop :=
  ProbeCriticalLineStatement

structure RiemannMaterialPayload where
  criticalLine : RiemannHypothesisMaterial

theorem criticalLine_implies_orbitCollapse
    (h : ProbeCriticalLineStatement) :
    CriticalOrbitCollapse := by
  intro s hs
  exact (criticalReflect_fixed_iff s).mpr (h s hs)

theorem orbitCollapse_iff_materialRH :
    CriticalOrbitCollapse ↔ RiemannHypothesisMaterial := by
  constructor
  · exact criticalOrbitCollapse_implies_probeCriticalLine
  · exact criticalLine_implies_orbitCollapse

theorem endpoint_iff_materialRH :
    Endpoint ↔ RiemannHypothesisMaterial := by
  change CriticalWheelTerminalClosure ↔ RiemannHypothesisMaterial
  exact criticalWheelTerminalClosure_iff_orbitCollapse.trans
    orbitCollapse_iff_materialRH

theorem payload_iff_materialRH :
    Nonempty RiemannMaterialPayload ↔ RiemannHypothesisMaterial := by
  constructor
  · rintro ⟨p⟩
    exact p.criticalLine
  · intro h
    exact ⟨{ criticalLine := h }⟩

theorem payload_iff_endpoint :
    Nonempty RiemannMaterialPayload ↔ Endpoint := by
  rw [payload_iff_materialRH, endpoint_iff_materialRH]

theorem payload_implies_dual_endpoint_state :
    RiemannMaterialPayload → DUAL_ENDPOINT_STATE := by
  intro p
  have hEndpoint : Endpoint :=
    endpoint_iff_materialRH.mpr p.criticalLine
  exact ⟨hEndpoint, hEndpoint, Iff.rfl⟩

theorem dual_endpoint_state_implies_payload :
    DUAL_ENDPOINT_STATE → RiemannMaterialPayload := by
  rintro ⟨hOpen, _, _⟩
  exact { criticalLine := endpoint_iff_materialRH.mp hOpen }

structure RiemannFinalCertificate where
  payload : RiemannMaterialPayload
  dual : DUAL_ENDPOINT_STATE

/-- Mechanical certificate constructor once the material critical-line proof
has actually been supplied. -/
def materialWitness
    (hRH : RiemannHypothesisMaterial) :
    RiemannFinalCertificate := by
  let p : RiemannMaterialPayload := { criticalLine := hRH }
  exact {
    payload := p
    dual := payload_implies_dual_endpoint_state p
  }

/-- Preferred non-circular entry point: a genuine material rigidity certificate
constructs the final payload and dual endpoint state. -/
def materialWitnessOfRigidity
    (cert : RHMaterialRigidityCertificate) :
    RiemannFinalCertificate :=
  materialWitness (probeCriticalLine_of_material_rigidity cert)

/-- Canonical object witnessing that the final RH certificate has been promoted
from the exact remaining material input, rather than manufactured by structure. -/
structure RHMaterialPromotion : Prop where
  input : RHMaterialPromotionInput
  finalCertificate : RiemannFinalCertificate

/-- Canonical promotion constructor.  Once the sole remaining material law is
provided, every downstream layer is filled mechanically. -/
def promotedByMaterial
    (input : RHMaterialPromotionInput) :
    RHMaterialPromotion := by
  let rigidity : RHMaterialRigidityCertificate :=
    materialRigidityCertificateOfPromotionInput input
  exact {
    input := input
    finalCertificate := materialWitnessOfRigidity rigidity
  }

/-- Promotion produces the material critical-line proposition. -/
theorem promotedByMaterial_implies_materialRH
    (p : RHMaterialPromotion) :
    RiemannHypothesisMaterial :=
  p.finalCertificate.payload.criticalLine

/-- Promotion produces the endpoint consumed by the structural lattice. -/
theorem promotedByMaterial_implies_endpoint
    (p : RHMaterialPromotion) :
    Endpoint :=
  endpoint_iff_materialRH.mpr
    (promotedByMaterial_implies_materialRH p)

/-- Exact promotion theorem: a promoted material certificate exists if and only if
the sole remaining RH-strength law has actually been proved. -/
theorem materialPromotion_iff_offLineReflectedPairExclusion :
    Nonempty RHMaterialPromotion ↔ OffLineReflectedPairExclusion := by
  constructor
  · rintro ⟨p⟩
    exact p.input.excludeOffLinePair
  · intro h
    exact ⟨promotedByMaterial { excludeOffLinePair := h }⟩

theorem finalCertificate_iff_materialRH :
    Nonempty RiemannFinalCertificate ↔ RiemannHypothesisMaterial := by
  constructor
  · rintro ⟨c⟩
    exact c.payload.criticalLine
  · intro h
    exact ⟨materialWitness h⟩

theorem finalCertificate_iff_endpoint :
    Nonempty RiemannFinalCertificate ↔ Endpoint := by
  rw [finalCertificate_iff_materialRH, endpoint_iff_materialRH]

/--
This is deliberately an equivalence, not a constructed certificate.
A concrete term of `RiemannFinalCertificate` still requires either a material
proof of `RiemannHypothesisMaterial` or a constructed
`RHMaterialRigidityCertificate`.
-/
theorem material_gate_exact :
    Nonempty RiemannFinalCertificate ↔
      (RiemannHypothesisMaterial ∧ DUAL_ENDPOINT_STATE) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.payload.criticalLine, c.dual⟩
  · rintro ⟨hRH, hDual⟩
    exact ⟨{
      payload := { criticalLine := hRH }
      dual := hDual
    }⟩

/-- A genuine rigidity certificate is sufficient for the final certificate. -/
theorem finalCertificate_of_material_rigidity
    (cert : RHMaterialRigidityCertificate) :
    Nonempty RiemannFinalCertificate :=
  ⟨materialWitnessOfRigidity cert⟩

end MCore
