import MCore.RH.P02RPAEndpointLattice
import MCore.RH.P02CriticalReflectionSymmetry

namespace MCore

/-!
# RH material rigidity frontier

This module separates the kernel-checked structural lattice from the one
remaining RH-strength mathematical obligation.

Nothing here assumes `ProbeCriticalLineStatement`, `CriticalOrbitCollapse`,
or `RiemannHypothesis` as a field.  No inhabitant of the certificate below is
constructed in this file.
-/

/-- Closure of the probe nontrivial-zero predicate under reflection across
Re(s)=1/2.  This is a genuine analytic/symmetry obligation. -/
def CriticalReflectionZeroClosure : Prop :=
  ∀ s : ℂ,
    ProbeNontrivialZetaZero s →
    ProbeNontrivialZetaZero (criticalReflect s)


/-- Conjugation symmetry already suffices to construct the full reflected
nontrivial-zero closure.  The remaining side conditions are elementary:
the reflected point cannot be 1, and if it were a negative even integer then
the original zero would lie in Re(s) > 1. -/
theorem criticalReflectionZeroClosure_of_conjugation
    (hconj : RiemannZetaConjugationZeroSymmetry) :
    CriticalReflectionZeroClosure := by
  intro s hs
  refine ⟨criticalReflect_zero_value_closed hconj
      probeFunctionalSideConditions_proved hs, ?_, ?_⟩
  · intro htriv
    rcases htriv with ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have hsre : s.re = 1 + (2 * (n + 1) : ℕ) := by
      simp [criticalReflect] at hre
      norm_num at hre ⊢
      linarith
    have hpos : (0 : ℝ) < (((2 * (n + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show 0 < 2 * (n + 1) by omega)
    have hgt : (1 : ℝ) < s.re := by
      rw [hsre]
      linarith
    exact (riemannZeta_ne_zero_of_one_lt_re hgt) hs.1
  · intro h1
    have hback := congrArg criticalReflect h1
    rw [criticalReflect_involutive] at hback
    have hs0 : s = 0 := by
      simpa [criticalReflect] using hback
    have hz0 : riemannZeta (0 : ℂ) = 0 := by
      simpa [hs0] using hs.1
    rw [riemannZeta_zero] at hz0
    norm_num at hz0

/-- The reflected nontrivial-zero closure is now a proved analytic consequence of
the completed-zeta conjugation theorem.  It is no longer part of the RH-strength mincut. -/
theorem criticalReflectionZeroClosure_proved :
    CriticalReflectionZeroClosure :=
  criticalReflectionZeroClosure_of_conjugation
    riemannZetaConjugationZeroSymmetry_proved

/-- Material rigidity law: an off-critical-line zero and its reflected partner
cannot both satisfy the probe nontrivial-zero predicate.

This proposition is intentionally exposed as the remaining material law.  It
is not manufactured by the RPA endpoint lattice and is not proved here. -/
def OffLineReflectedPairExclusion : Prop :=
  ∀ s : ℂ,
    ProbeNontrivialZetaZero s →
    ProbeNontrivialZetaZero (criticalReflect s) →
    s.re ≠ (1 / 2 : ℝ) →
    False

/-- The exact non-circular interface required to turn the structural chain into
a critical-line proof.  Constructing a value of this structure is the remaining
scientific task. -/
structure RHMaterialRigidityCertificate : Prop where
  zeroClosure : CriticalReflectionZeroClosure
  excludeOffLinePair : OffLineReflectedPairExclusion

/-- Exact remaining material input after all analytic symmetry infrastructure has
been discharged.  This structure has exactly one RH-strength field. -/
structure RHMaterialPromotionInput : Prop where
  excludeOffLinePair : OffLineReflectedPairExclusion

/-- Mechanical promotion of the exact remaining material input into the rigidity
certificate.  No RH conclusion is stored in the input besides the explicit
off-line-pair exclusion law itself. -/
def materialRigidityCertificateOfPromotionInput
    (input : RHMaterialPromotionInput) :
    RHMaterialRigidityCertificate where
  zeroClosure := criticalReflectionZeroClosure_proved
  excludeOffLinePair := input.excludeOffLinePair

/-- The exact promotion input is equivalent to the remaining material law. -/
theorem promotionInput_iff_offLineReflectedPairExclusion :
    Nonempty RHMaterialPromotionInput ↔ OffLineReflectedPairExclusion := by
  constructor
  · rintro ⟨input⟩
    exact input.excludeOffLinePair
  · intro h
    exact ⟨{ excludeOffLinePair := h }⟩

/-- Once zero closure and off-line-pair exclusion are both supplied, every
probe zero is fixed by critical reflection. -/
theorem criticalOrbitCollapse_of_material_rigidity
    (cert : RHMaterialRigidityCertificate) :
    CriticalOrbitCollapse := by
  intro s hs
  have hre : s.re = (1 / 2 : ℝ) := by
    by_contra hoff
    exact cert.excludeOffLinePair s hs (cert.zeroClosure s hs) hoff
  exact (criticalReflect_fixed_iff s).mpr hre

/-- Composition to the exact terminal material proposition used by the payload. -/
theorem probeCriticalLine_of_material_rigidity
    (cert : RHMaterialRigidityCertificate) :
    ProbeCriticalLineStatement :=
  criticalOrbitCollapse_implies_probeCriticalLine
    (criticalOrbitCollapse_of_material_rigidity cert)

/-- The material law is sufficient for the endpoint proposition. -/
theorem endpoint_of_material_rigidity
    (cert : RHMaterialRigidityCertificate) :
    Endpoint := by
  exact (criticalWheelTerminalClosure_iff_orbitCollapse).mpr
    (criticalOrbitCollapse_of_material_rigidity cert)

/-- Audit guard: the structural RPA lattice only transports Endpoint content;
it does not construct the material rigidity certificate. -/
theorem rpa_full_of_material_rigidity
    (cert : RHMaterialRigidityCertificate) :
    RPAFull := by
  have hEndpoint : Endpoint := endpoint_of_material_rigidity cert
  exact ⟨hEndpoint, hEndpoint, Iff.rfl⟩

end MCore
