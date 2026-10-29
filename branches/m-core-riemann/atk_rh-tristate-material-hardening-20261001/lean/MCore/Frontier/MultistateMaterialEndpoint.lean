import MCore.Frontier.MultistateSN
import MCore.RH.R0.GramTerminalLink

namespace MCore.RiemannMultistate

open MCore.RH.NB
open MCore.RH.R0

/--
Hardened terminal state for the RH multistate architecture.

Unlike the older generic WeightedModularBilinearDecay wrapper, this proposition
is fixed externally: it is exactly convergence of the canonical concrete
Báez-Duarte defect sequence to zero.  The certificate cannot choose an
arbitrary proposition such as True.
-/
def ConcreteState2 : Prop :=
  concreteNBData.DNToZero concreteGeneratorFamily

/-- A genuine terminal certificate for state 2 carries the literal concrete
zero-defect proposition and nothing weaker. -/
structure ConcreteWeightedDecayEndCertificate where
  decay : ConcreteState2

/-- The hardened state-2 certificate is inhabited exactly when the concrete
DN sequence tends to zero. -/
theorem concrete_end_certificate_iff_state2 :
    Nonempty ConcreteWeightedDecayEndCertificate ↔ ConcreteState2 := by
  constructor
  · rintro ⟨h⟩
    exact h.decay
  · intro h
    exact ⟨{ decay := h }⟩

/-- The hardened tri-state terminal is exactly the existing finite-span
density endpoint.  Thus the multistate presentation introduces no extra
mathematical gap and cannot bypass the canonical RH frontier. -/
theorem concrete_state2_iff_finiteSpanApproximatesChi :
    ConcreteState2 ↔
      concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily := by
  exact
    (concreteNBData.finiteSpanApproximatesChi_iff_DNToZero
      concreteGeneratorFamily).symm

/-- The same hardened terminal is exactly the concrete zero-limit endpoint. -/
theorem concrete_state2_iff_DNLimit_eq_zero :
    ConcreteState2 ↔
      concreteNBData.DNLimit concreteGeneratorFamily = 0 := by
  exact concreteNBData.DNToZero_iff_DNLimit_eq_zero concreteGeneratorFamily

/-- Consequently the tri-state terminal and the concrete Gram endpoint are
the same material obligation, via the already-certified Gram terminal link. -/
theorem concrete_end_certificate_iff_finiteSpan :
    Nonempty ConcreteWeightedDecayEndCertificate ↔
      concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily := by
  rw [concrete_end_certificate_iff_state2,
      concrete_state2_iff_finiteSpanApproximatesChi]

#print axioms MCore.RiemannMultistate.concrete_end_certificate_iff_state2
#print axioms MCore.RiemannMultistate.concrete_state2_iff_finiteSpanApproximatesChi
#print axioms MCore.RiemannMultistate.concrete_state2_iff_DNLimit_eq_zero
#print axioms MCore.RiemannMultistate.concrete_end_certificate_iff_finiteSpan

end MCore.RiemannMultistate
