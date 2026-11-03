import MCore.RH.R0.HardFrontier
import MCore.RH.R0.ExplicitGramRate
import MCore.RH.NB.BCFExplicitLogBounds
import MCore.RH.NB.ExplicitCoefficientProducer
import MCore.RH.R0.TerminalLaw

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
Recovered route A:
the fully explicit inverse-Gram all-N rate closes the canonical RH material
producer and therefore the terminal certificate.
-/
theorem recovered_terminal_of_explicitGramRate
    (h : ExplicitGramRateTarget) :
    RiemannTerminalCertifies :=
  terminal_of_concreteUniformLogDNBound
    (explicitGramRateTarget_iff_uniformLogDNBound.mp h)

/--
Recovered route B:
the concrete BCF three-term logarithmic bounds close the same terminal root.
This route does not require passing through the explicit inverse-Gram theorem.
-/
theorem recovered_terminal_of_bcfExplicitLogBounds
    (B : concreteNBData.BCFThreeTermMajorant concreteGeneratorFamily)
    (H : concreteNBData.BCFExplicitLogBounds B) :
    RiemannTerminalCertifies := by
  exact concreteNBData.FINAL_ROOT_of_explicit_bcf_bounds H

/--
Recovered route C:
one explicit coefficient table with L2 error tending to zero closes DNLimit=0
directly and hence the terminal certificate.
-/
theorem recovered_terminal_of_coefficient_error_tendsto_zero
    (c : ℕ → ℕ → ℝ)
    (hzero :
      Filter.Tendsto
        (fun N =>
          ‖concreteNBData.chi -
            concreteNBData.finiteCoefficientApproximant
              concreteGeneratorFamily c N‖)
        Filter.atTop
        (nhds 0)) :
    RiemannTerminalCertifies := by
  exact concreteDNLimit_eq_zero_of_coefficient_error_tendsto_zero c hzero

/--
Exact all-N material target recovered from the discovery file.
No endpoint statement occurs in the definition.
-/
def RecoveredAllNRate : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ,
      explicitGramResidual N ≤
        K / Real.log ((N : ℝ) + 2)

theorem recoveredAllNRate_iff_explicitGramRateTarget :
    RecoveredAllNRate ↔ ExplicitGramRateTarget := by
  rfl

theorem recoveredAllNRate_to_terminal
    (h : RecoveredAllNRate) :
    RiemannTerminalCertifies := by
  apply recovered_terminal_of_explicitGramRate
  exact recoveredAllNRate_iff_explicitGramRateTarget.mp h

/--
The recovered proof graph has no hidden bridge after the all-N estimate:
the only non-transport mathematical content is an inhabitant of
RecoveredAllNRate, or an independently stronger BCF/coefficient witness.
-/
def recoveredMaterialFrontier : Prop := RecoveredAllNRate

theorem recoveredMaterialFrontier_to_terminal
    (h : recoveredMaterialFrontier) :
    RiemannTerminalCertifies :=
  recoveredAllNRate_to_terminal h

#print axioms MCore.RH.R0.recovered_terminal_of_explicitGramRate
#print axioms MCore.RH.R0.recovered_terminal_of_bcfExplicitLogBounds
#print axioms MCore.RH.R0.recovered_terminal_of_coefficient_error_tendsto_zero
#print axioms MCore.RH.R0.recoveredAllNRate_iff_explicitGramRateTarget
#print axioms MCore.RH.R0.recoveredAllNRate_to_terminal
#print axioms MCore.RH.R0.recoveredMaterialFrontier_to_terminal

end MCore.RH.R0
