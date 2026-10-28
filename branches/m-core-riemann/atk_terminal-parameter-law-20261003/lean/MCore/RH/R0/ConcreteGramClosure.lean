import MCore.RH.R0.ConcreteFinalProducer
import MCore.RH.R0.GramTerminalLink

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
Exact closure theorem for the concrete Gram frontier.

This theorem does not add a new mathematical hypothesis.  It records that the
single concrete Gram residual is exactly equivalent to the certified zero-limit
root.
-/
theorem concreteGramResidual_iff_DNLimit_eq_zero :
    ConcreteGramResidual ↔
      concreteNBData.DNLimit concreteGeneratorFamily = 0 := by
  unfold ConcreteGramResidual
  exact concrete_DNLimit_eq_zero_iff_gram_scalar.symm

/-- The concrete Gram residual is exactly the kernel-level final root. -/
theorem concreteGramResidual_iff_FINAL_ROOT :
    ConcreteGramResidual ↔
      FINAL_ROOT concreteNBData concreteGeneratorFamily := by
  simpa [FINAL_ROOT] using concreteGramResidual_iff_DNLimit_eq_zero

/--
The same residual is exactly the already-certified finite-span density target.
Thus there is no additional bridge between the Gram scalar frontier and the
canonical Nyman--Beurling terminal proposition.
-/
theorem concreteGramResidual_iff_finiteSpanApproximatesChi :
    ConcreteGramResidual ↔
      concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily := by
  unfold ConcreteGramResidual
  exact concrete_finiteSpanApproximatesChi_iff_gram_scalar.symm

/-- Backward extraction: any final-root proof yields the concrete Gram residual. -/
theorem FINAL_ROOT_to_concreteGramResidual
    (h : FINAL_ROOT concreteNBData concreteGeneratorFamily) :
    ConcreteGramResidual :=
  concreteGramResidual_iff_FINAL_ROOT.mpr h

/-- Backward extraction from the canonical finite-span target. -/
theorem finiteSpanApproximatesChi_to_concreteGramResidual
    (h : concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily) :
    ConcreteGramResidual :=
  concreteGramResidual_iff_finiteSpanApproximatesChi.mpr h

/-- Forward closure, restated locally for the exact Gram frontier. -/
theorem concreteGramResidual_closes_FINAL_ROOT
    (h : ConcreteGramResidual) :
    FINAL_ROOT concreteNBData concreteGeneratorFamily :=
  concreteGramResidual_iff_FINAL_ROOT.mp h

#print axioms MCore.RH.R0.concreteGramResidual_iff_DNLimit_eq_zero
#print axioms MCore.RH.R0.concreteGramResidual_iff_FINAL_ROOT
#print axioms MCore.RH.R0.concreteGramResidual_iff_finiteSpanApproximatesChi
#print axioms MCore.RH.R0.FINAL_ROOT_to_concreteGramResidual
#print axioms MCore.RH.R0.finiteSpanApproximatesChi_to_concreteGramResidual
#print axioms MCore.RH.R0.concreteGramResidual_closes_FINAL_ROOT

end MCore.RH.R0
