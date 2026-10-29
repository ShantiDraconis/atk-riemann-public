import MCore.RH.R0.ConcreteGramEndpoint
import MCore.RH.NB.ZeroLimitFrontier

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB

/-- Terminal RH producer compressed to the concrete finite Gram scalar.
No new premise is introduced: this is the composition of the frozen
finite-span/zero-limit equivalence with the concrete Gram endpoint. -/
theorem concrete_finiteSpanApproximatesChi_iff_gram_scalar :
    concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ c : Fin N → ℝ,
          (∀ j : Fin N,
            (∑ i : Fin N,
              c i *
                concreteNBData.gramEntry concreteGeneratorFamily i j) =
              concreteNBData.targetEntry concreteGeneratorFamily j) ∧
          1 -
              (∑ i : Fin N,
                c i *
                  concreteNBData.targetEntry concreteGeneratorFamily i) <
            ε ^ 2 := by
  exact
    (concreteNBData.finiteSpanApproximatesChi_iff_DNLimit_eq_zero
      concreteGeneratorFamily).trans
      concrete_DNLimit_eq_zero_iff_gram_scalar

#print axioms MCore.RH.R0.concrete_finiteSpanApproximatesChi_iff_gram_scalar

end MCore.RH.R0
