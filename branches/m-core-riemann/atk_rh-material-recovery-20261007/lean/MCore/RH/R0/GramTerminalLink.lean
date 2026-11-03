import MCore.RH.R0.ConcreteGramEndpoint

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB

/--
Compatibility terminal link between the canonical finite-span target and the
concrete Gram scalar formulation.  This is composition of two existing exact
equivalences; no new mathematical hypothesis is introduced.
-/
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
