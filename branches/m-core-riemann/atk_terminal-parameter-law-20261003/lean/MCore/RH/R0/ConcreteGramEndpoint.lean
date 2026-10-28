import MCore.RH.R0.ChiNorm
import MCore.RH.R0.RhoConcrete
import MCore.RH.NB.GramEndpoint

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB

/--
Concrete terminal Gram formulation.

The canonical concrete zero-defect endpoint is equivalent to solving the
finite Gram normal equations at arbitrarily small reduced scalar defect
`1 - c^T b`. This introduces no new hypothesis.
-/
theorem concrete_DNLimit_eq_zero_iff_gram_scalar
    :
    concreteNBData.DNLimit concreteGeneratorFamily = 0 ↔
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
  simpa [concreteNBData_chi_norm] using
    (concreteNBData.DNLimit_eq_zero_iff_normal_equation_energy
      concreteGeneratorFamily)

#print axioms concrete_DNLimit_eq_zero_iff_gram_scalar

end MCore.RH.R0
