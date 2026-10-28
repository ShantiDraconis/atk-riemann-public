import MCore.RH.R0.HardFrontier
import MCore.RH.NB.CoefficientRealization

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
Explicit coefficient-family form of the unique RH material producer.
This is not a new hypothesis used to close the lane: it is an exact
finite-dimensional realization of the same quantitative obligation.
-/
structure ConcreteCoefficientLogRate where
  K : ℝ
  hK : 0 ≤ K
  coeff : (N : ℕ) → Fin N → ℝ
  error_sq_le :
    ∀ N : ℕ,
      ‖concreteNBData.chi -
        concreteNBData.coefficientApproximantAt
          concreteGeneratorFamily N (coeff N)‖ ^ 2 ≤
        logMajorant K N

/-- Any explicit coefficient family with the logarithmic L² error rate
produces the canonical uniform DN bound by optimality of projection. -/
theorem ConcreteCoefficientLogRate.toUniformLogDNBound
    (h : ConcreteCoefficientLogRate) :
    ConcreteUniformLogDNBound := by
  refine ⟨h.K, h.hK, ?_⟩
  intro N
  exact le_trans
    (concreteNBData.DN_le_coefficient_error_sq
      concreteGeneratorFamily N (h.coeff N))
    (h.error_sq_le N)

/-- Conversely, the canonical DN bound has an optimal finite coefficient
realization at every N, so the coefficient formulation loses no content. -/
noncomputable def uniformLogDNBound_to_ConcreteCoefficientLogRate
    (h : ConcreteUniformLogDNBound) :
    ConcreteCoefficientLogRate :=
  let K : ℝ := Classical.choose h
  let hspec := Classical.choose_spec h
  let coeff : (N : ℕ) → Fin N → ℝ :=
    fun N =>
      Classical.choose
        (concreteNBData.exists_optimal_coefficients_DN
          concreteGeneratorFamily N)
  {
    K := K
    hK := hspec.1
    coeff := coeff
    error_sq_le := by
      intro N
      have hcoeff :=
        Classical.choose_spec
          (concreteNBData.exists_optimal_coefficients_DN
            concreteGeneratorFamily N)
      rw [hcoeff]
      exact hspec.2 N
  }

/-- Exact producer-first normalization of the material gap. -/
theorem concreteCoefficientLogRate_iff_uniformLogDNBound :
    Nonempty ConcreteCoefficientLogRate ↔ ConcreteUniformLogDNBound := by
  constructor
  · rintro ⟨h⟩
    exact h.toUniformLogDNBound
  · intro h
    exact ⟨uniformLogDNBound_to_ConcreteCoefficientLogRate h⟩

#print axioms MCore.RH.R0.ConcreteCoefficientLogRate.toUniformLogDNBound
#print axioms MCore.RH.R0.uniformLogDNBound_to_ConcreteCoefficientLogRate
#print axioms MCore.RH.R0.concreteCoefficientLogRate_iff_uniformLogDNBound

end MCore.RH.R0
