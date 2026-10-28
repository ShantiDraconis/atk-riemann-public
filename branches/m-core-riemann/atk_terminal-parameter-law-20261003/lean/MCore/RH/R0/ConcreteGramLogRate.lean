import MCore.RH.R0.HardFrontier
import MCore.RH.R0.ChiNorm
import MCore.RH.NB.GramEnergy

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
Quantitative Gram normal-equation form of the canonical logarithmic producer.
For each N we require an exact normal-equation solution whose reduced optimal
energy is bounded by the logarithmic majorant.
-/
structure ConcreteGramLogRate where
  K : ℝ
  hK : 0 ≤ K
  coeff : (N : ℕ) → Fin N → ℝ
  normal :
    ∀ (N : ℕ) (j : Fin N),
      (∑ i : Fin N,
        coeff N i *
          concreteNBData.gramEntry concreteGeneratorFamily i j) =
        concreteNBData.targetEntry concreteGeneratorFamily j
  reduced_energy_le :
    ∀ N : ℕ,
      1 - (∑ i : Fin N,
        coeff N i *
          concreteNBData.targetEntry concreteGeneratorFamily i) ≤
        logMajorant K N

/-- A quantitative Gram certificate yields the canonical DN logarithmic bound. -/
theorem ConcreteGramLogRate.toUniformLogDNBound
    (h : ConcreteGramLogRate) :
    ConcreteUniformLogDNBound := by
  refine ⟨h.K, h.hK, ?_⟩
  intro N
  have henergy :
      concreteNBData.coefficientEnergy concreteGeneratorFamily N (h.coeff N) =
        ‖concreteNBData.chi‖ ^ 2 -
          ∑ i : Fin N,
            h.coeff N i *
              concreteNBData.targetEntry concreteGeneratorFamily i :=
    concreteNBData.coefficientEnergy_of_normal_equations
      concreteGeneratorFamily N (h.coeff N) (h.normal N)
  have herr :
      ‖concreteNBData.chi -
        concreteNBData.coefficientApproximantAt
          concreteGeneratorFamily N (h.coeff N)‖ ^ 2 =
        concreteNBData.coefficientEnergy
          concreteGeneratorFamily N (h.coeff N) :=
    concreteNBData.coefficient_error_sq_eq_energy
      concreteGeneratorFamily N (h.coeff N)
  have hdnle :
      concreteNBData.DN concreteGeneratorFamily N ≤
        ‖concreteNBData.chi -
          concreteNBData.coefficientApproximantAt
            concreteGeneratorFamily N (h.coeff N)‖ ^ 2 :=
    concreteNBData.DN_le_coefficient_error_sq
      concreteGeneratorFamily N (h.coeff N)
  calc
    concreteNBData.DN concreteGeneratorFamily N
        ≤ ‖concreteNBData.chi -
            concreteNBData.coefficientApproximantAt
              concreteGeneratorFamily N (h.coeff N)‖ ^ 2 := hdnle
    _ = concreteNBData.coefficientEnergy
          concreteGeneratorFamily N (h.coeff N) := herr
    _ = ‖concreteNBData.chi‖ ^ 2 -
          ∑ i : Fin N,
            h.coeff N i *
              concreteNBData.targetEntry concreteGeneratorFamily i := henergy
    _ = 1 -
          ∑ i : Fin N,
            h.coeff N i *
              concreteNBData.targetEntry concreteGeneratorFamily i := by
          rw [concreteNBData_chi_norm]
          norm_num
    _ ≤ logMajorant h.K N := h.reduced_energy_le N

/-- Canonical optimal coefficient vector chosen from the certified projection theorem. -/
noncomputable def optimalGramCoeff (N : ℕ) : Fin N → ℝ :=
  Classical.choose
    (concreteNBData.exists_optimal_coefficients_reduced_energy
      concreteGeneratorFamily N)

theorem optimalGramCoeff_reduced_energy (N : ℕ) :
    concreteNBData.DN concreteGeneratorFamily N =
      ‖concreteNBData.chi‖ ^ 2 -
        ∑ i : Fin N,
          optimalGramCoeff N i *
            concreteNBData.targetEntry concreteGeneratorFamily i :=
  (Classical.choose_spec
    (concreteNBData.exists_optimal_coefficients_reduced_energy
      concreteGeneratorFamily N)).1

theorem optimalGramCoeff_normal (N : ℕ) :
    ∀ j : Fin N,
      (∑ i : Fin N,
        optimalGramCoeff N i *
          concreteNBData.gramEntry concreteGeneratorFamily i j) =
        concreteNBData.targetEntry concreteGeneratorFamily j :=
  (Classical.choose_spec
    (concreteNBData.exists_optimal_coefficients_reduced_energy
      concreteGeneratorFamily N)).2

/--
Conversely, every canonical DN logarithmic bound has an optimal coefficient
vector satisfying the Gram normal equations at each stage, so this Gram
formulation loses no information.
-/
noncomputable def uniformLogDNBound_to_ConcreteGramLogRate
    (h : ConcreteUniformLogDNBound) :
    ConcreteGramLogRate := by
  let B : ConcreteLogDNBound :=
    Classical.choice (concreteUniformLogDNBound_iff_nonempty.mp h)
  refine {
    K := B.K
    hK := B.hK
    coeff := optimalGramCoeff
    normal := ?_
    reduced_energy_le := ?_
  }
  · intro N j
    exact optimalGramCoeff_normal N j
  · intro N
    have hchi : ‖concreteNBData.chi‖ ^ 2 = 1 := by
      rw [concreteNBData_chi_norm]
      norm_num
    have hEq :
        concreteNBData.DN concreteGeneratorFamily N =
          1 - ∑ i : Fin N,
            optimalGramCoeff N i *
              concreteNBData.targetEntry concreteGeneratorFamily i := by
      calc
        concreteNBData.DN concreteGeneratorFamily N
            = ‖concreteNBData.chi‖ ^ 2 -
                ∑ i : Fin N,
                  optimalGramCoeff N i *
                    concreteNBData.targetEntry concreteGeneratorFamily i :=
              optimalGramCoeff_reduced_energy N
        _ = 1 - ∑ i : Fin N,
                optimalGramCoeff N i *
                  concreteNBData.targetEntry concreteGeneratorFamily i := by rw [hchi]
    rw [← hEq]
    exact B.dn_le N

theorem concreteGramLogRate_iff_uniformLogDNBound :
    Nonempty ConcreteGramLogRate ↔ ConcreteUniformLogDNBound := by
  constructor
  · rintro ⟨h⟩
    exact h.toUniformLogDNBound
  · intro h
    exact ⟨uniformLogDNBound_to_ConcreteGramLogRate h⟩

#print axioms MCore.RH.R0.optimalGramCoeff_reduced_energy
#print axioms MCore.RH.R0.optimalGramCoeff_normal
#print axioms MCore.RH.R0.ConcreteGramLogRate.toUniformLogDNBound
#print axioms MCore.RH.R0.uniformLogDNBound_to_ConcreteGramLogRate
#print axioms MCore.RH.R0.concreteGramLogRate_iff_uniformLogDNBound

end MCore.RH.R0
