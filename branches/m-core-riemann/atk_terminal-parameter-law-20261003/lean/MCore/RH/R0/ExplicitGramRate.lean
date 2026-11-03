import MCore.RH.R0.GramInverse
import MCore.RH.R0.TargetClosedForm
import MCore.RH.R0.GramAutocorrelation
import MCore.RH.R0.ChiNorm

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB

/-- Completely explicit target vector; no Hilbert inner product remains. -/
noncomputable def explicitTargetVector (N : ℕ) : Fin N → ℝ :=
  fun i =>
    (Real.log ((rhoIndex i : ℕ) : ℝ) + 1 - Real.eulerMascheroniConstant) /
      (((rhoIndex i : ℕ) : ℝ))

/-- Completely explicit Gram matrix through the multiplicative fractional autocorrelation kernel. -/
noncomputable def explicitGramMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (1 / (((rhoIndex i : ℕ) : ℝ))) *
      fractionalAutocorrelation
        ((((rhoIndex i : ℕ) : ℝ)) / (((rhoIndex j : ℕ) : ℝ)))

theorem explicitTargetVector_eq_concrete (N : ℕ) :
    explicitTargetVector N = concreteTargetVector N := by
  funext i
  exact (concreteTargetVector_closed_form N i).symm

theorem explicitGramMatrix_eq_concrete (N : ℕ) :
    explicitGramMatrix N = concreteGramMatrix N := by
  ext i j
  exact (concreteGramMatrix_eq_fractionalAutocorrelation N i j).symm

/-- Explicit inverse-Gram coefficient vector. -/
noncomputable def explicitOptimalCoeff (N : ℕ) : Fin N → ℝ :=
  (explicitGramMatrix N)⁻¹ *ᵥ explicitTargetVector N

/-- Completely explicit finite-stage squared residual. -/
noncomputable def explicitGramResidual (N : ℕ) : ℝ :=
  1 - dotProduct (explicitTargetVector N) (explicitOptimalCoeff N)

theorem explicitOptimalCoeff_eq_canonical (N : ℕ) :
    explicitOptimalCoeff N = optimalGramCoeff N := by
  unfold explicitOptimalCoeff
  rw [explicitGramMatrix_eq_concrete, explicitTargetVector_eq_concrete]
  exact (optimalGramCoeff_eq_inv_mulVec_target N).symm

/--
The canonical DN is exactly the finite-dimensional inverse-Gram residual.
No projection-space notation remains on the right.
-/
theorem concreteDN_eq_explicitGramResidual (N : ℕ) :
    concreteNBData.DN concreteGeneratorFamily N =
      explicitGramResidual N := by
  rw [optimalGramCoeff_reduced_energy]
  rw [concreteNBData_chi_norm]
  unfold explicitGramResidual
  rw [explicitOptimalCoeff_eq_canonical]
  rw [explicitTargetVector_eq_concrete]
  simp only [one_pow]
  unfold dotProduct
  apply congrArg (fun z : ℝ => 1 - z)
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- H1 in fully explicit arithmetic/autocorrelation form. -/
def ExplicitGramRateTarget : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ,
      explicitGramResidual N ≤ logMajorant K N

/--
The fully explicit inverse-Gram rate is definitionally equivalent to the canonical
uniform logarithmic DN producer.
-/
theorem explicitGramRateTarget_iff_uniformLogDNBound :
    ExplicitGramRateTarget ↔ ConcreteUniformLogDNBound := by
  constructor
  · rintro ⟨K, hK, hbound⟩
    refine ⟨K, hK, ?_⟩
    intro N
    rw [concreteDN_eq_explicitGramResidual]
    exact hbound N
  · rintro ⟨K, hK, hbound⟩
    refine ⟨K, hK, ?_⟩
    intro N
    rw [← concreteDN_eq_explicitGramResidual]
    exact hbound N

#print axioms MCore.RH.R0.explicitTargetVector_eq_concrete
#print axioms MCore.RH.R0.explicitGramMatrix_eq_concrete
#print axioms MCore.RH.R0.concreteDN_eq_explicitGramResidual
#print axioms MCore.RH.R0.explicitGramRateTarget_iff_uniformLogDNBound

end MCore.RH.R0
