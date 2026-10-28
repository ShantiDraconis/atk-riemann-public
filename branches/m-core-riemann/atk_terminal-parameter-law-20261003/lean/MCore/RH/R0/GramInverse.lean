import MCore.RH.R0.LinearIndependent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace MCore.RH.R0

/-- B3: positive definiteness gives nonzero determinant. -/
theorem concreteGramMatrix_det_ne_zero (N : ℕ) :
    (concreteGramMatrix N).det ≠ 0 := by
  have hunit : IsUnit (concreteGramMatrix N) :=
    (concreteGramMatrix_posDef N).isUnit
  have hdetunit : IsUnit (concreteGramMatrix N).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  exact hdetunit.ne_zero

/-- B2: the canonical optimal coefficient vector is the inverse-Gram solution. -/
theorem optimalGramCoeff_eq_inv_mulVec_target (N : ℕ) :
    optimalGramCoeff N =
      (concreteGramMatrix N)⁻¹.mulVec (concreteTargetVector N) := by
  letI : Invertible (concreteGramMatrix N) :=
    (concreteGramMatrix_posDef N).isUnit.invertible
  have hnormal :
      concreteTargetVector N =
        (concreteGramMatrix N).mulVec (optimalGramCoeff N) := by
    exact (optimalGramCoeff_mulVec N).symm
  have hinv :
      (concreteGramMatrix N)⁻¹.mulVec (concreteTargetVector N) =
        optimalGramCoeff N :=
    Matrix.inv_mulVec_eq_vec hnormal
  exact hinv.symm

#print axioms MCore.RH.R0.concreteGramMatrix_det_ne_zero
#print axioms MCore.RH.R0.optimalGramCoeff_eq_inv_mulVec_target

end MCore.RH.R0
