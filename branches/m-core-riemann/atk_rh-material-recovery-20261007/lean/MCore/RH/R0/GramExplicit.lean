import MCore.RH.R0.ConcreteGramLogRate
import Mathlib.Analysis.InnerProductSpace.GramMatrix

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB

/-- Concrete finite Gram matrix of the frozen generator family. -/
noncomputable def concreteGramMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.gram ℝ (fun i : Fin N => concreteGeneratorFamily i)

/-- Concrete target vector of inner products with chi. -/
noncomputable def concreteTargetVector (N : ℕ) : Fin N → ℝ :=
  fun i => concreteNBData.targetEntry concreteGeneratorFamily i

@[simp]
theorem concreteGramMatrix_apply (N : ℕ) (i j : Fin N) :
    concreteGramMatrix N i j =
      concreteNBData.gramEntry concreteGeneratorFamily i j := by
  rfl

@[simp]
theorem concreteTargetVector_apply (N : ℕ) (i : Fin N) :
    concreteTargetVector N i =
      concreteNBData.targetEntry concreteGeneratorFamily i := by
  rfl

/-- Every finite concrete Gram matrix is positive semidefinite. -/
theorem concreteGramMatrix_posSemidef (N : ℕ) :
    (concreteGramMatrix N).PosSemidef := by
  simpa [concreteGramMatrix] using
    (Matrix.posSemidef_gram ℝ
      (fun i : Fin N => concreteGeneratorFamily i))

/-- Positive definiteness is exactly finite linear independence of the generators. -/
theorem concreteGramMatrix_posDef_iff_linearIndependent (N : ℕ) :
    (concreteGramMatrix N).PosDef ↔
      LinearIndependent ℝ (fun i : Fin N => concreteGeneratorFamily i) := by
  simpa [concreteGramMatrix] using
    (Matrix.posDef_gram_iff_linearIndependent
      (𝕜 := ℝ)
      (v := fun i : Fin N => concreteGeneratorFamily i))

/-- Existing scalar normal equations are exactly the matrix equation G_N c = b_N. -/
theorem concrete_normal_equations_iff_mulVec
    (N : ℕ) (c : Fin N → ℝ) :
    (∀ j : Fin N,
      (∑ i : Fin N,
        c i * concreteNBData.gramEntry concreteGeneratorFamily i j) =
        concreteNBData.targetEntry concreteGeneratorFamily j) ↔
      concreteGramMatrix N *ᵥ c = concreteTargetVector N := by
  constructor
  · intro h
    funext j
    simpa [concreteGramMatrix, concreteTargetVector, Matrix.mulVec,
      dotProduct, mul_comm, real_inner_comm] using h j
  · intro h j
    have hj := congr_fun h j
    simpa [concreteGramMatrix, concreteTargetVector, Matrix.mulVec,
      dotProduct, mul_comm, real_inner_comm] using hj

/-- The canonical optimal coefficients solve the explicit concrete Gram system. -/
theorem optimalGramCoeff_mulVec (N : ℕ) :
    concreteGramMatrix N *ᵥ optimalGramCoeff N =
      concreteTargetVector N := by
  exact
    (concrete_normal_equations_iff_mulVec N (optimalGramCoeff N)).1
      (optimalGramCoeff_normal N)

#check concreteGramMatrix
#check concreteTargetVector
#print axioms MCore.RH.R0.concreteGramMatrix_posSemidef
#print axioms MCore.RH.R0.concreteGramMatrix_posDef_iff_linearIndependent
#print axioms MCore.RH.R0.concrete_normal_equations_iff_mulVec
#print axioms MCore.RH.R0.optimalGramCoeff_mulVec

end MCore.RH.R0
