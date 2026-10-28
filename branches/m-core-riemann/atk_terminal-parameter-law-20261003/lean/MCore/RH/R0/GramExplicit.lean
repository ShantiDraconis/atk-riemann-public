import MCore.RH.R0.ConcreteGramLogRate
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped BigOperators

namespace MCore.RH.R0

open MCore.RH.NB

/-- Concrete finite Gram matrix of the frozen generator family. -/
noncomputable def concreteGramMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => @inner ℝ concreteNBData.H _ (concreteGeneratorFamily i) (concreteGeneratorFamily j)

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

private theorem concreteGram_quadratic
    (N : ℕ) (x : Fin N → ℝ) :
    dotProduct x (Matrix.mulVec (concreteGramMatrix N) x) =
      @inner ℝ concreteNBData.H _
        (∑ i : Fin N, x i • concreteGeneratorFamily i)
        (∑ i : Fin N, x i • concreteGeneratorFamily i) := by
  unfold Matrix.mulVec dotProduct concreteGramMatrix
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Every finite concrete Gram matrix is positive semidefinite. -/
theorem concreteGramMatrix_posSemidef (N : ℕ) :
    (concreteGramMatrix N).PosSemidef := by
  constructor
  · ext i j
    simp [concreteGramMatrix, real_inner_comm]
  · intro x
    have hstar : star x = x := by
      ext i
      simp
    rw [hstar, concreteGram_quadratic]
    exact real_inner_self_nonneg

/-- Positive definiteness is exactly finite linear independence of the generators. -/
theorem concreteGramMatrix_posDef_iff_linearIndependent (N : ℕ) :
    (concreteGramMatrix N).PosDef ↔
      LinearIndependent ℝ (fun i : Fin N => concreteGeneratorFamily i) := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h x hsum
    by_contra hx
    have hx0 : x ≠ 0 := by
      intro hzero
      apply hx
      intro i
      exact congrFun hzero i
    have hq := h.2 x hx0
    have hstar : star x = x := by
      ext i
      simp
    rw [hstar, concreteGram_quadratic, hsum] at hq
    simpa using hq
  · intro h
    constructor
    · exact (concreteGramMatrix_posSemidef N).1
    · intro x hx
      have hstar : star x = x := by
        ext i
        simp
      rw [hstar, concreteGram_quadratic]
      have hsum :
          (∑ i : Fin N, x i • concreteGeneratorFamily i) ≠ 0 := by
        intro hs
        apply hx
        funext i
        exact h x hs i
      exact real_inner_self_pos.mpr hsum

/-- Existing scalar normal equations are exactly the matrix equation G_N c = b_N. -/
theorem concrete_normal_equations_iff_mulVec
    (N : ℕ) (c : Fin N → ℝ) :
    (∀ j : Fin N,
      (∑ i : Fin N,
        c i * concreteNBData.gramEntry concreteGeneratorFamily i j) =
        concreteNBData.targetEntry concreteGeneratorFamily j) ↔
      Matrix.mulVec (concreteGramMatrix N) c = concreteTargetVector N := by
  constructor
  · intro h
    funext j
    unfold Matrix.mulVec dotProduct concreteGramMatrix concreteTargetVector
    calc
      (∑ i : Fin N,
          @inner ℝ concreteNBData.H _
            (concreteGeneratorFamily j) (concreteGeneratorFamily i) * c i)
          =
        ∑ i : Fin N,
          c i * @inner ℝ concreteNBData.H _
            (concreteGeneratorFamily i) (concreteGeneratorFamily j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [real_inner_comm]
              ring
      _ = concreteNBData.targetEntry concreteGeneratorFamily j := by
            simpa [MCore.RH.NB.NBHilbertData.gramEntry] using h j
  · intro h j
    have hj := congr_fun h j
    unfold Matrix.mulVec dotProduct concreteGramMatrix concreteTargetVector at hj
    calc
      (∑ i : Fin N,
          c i * concreteNBData.gramEntry concreteGeneratorFamily i j)
          =
        ∑ i : Fin N,
          @inner ℝ concreteNBData.H _
            (concreteGeneratorFamily j) (concreteGeneratorFamily i) * c i := by
              apply Finset.sum_congr rfl
              intro i hi
              unfold MCore.RH.NB.NBHilbertData.gramEntry
              rw [real_inner_comm]
              ring
      _ = concreteNBData.targetEntry concreteGeneratorFamily j := hj

/-- The canonical optimal coefficients solve the explicit concrete Gram system. -/
theorem optimalGramCoeff_mulVec (N : ℕ) :
    Matrix.mulVec (concreteGramMatrix N) (optimalGramCoeff N) =
      concreteTargetVector N := by
  exact
    (concrete_normal_equations_iff_mulVec N (optimalGramCoeff N)).1
      (optimalGramCoeff_normal N)

#print axioms MCore.RH.R0.concreteGramMatrix_posSemidef
#print axioms MCore.RH.R0.concreteGramMatrix_posDef_iff_linearIndependent
#print axioms MCore.RH.R0.concrete_normal_equations_iff_mulVec
#print axioms MCore.RH.R0.optimalGramCoeff_mulVec

end MCore.RH.R0
