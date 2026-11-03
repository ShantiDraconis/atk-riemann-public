import MCore.RH.R0.VasyuninFiniteGram

namespace MCore.RH.R0

/-- The one-by-one Vasyunin cotangent sum vanishes. -/
@[simp] theorem vasyuninSum_one_one :
    vasyuninSum 1 1 = 0 := by
  simp [vasyuninSum]

/-- Exact diagonal value of the finite Vasyunin Gram kernel. -/
theorem vasyuninGramEntry_diag
    (n : ℕ) (hn : 0 < n) :
    vasyuninGramEntry n n =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / n := by
  unfold vasyuninGramEntry reducedNumerator reducedDenominator
  have hg : Nat.gcd n n = n := Nat.gcd_self n
  rw [hg]
  have hdiv : n / n = 1 := Nat.div_self hn
  rw [hdiv]
  simp [vasyuninSum]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  ring

/-- Exact diagonal of the Vasyunin Gram matrix. -/
theorem vasyuninGramMatrix_diag
    (N : ℕ) (i : Fin N) :
    vasyuninGramMatrix N i i =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) /
        (((rhoIndex i : ℕ) : ℝ)) := by
  unfold vasyuninGramMatrix
  exact vasyuninGramEntry_diag (rhoIndex i) (rhoIndex_pos i)

/-- The finite formula is symmetric, as required of a Gram kernel. -/
theorem vasyuninGramEntry_symm
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    vasyuninGramEntry p q = vasyuninGramEntry q p := by
  unfold vasyuninGramEntry reducedNumerator reducedDenominator
  rw [Nat.gcd_comm q p]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpne : (p : ℝ) ≠ 0 := hpR.ne'
  have hqne : (q : ℝ) ≠ 0 := hqR.ne'
  rw [Real.log_div hpR.ne' hqR.ne', Real.log_div hqR.ne' hpR.ne']
  ring

theorem vasyuninGramMatrix_symm
    (N : ℕ) :
    (vasyuninGramMatrix N).IsHermitian := by
  intro i j
  simp only [starRingEnd_apply, star_trivial]
  exact vasyuninGramEntry_symm
    (rhoIndex j) (rhoIndex i) (rhoIndex_pos j) (rhoIndex_pos i)

#print axioms MCore.RH.R0.vasyuninGramEntry_diag
#print axioms MCore.RH.R0.vasyuninGramEntry_symm
#print axioms MCore.RH.R0.vasyuninGramMatrix_symm

end MCore.RH.R0
