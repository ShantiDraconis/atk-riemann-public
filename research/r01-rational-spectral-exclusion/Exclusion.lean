import Mathlib

namespace R01

def OnLine (s : ℂ) : Prop := s.re = 1 / 2

noncomputable def spectralBound (σ t : ℝ) : ℝ :=
  (2 * σ - 1) * ((1 - σ)^2 + t^2) / (σ^2 + t^2)^2

theorem spectralBound_pos {σ t : ℝ} (hl : 1 / 2 < σ) (hr : σ < 1) :
    0 < spectralBound σ t := by
  have hgap : 0 < 2 * σ - 1 := by linarith
  have hx : 0 < 1 - σ := by linarith
  have hy : 0 < σ := by linarith
  unfold spectralBound
  positivity

theorem cross_multiply {σ t U : ℝ} (hl : 1 / 2 < σ) :
    U < spectralBound σ t ↔
      U * (σ^2 + t^2)^2 < (2 * σ - 1) * ((1 - σ)^2 + t^2) := by
  have hy : 0 < σ := by linarith
  unfold spectralBound
  exact lt_div_iff₀ (by positivity)

theorem exclude_right {s : ℂ} {D U : ℝ} (hcert : D ≤ U)
    (hmellin : riemannZeta s = 0 → spectralBound s.re s.im ≤ D)
    (hstrict : U < spectralBound s.re s.im) :
    riemannZeta s ≠ 0 := by
  intro hz
  exact (not_lt_of_ge ((hmellin hz).trans hcert)) hstrict

theorem zero_classification (s : ℂ) :
    riemannZeta s = 0 ↔
      (riemannZeta s = 0 ∧ OnLine s) ∨
      (riemannZeta s = 0 ∧ ¬ OnLine s) := by
  classical
  by_cases h : OnLine s <;> simp [h]

#print axioms spectralBound_pos
#print axioms cross_multiply
#print axioms exclude_right
#print axioms zero_classification


/-- For k = 2 the modular column (1,0,1,0) kills the odd increments. -/
theorem four_cell_energy_gap (a b c d : ℝ) (hodd : a + c = 0)
    (htotal : a + b + c + d = 1) :
    2*a^2 + 6*b^2 + 12*c^2 + 20*d^2 - 60/13 =
      14*a^2 + 26*(b - 10/13)^2 := by
  have hc : c = -a := by linarith
  have hd : d = 1-b := by linarith
  rw [hc, hd]
  ring

theorem four_cell_exact_minimum :
    IsLeast {e : ℝ | ∃ a b c d : ℝ, a+c=0 ∧ a+b+c+d=1 ∧
      e = 2*a^2 + 6*b^2 + 12*c^2 + 20*d^2} (60/13) := by
  constructor
  · exact ⟨0, 10/13, 0, 3/13, by norm_num, by norm_num, by norm_num⟩
  · rintro e ⟨a, b, c, d, hodd, htotal, rfl⟩
    have h := four_cell_energy_gap a b c d hodd htotal
    nlinarith [sq_nonneg a, sq_nonneg (b - 10/13)]

#print axioms four_cell_energy_gap
#print axioms four_cell_exact_minimum

end R01
