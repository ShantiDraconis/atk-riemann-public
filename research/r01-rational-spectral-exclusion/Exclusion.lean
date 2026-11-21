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

end R01
