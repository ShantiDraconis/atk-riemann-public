import Mathlib
import ATK.Exact
import ATK.RHBridge

/-!
# ATK — Riemann no regime suave: o que JÁ é teorema sobre os zeros

No NS, a versão com força fechou. Em Riemann, o que fecha hoje no kernel é a estrutura clássica
dos zeros (não a reta crítica):

* `critical_strip` — todo zero não trivial está na faixa aberta `0 < Re s < 1`;
* `zero_reflection` — os zeros da faixa vêm em pares `s ↔ 1 − s` (simetria em torno de `Re = 1/2`);
* `trivial_zeros` — `−2, −4, −6, …` são zeros.

O que NÃO fecha: que a parte real seja exatamente `1/2` (RH). A faixa crítica tem largura 1; a
hipótese de Riemann a reduz a uma reta, e nenhum método conhecido faz isso.
-/

noncomputable section

namespace ATK.RHStrip

open Complex

theorem zero_re_lt_one {s : ℂ} (hs : riemannZeta s = 0) : s.re < 1 := by
  by_contra h
  push_neg at h
  exact riemannZeta_ne_zero_of_one_le_re h hs

theorem nontrivial_zero_re_pos {s : ℂ} (hs : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra h
  push_neg at h
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  rcases ATK.RHBridge.left_zero_reflects hs (by linarith) hs0 with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [sub_re, one_re]; linarith) h1
  · exact htriv h1

/-- **Faixa crítica**: todo zero não trivial satisfaz `0 < Re s < 1`. -/
theorem critical_strip : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    0 < s.re ∧ s.re < 1 :=
  fun _ hs htriv _ => ⟨nontrivial_zero_re_pos hs htriv, zero_re_lt_one hs⟩

/-- **Simetria**: se `s` é zero com `Re s > 0` e `s ≠ 1`, então `1 − s` também é zero. -/
theorem zero_reflection : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s ≠ 1 →
    riemannZeta (1 - s) = 0 := by
  intro s hs hpos hs1
  have hn : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have h1 := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h1
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [riemannZeta_one_sub hn hs1, hs, mul_zero]

/-- Os zeros triviais. -/
theorem trivial_zeros : ∀ n : ℕ, riemannZeta (-2 * (n + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one

end ATK.RHStrip

end

#print axioms ATK.RHStrip.zero_re_lt_one
#print axioms ATK.RHStrip.nontrivial_zero_re_pos
#print axioms ATK.RHStrip.critical_strip
#print axioms ATK.RHStrip.zero_reflection
#print axioms ATK.RHStrip.trivial_zeros
