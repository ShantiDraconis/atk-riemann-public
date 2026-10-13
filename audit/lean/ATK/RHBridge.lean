import Mathlib
import ATK.Exact

/-!
# ATK — Riemann: ponte condicional no formato da ponte NS (`clayC_of_fc`)

* **Alvo exato** (portão ATK): `RiemannHypothesis` da Mathlib.
* **Hipótese H**: `NoZerosRightOfHalf` — `ζ(s) ≠ 0` para `Re s > 1/2`.
* **Ponte**: `rh_of_noZerosRightOfHalf : NoZerosRightOfHalf → RiemannHypothesis`, pela equação
  funcional da Mathlib (`riemannZeta_one_sub`): um zero não trivial com `Re s < 1/2` reflete-se
  em `1 − s`, com `Re(1 − s) > 1/2`; os únicos zeros que a reflexão não alcança são os
  triviais `−2(n+1)`.

Força da hipótese (registrada): `noZerosRightOfHalf_of_rh` prova a recíproca, logo H é
**equivalente** ao alvo. A ponte reduz o problema à metade direita da faixa crítica
`1/2 < Re s < 1` (em `Re s ≥ 1` a Mathlib já prova `ζ ≠ 0`: `riemannZeta_ne_zero_of_one_le_re`).
A etapa seguinte do programa (Nyman–Beurling/Báez-Duarte: aproximação de `χ_(0,1]` em `L²` pela
família `ρ(1/(kx))`, para onde aponta a numérica de `D_N`) implica H — ainda não formalizada.
-/

noncomputable section

namespace ATK.RHBridge

open Complex

/-- **Hipótese H**: `ζ` não se anula no semiplano `Re s > 1/2`. -/
def NoZerosRightOfHalf : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0

/-- Reflexão de zeros: se `ζ(s) = 0`, `Re s < 1/2` e `s ≠ 0`, então `ζ(1 − s) = 0`
ou `s` é um zero trivial `−2(n+1)`. -/
theorem left_zero_reflects {s : ℂ} (hs : riemannZeta s = 0) (hre : s.re < 1 / 2)
    (hs0 : s ≠ 0) : riemannZeta (1 - s) = 0 ∨ ∃ n : ℕ, s = -2 * (n + 1) := by
  set t : ℂ := 1 - s with ht
  have htre' : t.re = 1 - s.re := by rw [ht, sub_re, one_re]
  have htre : 1 / 2 < t.re := by rw [htre']; linarith
  have htn : ∀ n : ℕ, t ≠ -n := by
    intro n hn
    have h1 := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h1
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have ht1 : t ≠ 1 := by
    intro h
    apply hs0
    have h' : (1 : ℂ) - s = 1 := by rw [← ht]; exact h
    linear_combination -h'
  have h1t : 1 - t = s := by rw [ht]; ring
  have hfe := riemannZeta_one_sub htn ht1
  rw [h1t, hs] at hfe
  have h2pi : 2 * (π : ℂ) ≠ 0 := mod_cast by positivity
  have hpow : (2 * (π : ℂ)) ^ (-t) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact h2pi h
  have hG : Gamma t ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  rcases mul_eq_zero.mp hfe.symm with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact absurd h hpow
      · exact absurd h hG
    · -- `cos(π t / 2) = 0` ⇒ `t = 2k + 1` ⇒ `s = −2k`
      right
      obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp h
      have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      have hk2 : (π : ℂ) * t = (π : ℂ) * (2 * k + 1) := by linear_combination 2 * hk
      have htk : t = 2 * k + 1 := mul_left_cancel₀ hpi hk2
      have hsk : s = -2 * (k : ℂ) := by rw [← h1t, htk]; ring
      have hkre := congrArg Complex.re hsk
      simp only [mul_re, neg_re, intCast_re, intCast_im, mul_zero, sub_zero] at hkre
      norm_num at hkre
      have hkpos : 1 ≤ k := by
        have hk0 : k ≠ 0 := by
          rintro rfl
          apply hs0
          rw [hsk]
          simp
        have hkm : (-1 : ℤ) < k := by
          by_contra hc
          push_neg at hc
          have hc' : (k : ℝ) ≤ -1 := by exact_mod_cast hc
          linarith
        omega
      refine ⟨(k - 1).toNat, ?_⟩
      have hnat : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
      have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
        have h3 : ((((k - 1).toNat : ℕ) : ℤ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by rw [hnat]
        rw [Int.cast_natCast] at h3
        rw [h3]
        push_cast
        ring
      rw [hsk, hc]
      ring
  · left
    exact h

/-- **Ponte certificada** `H → alvo exato`. -/
theorem rh_of_noZerosRightOfHalf (H : NoZerosRightOfHalf) : RiemannHypothesis := by
  intro s hs htriv _
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hs
      norm_num at hs
    rcases left_zero_reflects hs hlt hs0 with h | h
    · refine H (1 - s) ?_ h
      rw [sub_re, one_re]
      linarith
    · exact htriv h
  · exact heq
  · exact absurd hs (H s hgt)

/-- Recíproca: RH implica H. Logo H é equivalente ao alvo (força registrada). -/
theorem noZerosRightOfHalf_of_rh (h : RiemannHypothesis) : NoZerosRightOfHalf := by
  intro s hre hz
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  · push_neg at h1
    have hntriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have h2 := congrArg Complex.re hn
      simp only [mul_re, neg_re, add_re, natCast_re, one_re, add_im, natCast_im, one_im,
        mul_zero, sub_zero] at h2
      norm_num at h2
      have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hs1 : s ≠ 1 := by
      rintro rfl
      norm_num at h1
    have := h s hz hntriv hs1
    linarith

theorem rh_iff_noZerosRightOfHalf : RiemannHypothesis ↔ NoZerosRightOfHalf :=
  ⟨noZerosRightOfHalf_of_rh, rh_of_noZerosRightOfHalf⟩

/-- Falsificador: um zero com `Re s > 1/2` refuta H e, pela equivalência, RH. -/
theorem not_rh_of_zero {s : ℂ} (hre : 1 / 2 < s.re) (hz : riemannZeta s = 0) :
    ¬ RiemannHypothesis :=
  fun h => noZerosRightOfHalf_of_rh h s hre hz

end ATK.RHBridge

end

#print axioms ATK.RHBridge.left_zero_reflects
#print axioms ATK.RHBridge.rh_of_noZerosRightOfHalf
#print axioms ATK.RHBridge.noZerosRightOfHalf_of_rh
#print axioms ATK.RHBridge.rh_iff_noZerosRightOfHalf
#print axioms ATK.RHBridge.not_rh_of_zero
