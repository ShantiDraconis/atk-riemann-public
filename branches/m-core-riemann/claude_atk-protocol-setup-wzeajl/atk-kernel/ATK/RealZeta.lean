import Mathlib

/-!
# ATK — RealZeta (tocando a funcao zeta real do Mathlib)

Diferente de todos os outros arquivos ATK, este toca diretamente a funcao
`riemannZeta : ℂ → ℂ` que ja existe no Mathlib (nao uma funcao generica
`F : ℂ → ℂ`). Usa dois teoremas reais do Mathlib, confirmados na
documentacao antes de escrever qualquer coisa aqui (nao advinhados):

* `riemannZeta_zero : riemannZeta 0 = -1 / 2`
* `riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n+1)) = 0`
  (os zeros triviais)

A partir desses dois fatos ja demonstrados no Mathlib, derivamos
instancias numericas concretas e uma distincao explicita entre um valor
nao nulo e um zero trivial.

Isso NAO toca a faixa critica, nao toca zeros nao triviais, nao toca a
Hipotese de Riemann. `RiemannHypothesis` no Mathlib e uma `def`
(proposicao), nao um teorema demonstrado — nao aparece aqui.
-/

namespace ATK.RealZeta

/-- ζ(0) = -1/2 ≠ 0. -/
theorem riemannZeta_zero_ne_zero : riemannZeta 0 ≠ 0 := by
  rw [riemannZeta_zero]
  norm_num

/-- Primeiro zero trivial: ζ(-2) = 0 (caso `n = 0` do teorema geral). -/
theorem riemannZeta_neg_two : riemannZeta (-2 : ℂ) = 0 := by
  have h := riemannZeta_neg_two_mul_nat_add_one 0
  norm_num at h
  exact h

/-- Segundo zero trivial: ζ(-4) = 0 (caso `n = 1`). -/
theorem riemannZeta_neg_four : riemannZeta (-4 : ℂ) = 0 := by
  have h := riemannZeta_neg_two_mul_nat_add_one 1
  norm_num at h
  exact h

/-- Terceiro zero trivial: ζ(-6) = 0 (caso `n = 2`). -/
theorem riemannZeta_neg_six : riemannZeta (-6 : ℂ) = 0 := by
  have h := riemannZeta_neg_two_mul_nat_add_one 2
  norm_num at h
  exact h

/-- ζ(0) e ζ(-2) sao valores distintos da mesma funcao: um nao-zero
    (`-1/2`), outro um zero trivial. Toca `riemannZeta` de verdade; nao
    decide absolutamente nada sobre zeros nao triviais ou RH. -/
theorem riemannZeta_zero_ne_riemannZeta_neg_two :
    riemannZeta 0 ≠ riemannZeta (-2) := by
  rw [riemannZeta_zero, riemannZeta_neg_two]
  norm_num

end ATK.RealZeta

#print axioms ATK.RealZeta.riemannZeta_zero_ne_zero
#print axioms ATK.RealZeta.riemannZeta_neg_two
#print axioms ATK.RealZeta.riemannZeta_neg_four
#print axioms ATK.RealZeta.riemannZeta_neg_six
#print axioms ATK.RealZeta.riemannZeta_zero_ne_riemannZeta_neg_two
