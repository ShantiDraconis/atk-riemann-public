import Mathlib

/-!
# ATK — CrossingFamily (a família G_λ, em versão real segura)

Formaliza o conteúdo algébrico real por trás da família polinomial
`G_λ(s) = ((s-1/2-λ)² + γ²)·((s-1/2+λ)² + γ²)` discutida como exemplo de
"zeros que cruzam entre crítico e externo". Em vez de trabalhar com `ℂ` e
`Complex.I` diretamente (risco de erro de sintaxe que eu não posso
verificar sem kernel local), formalizo o conteúdo real equivalente: com
`x = s - 1/2` tratado como variável real, o quártico

    quarticG λ γ x = (x² + γ² - λ²)² + 4γ²λ²

se fatora exatamente como o produto de dois quadrados deslocados, e no
caso degenerado `λ = 0` colapsa num quadrado perfeito — exatamente o fato
de que, nesse caso, os dois pares de zeros coincidem e a multiplicidade
sobe para 2. Isso é álgebra polinomial pura; não toca ξ nem ζ.
-/

namespace ATK.CrossingFamily

/-- O quártico central da família, como polinômio em `x` com parâmetros
    reais `λ` (deslocamento) e `γ` (altura). -/
noncomputable def quarticG (lam gam x : ℝ) : ℝ :=
  (x ^ 2 + gam ^ 2 - lam ^ 2) ^ 2 + 4 * gam ^ 2 * lam ^ 2

/-- Identidade de fatoração: o quártico é exatamente o produto dos dois
    fatores quadráticos associados aos pares de zeros `x = ±λ ± iγ`
    (parte real `x² ∓ 2λx + λ² + γ²`, aqui vista puramente como
    polinômio real). Pura álgebra — `ring` fecha sem hipóteses extras. -/
theorem factorization (lam gam x : ℝ) :
    quarticG lam gam x =
      ((x - lam) ^ 2 + gam ^ 2) * ((x + lam) ^ 2 + gam ^ 2) := by
  unfold quarticG
  ring

/-- Caso degenerado `λ = 0`: o quártico colapsa num quadrado perfeito.
    É o análogo algébrico de "os dois pares de zeros coincidem e a
    multiplicidade dobra" quando o deslocamento desaparece. -/
theorem degenerate_at_zero (gam x : ℝ) :
    quarticG 0 gam x = (x ^ 2 + gam ^ 2) ^ 2 := by
  unfold quarticG
  ring

/-- O quártico nunca é negativo, para quaisquer `λ, γ, x` reais — soma de
    um quadrado com um termo `4γ²λ² ≥ 0`. -/
theorem quarticG_nonneg (lam gam x : ℝ) : 0 ≤ quarticG lam gam x := by
  unfold quarticG
  positivity

end ATK.CrossingFamily

#print axioms ATK.CrossingFamily.factorization
#print axioms ATK.CrossingFamily.degenerate_at_zero
#print axioms ATK.CrossingFamily.quarticG_nonneg
