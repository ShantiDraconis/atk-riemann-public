import Mathlib

/-!
# ATK — JensenDegreeTwo (criterio do discriminante, grau 2)

Formaliza o criterio de hiperbolicidade de grau 2 discutido na secao de
polinomios de Jensen: se `b² ≥ a·c` (com `a ≠ 0`), o polinomio quadratico
`a·X² + 2b·X + c` tem uma raiz real explicita. Isso e exatamente a condicao
`a_{k+1}² ≥ a_k·a_{k+2}` aplicada ao polinomio de Jensen de grau 2
`J(X) = a_k + 2 a_{k+1} X + a_{k+2} X²`.

Isso NAO demonstra hiperbolicidade para graus superiores, nem para todos os
deslocamentos simultaneamente, nem diz nada sobre os coeficientes reais da
funcao xi — e so o criterio do discriminante, verdadeiro para qualquer
quadratico real.
-/

namespace ATK.JensenDegreeTwo

/-- Criterio do discriminante: se `a ≠ 0` e `a·c ≤ b²`, entao
    `a·X² + 2b·X + c` tem uma raiz real explicita,
    `X = (r - b) / a`, com `r = √(b²-ac)`.

    Demonstracao estruturada para evitar qualquer cancelamento `a * a⁻¹`
    dentro de `ring` (que nao sabe usar `a ≠ 0` para isso): a unica
    divisao usada e a mais simples possivel, `a * ((r-b)/a) = r-b`, via
    `field_simp`; todo o resto e algebra polinomial pura. -/
theorem quadratic_has_real_root (a b c : ℝ) (ha : a ≠ 0) (hdisc : a * c ≤ b ^ 2) :
    ∃ x : ℝ, a * x ^ 2 + 2 * b * x + c = 0 := by
  have hnn : 0 ≤ b ^ 2 - a * c := by linarith
  set r := Real.sqrt (b ^ 2 - a * c) with hr
  have hsq : r ^ 2 = b ^ 2 - a * c := Real.sq_sqrt hnn
  have hy2 : (r - b) ^ 2 + 2 * b * (r - b) + a * c = 0 := by
    have hexpand : (r - b) ^ 2 + 2 * b * (r - b) + a * c = r ^ 2 - b ^ 2 + a * c := by
      ring
    rw [hexpand, hsq]; ring
  refine ⟨(r - b) / a, ?_⟩
  have hax : a * ((r - b) / a) = r - b := by field_simp
  have hmul : a * (a * ((r - b) / a) ^ 2 + 2 * b * ((r - b) / a) + c)
      = (a * ((r - b) / a)) ^ 2 + 2 * b * (a * ((r - b) / a)) + a * c := by ring
  rw [hax] at hmul
  rw [hy2] at hmul
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h ha
  · exact h

/-- Instancia nomeada: o polinomio de Jensen de grau 2,
    `J(X) = a_k + 2 a_{k+1} X + a_{k+2} X²`, tem raiz real quando
    `a_{k+1}² ≥ a_k·a_{k+2}` — a condicao de "hiperbolicidade" discutida
    para o grau 2. Caso particular direto de `quadratic_has_real_root`. -/
theorem jensen_degree_two_has_real_root
    (a_k a_k1 a_k2 : ℝ) (ha2 : a_k2 ≠ 0) (hdisc : a_k2 * a_k ≤ a_k1 ^ 2) :
    ∃ X : ℝ, a_k2 * X ^ 2 + 2 * a_k1 * X + a_k = 0 :=
  quadratic_has_real_root a_k2 a_k1 a_k ha2 hdisc

end ATK.JensenDegreeTwo

#print axioms ATK.JensenDegreeTwo.quadratic_has_real_root
#print axioms ATK.JensenDegreeTwo.jensen_degree_two_has_real_root
