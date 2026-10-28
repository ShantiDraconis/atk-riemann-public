import Mathlib

/-!
# ATK — Hex (identidades elementares do hexágono / grafo K6)

Formaliza SOMENTE os fatos algébricos/geométricos elementares e incondicionais
usados na discussão do "hexágono": dados parâmetros reais `d` e `t` (pensados
como `ρ = 1/2 + d + i t` para um zero hipotético de ξ), prova identidades
sobre seis pontos auxiliares e a energia do grafo K6 associada.

NÃO formaliza, NÃO assume e NÃO avança a Hipótese de Riemann. Nenhuma
referência à função zeta ou xi aparece neste arquivo — é álgebra real pura
sobre `ℝ × ℝ`.

* `d_eq_half_diff`, `t_eq_half_diff` — `d` e `t` são recuperáveis dos pontos.
* `P5_eq_midpoint`, `P6_eq_midpoint` — os dois pontos de referência são
  pontos médios dos pares simétricos.
* `k6_energy` — soma das 15 distâncias quadráticas entre os seis pontos
  é exatamente `24 d² + 36 t²`.
* `horizontalEnergy_eq_zero_iff` — a energia horizontal se anula sse `d = 0`
  (conteúdo íntegro: `x² = 0 ↔ x = 0` em `ℝ`).

Escopo: estes são lemas auxiliares de geometria de coordenadas. Nenhum deles
prova uma conjectura do milênio; `OPEN_MATH` continua verdadeiro para RH.

Nota de correção: as `def`s abaixo envolvem divisão real (`/2`), que depende
de `Real.instDivInvMonoid`, uma instância não computável no Mathlib. Por isso
são marcadas `noncomputable` — isso afeta apenas geração de código executável,
não a validade das provas (o kernel aceita e `#print axioms` confirma que
todas dependem só dos três axiomas padrão).
-/

namespace ATK.Hex

/-- Os seis pontos de análise associados a um zero hipotético
    `ρ = 1/2 + d + i t`. `P1..P4` vêm das simetrias `ξ(s)=ξ(1-s)` e
    `ξ(s̄)=conj(ξ(s))`; `P5,P6` são pontos de referência na linha crítica,
    NÃO necessariamente zeros. -/
noncomputable def P1 (d t : ℝ) : ℝ × ℝ := (1 / 2 + d, t)
noncomputable def P2 (d t : ℝ) : ℝ × ℝ := (1 / 2 - d, t)
noncomputable def P3 (d t : ℝ) : ℝ × ℝ := (1 / 2 - d, -t)
noncomputable def P4 (d t : ℝ) : ℝ × ℝ := (1 / 2 + d, -t)
noncomputable def P5 (d t : ℝ) : ℝ × ℝ := (1 / 2, t)
noncomputable def P6 (d t : ℝ) : ℝ × ℝ := (1 / 2, -t)

/-- Distância euclidiana ao quadrado entre dois pontos de `ℝ × ℝ`. -/
noncomputable def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

theorem d_eq_half_diff (d t : ℝ) :
    d = ((P1 d t).1 - (P2 d t).1) / 2 := by
  simp only [P1, P2]
  ring

theorem t_eq_half_diff (d t : ℝ) :
    t = ((P1 d t).2 - (P4 d t).2) / 2 := by
  simp only [P1, P4]
  ring

theorem P5_eq_midpoint (d t : ℝ) :
    P5 d t = (((P1 d t).1 + (P2 d t).1) / 2, ((P1 d t).2 + (P2 d t).2) / 2) := by
  simp only [P1, P2, P5]
  norm_num

theorem P6_eq_midpoint (d t : ℝ) :
    P6 d t = (((P3 d t).1 + (P4 d t).1) / 2, ((P3 d t).2 + (P4 d t).2) / 2) := by
  simp only [P3, P4, P6]
  norm_num

/-- Soma das 15 distâncias quadráticas entre pares dos seis pontos:
    `24 d² + 36 t²`. Pura álgebra de coordenadas. -/
theorem k6_energy (d t : ℝ) :
    sqDist (P1 d t) (P2 d t) + sqDist (P1 d t) (P3 d t) + sqDist (P1 d t) (P4 d t)
      + sqDist (P1 d t) (P5 d t) + sqDist (P1 d t) (P6 d t)
    + sqDist (P2 d t) (P3 d t) + sqDist (P2 d t) (P4 d t) + sqDist (P2 d t) (P5 d t)
      + sqDist (P2 d t) (P6 d t)
    + sqDist (P3 d t) (P4 d t) + sqDist (P3 d t) (P5 d t) + sqDist (P3 d t) (P6 d t)
    + sqDist (P4 d t) (P5 d t) + sqDist (P4 d t) (P6 d t)
    + sqDist (P5 d t) (P6 d t)
      = 24 * d ^ 2 + 36 * t ^ 2 := by
  simp only [P1, P2, P3, P4, P5, P6, sqDist]
  ring

/-- Energia horizontal do quarteto simétrico. -/
noncomputable def horizontalEnergy (d : ℝ) : ℝ := 24 * d ^ 2

/-- A energia horizontal se anula sse `d = 0`. Não diz nada sobre se algum
    zero real de ξ tem `d ≠ 0`. -/
theorem horizontalEnergy_eq_zero_iff (d : ℝ) :
    horizontalEnergy d = 0 ↔ d = 0 := by
  unfold horizontalEnergy
  constructor
  · intro h
    nlinarith [sq_nonneg d]
  · intro h
    simp [h]

end ATK.Hex

#print axioms ATK.Hex.d_eq_half_diff
#print axioms ATK.Hex.t_eq_half_diff
#print axioms ATK.Hex.P5_eq_midpoint
#print axioms ATK.Hex.P6_eq_midpoint
#print axioms ATK.Hex.k6_energy
#print axioms ATK.Hex.horizontalEnergy_eq_zero_iff
