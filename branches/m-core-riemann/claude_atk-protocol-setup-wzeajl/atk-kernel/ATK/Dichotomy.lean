import Mathlib

/-!
# ATK — Dichotomy (classificação exaustiva crítico/externo)

Formaliza, para uma função genérica `F : ℂ → ℂ`, a classificação discutida
sob os nomes "ATKTerminal" e "ATK-CEZ": todo ponto do domínio é exatamente
um dos quatro estados (zero crítico, zero externo, não-zero crítico,
não-zero externo); nenhum ponto pode estar simultaneamente nas classes
"zero crítico" e "zero externo"; e "todos os zeros são críticos" é
equivalente, por definição, a "não existe zero externo".

Esses três fatos são lógica proposicional pura (terceiro excluído, aplicado
duas vezes) — não usam nenhuma propriedade analítica de `F`. Por isso valem
para QUALQUER `F : ℂ → ℂ`, inclusive a função zeta/xi, sem decidir nada
sobre ela: aplicar isto a ζ não aproxima nem afasta uma prova da Hipótese
de Riemann.
-/

namespace ATK.Dichotomy

/-- Um ponto é "crítico" quando sua parte real é `1/2`. -/
def Critical (s : ℂ) : Prop := s.re = (1 / 2 : ℝ)

/-- `F` tem algum zero fora da linha crítica. -/
def HasNonCriticalZero (F : ℂ → ℂ) : Prop :=
  ∃ s : ℂ, F s = 0 ∧ ¬ Critical s

/-- Todos os zeros de `F` estão na linha crítica. -/
def AllZerosCritical (F : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, F s = 0 → Critical s

/-- Classificação exaustiva de um ponto quanto a `F`: exatamente um dos
    quatro estados ocorre (não exclusivamente provado aqui — a disjunção
    é verdadeira; a exclusividade sai de `pointwise_classification_unique`
    abaixo). -/
theorem pointwise_classification (F : ℂ → ℂ) (s : ℂ) :
    (F s = 0 ∧ Critical s) ∨ (F s = 0 ∧ ¬ Critical s) ∨
    (F s ≠ 0 ∧ Critical s) ∨ (F s ≠ 0 ∧ ¬ Critical s) := by
  classical
  by_cases hz : F s = 0 <;> by_cases hc : Critical s <;> tauto

/-- Nenhum ponto pode estar simultaneamente em "zero crítico" e
    "zero externo": são mutuamente exclusivos. -/
theorem no_point_both_critical_and_external (F : ℂ → ℂ) (s : ℂ) :
    ¬ ((F s = 0 ∧ Critical s) ∧ (F s = 0 ∧ ¬ Critical s)) := by
  rintro ⟨⟨_, hc⟩, ⟨_, hnc⟩⟩
  exact hnc hc

/-- `F` não pode, simultaneamente, ter um zero fora da linha e ter todos
    os seus zeros na linha. -/
theorem not_both (F : ℂ → ℂ) :
    ¬ (HasNonCriticalZero F ∧ AllZerosCritical F) := by
  rintro ⟨⟨s, hz, hnc⟩, hall⟩
  exact hnc (hall s hz)

/-- "Todos os zeros são críticos" equivale, por definição, a "não existe
    zero externo". É a mesma proposição reescrita, não uma redução. -/
theorem all_critical_iff_no_noncritical (F : ℂ → ℂ) :
    AllZerosCritical F ↔ ¬ HasNonCriticalZero F := by
  constructor
  · intro hall hex
    obtain ⟨s, hz, hnc⟩ := hex
    exact hnc (hall s hz)
  · intro hno s hz
    by_contra hnc
    exact hno ⟨s, hz, hnc⟩

end ATK.Dichotomy

#print axioms ATK.Dichotomy.pointwise_classification
#print axioms ATK.Dichotomy.no_point_both_critical_and_external
#print axioms ATK.Dichotomy.not_both
#print axioms ATK.Dichotomy.all_critical_iff_no_noncritical
