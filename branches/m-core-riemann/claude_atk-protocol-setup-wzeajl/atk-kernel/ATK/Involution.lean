import Mathlib

/-!
# ATK — Involution (projetores complementares de S² = I)

Formaliza o "produtor de simetria" discutido: dado um elemento `S` com
`S² = 1`, os projetores `P± = (1±S)/2` sao idempotentes, ortogonais entre
si e somam a identidade. Primeiro em sua forma "dobrada" (sem dividir por
2, valida em qualquer anel comutativo — risco minimo); depois a versao
real com divisao explicita por 2.

Isso NAO prova nada sobre nenhuma conjectura do milenio: e uma identidade
algebrica generica sobre qualquer involucao `S² = 1`, que se aplicaria a
qualquer uma (reflexao critica, conjugacao, etc.) sem decidir nada sobre
o objeto especifico ao qual for aplicada.
-/

namespace ATK.Involution

variable {α : Type*} [CommRing α]

/-- Forma dobrada da idempotencia de `1+S`: `(1+S)² = 2(1+S)` quando
    `S² = 1`. Valida em qualquer anel comutativo. -/
theorem doubled_idempotent_plus (S : α) (hS : S ^ 2 = 1) :
    (1 + S) * (1 + S) = 2 * (1 + S) := by
  have h : (1 + S) * (1 + S) = 1 + 2 * S + S ^ 2 := by ring
  rw [h, hS]
  ring

/-- Forma dobrada da idempotencia de `1-S`. -/
theorem doubled_idempotent_minus (S : α) (hS : S ^ 2 = 1) :
    (1 - S) * (1 - S) = 2 * (1 - S) := by
  have h : (1 - S) * (1 - S) = 1 - 2 * S + S ^ 2 := by ring
  rw [h, hS]
  ring

/-- Ortogonalidade: `(1+S)(1-S) = 0` quando `S² = 1`. -/
theorem product_zero (S : α) (hS : S ^ 2 = 1) :
    (1 + S) * (1 - S) = 0 := by
  have h : (1 + S) * (1 - S) = 1 - S ^ 2 := by ring
  rw [h, hS]
  ring

/-- Soma a identidade (dobrada): `(1+S) + (1-S) = 2`. Nao precisa de `hS`. -/
theorem sum_doubled (S : α) : (1 + S) + (1 - S) = 2 := by ring

section Real

/-- Projetor `P+ = (1+S)/2`, em `ℝ`. -/
noncomputable def Pplus (S : ℝ) : ℝ := (1 + S) / 2

/-- Projetor `P- = (1-S)/2`, em `ℝ`. -/
noncomputable def Pminus (S : ℝ) : ℝ := (1 - S) / 2

/-- `P+` e idempotente quando `S² = 1`. -/
theorem Pplus_idem (S : ℝ) (hS : S ^ 2 = 1) : Pplus S ^ 2 = Pplus S := by
  unfold Pplus
  have key : (1 + S) ^ 2 = 2 * (1 + S) := by
    have h : (1 + S) ^ 2 = 1 + 2 * S + S ^ 2 := by ring
    rw [h, hS]; ring
  rw [div_pow, key]
  ring

/-- `P-` e idempotente quando `S² = 1`. -/
theorem Pminus_idem (S : ℝ) (hS : S ^ 2 = 1) : Pminus S ^ 2 = Pminus S := by
  unfold Pminus
  have key : (1 - S) ^ 2 = 2 * (1 - S) := by
    have h : (1 - S) ^ 2 = 1 - 2 * S + S ^ 2 := by ring
    rw [h, hS]; ring
  rw [div_pow, key]
  ring

/-- `P+` e `P-` sao ortogonais: `P+ · P- = 0`. -/
theorem Pplus_mul_Pminus (S : ℝ) (hS : S ^ 2 = 1) : Pplus S * Pminus S = 0 := by
  unfold Pplus Pminus
  have h : (1 + S) * (1 - S) = 0 := by
    have h' : (1 + S) * (1 - S) = 1 - S ^ 2 := by ring
    rw [h', hS]; ring
  rw [div_mul_div_comm, h]
  ring

/-- `P+ + P- = 1`, sem precisar de `S² = 1`. -/
theorem Pplus_add_Pminus (S : ℝ) : Pplus S + Pminus S = 1 := by
  unfold Pplus Pminus
  ring

end Real

end ATK.Involution

#print axioms ATK.Involution.doubled_idempotent_plus
#print axioms ATK.Involution.doubled_idempotent_minus
#print axioms ATK.Involution.product_zero
#print axioms ATK.Involution.sum_doubled
#print axioms ATK.Involution.Pplus_idem
#print axioms ATK.Involution.Pminus_idem
#print axioms ATK.Involution.Pplus_mul_Pminus
#print axioms ATK.Involution.Pplus_add_Pminus
