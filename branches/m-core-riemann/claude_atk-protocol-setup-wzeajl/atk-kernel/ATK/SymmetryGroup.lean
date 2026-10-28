import Mathlib

/-!
# ATK — SymmetryGroup (Z₂×Z₂ de reflexao e conjugacao)

Formaliza a estrutura de grupo discutida para os operadores de simetria:
`Refl(σ,t) = (1-σ,t)` (reflexao em torno da linha critica) e
`Conj(σ,t) = (σ,-t)` (conjugacao). Ambos sao involucoes e comutam entre
si — gerando um grupo isomorfo a `ℤ/2 × ℤ/2`.

Puro fato algebrico sobre `ℝ × ℝ`; nao decide nada sobre ξ, ζ ou RH.
-/

namespace ATK.SymmetryGroup

/-- Reflexao em torno da linha critica: `(σ,t) ↦ (1-σ,t)`. -/
def Refl (s : ℝ × ℝ) : ℝ × ℝ := (1 - s.1, s.2)

/-- Conjugacao: `(σ,t) ↦ (σ,-t)`. -/
def Conj (s : ℝ × ℝ) : ℝ × ℝ := (s.1, -s.2)

/-- `Refl` e uma involucao. -/
theorem Refl_involutive (s : ℝ × ℝ) : Refl (Refl s) = s := by
  unfold Refl
  simp

/-- `Conj` e uma involucao. -/
theorem Conj_involutive (s : ℝ × ℝ) : Conj (Conj s) = s := by
  unfold Conj
  simp

/-- `Refl` e `Conj` comutam: `Refl ∘ Conj = Conj ∘ Refl`. Junto com as
    duas involucoes acima, geram um grupo isomorfo a `ℤ/2 × ℤ/2`. -/
theorem Refl_comm_Conj (s : ℝ × ℝ) : Refl (Conj s) = Conj (Refl s) := by
  unfold Refl Conj
  simp

/-- A composta `Refl ∘ Conj` tambem e uma involucao — o terceiro elemento
    nao trivial do grupo `ℤ/2 × ℤ/2`. -/
theorem ReflConj_involutive (s : ℝ × ℝ) : Refl (Conj (Refl (Conj s))) = s := by
  unfold Refl Conj
  simp

end ATK.SymmetryGroup

#print axioms ATK.SymmetryGroup.Refl_involutive
#print axioms ATK.SymmetryGroup.Conj_involutive
#print axioms ATK.SymmetryGroup.Refl_comm_Conj
#print axioms ATK.SymmetryGroup.ReflConj_involutive
