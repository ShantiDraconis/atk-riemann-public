import Mathlib

/-!
# ATK — Transport (o que uma reparametrização injetiva realmente preserva)

Formaliza, de forma genérica (não comprometida com hélice, parábola,
hiperboloide ou toro especificamente), os dois fatos elementares por trás
da discussão "podemos transportar o cálculo da zeta para outra geometria":

1. Se `F̃ ∘ Φ = F`, transportar `F` por `Φ` preserva exatamente o lugar dos
   zeros de `F`.
2. O toro periódico, como descrito no texto (`Φ_T(σ+1,t) = Φ_T(σ,t)`), NÃO
   é injetivo em `σ ∈ ℝ`: dou o contraexemplo explícito `(0,t) ≠ (1,t)` com
   mesma imagem, e a consequência concreta de que tal toro identifica
   `σ = 1/2` com `σ = 3/2`.

NÃO avança a Hipótese de Riemann. É a formalização do único conteúdo
matemático real desta parte do texto: mudar de coordenadas não cria nem
destrói zeros, EXCETO quando a mudança de coordenadas não é injetiva —
caso em que a função transportada deixa de estar bem definida sem
informação extra.
-/

namespace ATK.Transport

variable {α β : Type*}

/-- Transportar uma função por `Φ` (via `F̃ ∘ Φ = F`) preserva exatamente
    o lugar dos zeros: `F̃ (Φ s) = z ↔ F s = z`. Em particular, para `z = 0`,
    `F̃ (Φ s) = 0 ↔ F s = 0`. Não exige injetividade de `Φ` — só exige que
    `F̃` tenha sido de fato definida como a extensão de `F` ao longo de `Φ`. -/
theorem zero_at_point_preserved_by_transport
    {F : α → β} {Ftil : β → β} {Φ : α → β}
    (htransport : ∀ s, Ftil (Φ s) = F s) (z : β) (s : α) :
    Ftil (Φ s) = z ↔ F s = z := by
  rw [htransport]

/-- Qualquer `Φ : ℝ × ℝ → γ` que satisfaça a periodicidade
    `Φ (σ + 1, t) = Φ (σ, t)` para todo `σ, t` NÃO é injetiva: `(0, t)` e
    `(1, t)` têm a mesma imagem, mas são pontos distintos do domínio. -/
theorem torus_sigma_periodicity_breaks_injectivity
    {γ : Type*} (Φ : ℝ × ℝ → γ)
    (hper : ∀ σ t : ℝ, Φ (σ + 1, t) = Φ (σ, t)) (t : ℝ) :
    ¬ Function.Injective Φ := by
  intro hinj
  have h01 : Φ (0, t) = Φ (1, t) := by
    have h := hper 0 t
    norm_num at h
    exact h.symm
  have heq : ((0 : ℝ), t) = ((1 : ℝ), t) := hinj h01
  have hne : ((0 : ℝ), t) ≠ ((1 : ℝ), t) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  exact hne heq

/-- Consequência direta: para `s₁ = (1/2, t)` e `s₂ = (3/2, t)` (mesma
    parte imaginária `t`, abscissas diferentes — `s₂` não está na faixa
    `0 < σ < 1` nem é o mesmo número complexo que `s₁`), um toro periódico
    de período 1 em `σ` os identifica geometricamente. Isso NÃO implica
    `η(1/2+it) = η(3/2+it)`; é exatamente a advertência do texto original,
    agora como teorema. -/
theorem torus_identifies_half_and_three_half (t : ℝ)
    {γ : Type*} (Φ : ℝ × ℝ → γ)
    (hper : ∀ σ s : ℝ, Φ (σ + 1, s) = Φ (σ, s)) :
    Φ (3 / 2, t) = Φ (1 / 2, t) := by
  have h := hper (1 / 2) t
  norm_num at h
  exact h

end ATK.Transport

#print axioms ATK.Transport.zero_at_point_preserved_by_transport
#print axioms ATK.Transport.torus_sigma_periodicity_breaks_injectivity
#print axioms ATK.Transport.torus_identifies_half_and_three_half
