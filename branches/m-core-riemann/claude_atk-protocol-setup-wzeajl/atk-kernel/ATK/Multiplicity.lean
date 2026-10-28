import Mathlib

/-!
# ATK — Multiplicity (ponte B17 + cancelamento removível)

Formaliza dois pedacos algebricos elementares discutidos:

1. A "ponte B17": multiplicar por um fator `u` nao-nulo num ponto `a`
   preserva, nesse ponto, a equivalencia entre `F a = 0` e `G a = 0`
   quando `G = u · F`; e, se `F` se fatora como `(z-a)^m · h` com
   `h a ≠ 0`, o produto `u · F` se fatora com a MESMA potencia `(z-a)^m`
   e cofator `u · h` ainda nao-nulo em `a`. Pura reescrita algebrica —
   nenhum maquinario de "ordem de zero" do Mathlib e necessario.

2. Um exemplo concreto de cancelamento de singularidade removivel:
   `(x²-1)/(x-1) = x+1` para `x ≠ 1` — a formalizacao exata de
   "0/0 nao e automaticamente zero; fora do ponto problematico, a
   expressao simplifica para um valor finito explicito".

Nenhum destes toca ξ, ζ ou qualquer conjectura do milenio.
-/

namespace ATK.Multiplicity

variable {α : Type*} [Field α]

/-- Se `G = u * F` pontualmente e `u a ≠ 0`, entao `F a = 0 ↔ G a = 0`. -/
theorem zero_iff_of_nonzero_factor
    {F G u : α → α} (a : α)
    (hrel : ∀ z, G z = u z * F z) (hu : u a ≠ 0) :
    F a = 0 ↔ G a = 0 := by
  rw [hrel a]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hu
    · exact h1

/-- Fatoracao preservada: se `F z = (z-a)^m * h z`, entao multiplicar por
    `u` produz exatamente `(z-a)^m * (u z * h z)` — a mesma potencia de
    `(z-a)`, com o cofator multiplicado por `u z`. -/
theorem factor_preserved
    {h u F : α → α} (a : α) (m : ℕ)
    (hfact : ∀ z, F z = (z - a) ^ m * h z) (z : α) :
    u z * F z = (z - a) ^ m * (u z * h z) := by
  rw [hfact z]
  ring

/-- Se o cofator original e nao-nulo em `a` e o fator multiplicador
    tambem, o novo cofator `u·h` continua nao-nulo em `a`. -/
theorem cofactor_nonzero
    {h u : α → α} (a : α) (hh : h a ≠ 0) (hu : u a ≠ 0) :
    u a * h a ≠ 0 :=
  mul_ne_zero hu hh

/-- Cancelamento de singularidade removivel: para `x ≠ 1`,
    `(x²-1)/(x-1) = x+1`. A expressao original e indefinida em `x=1`
    (forma `0/0`); fora desse ponto, ela simplifica para um valor finito
    explicito — exatamente o que distingue uma indeterminacao de um
    valor zero. -/
theorem removable_example (x : ℝ) (hx : x ≠ 1) :
    (x ^ 2 - 1) / (x - 1) = x + 1 := by
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  rw [div_eq_iff hx1]
  ring

end ATK.Multiplicity

#print axioms ATK.Multiplicity.zero_iff_of_nonzero_factor
#print axioms ATK.Multiplicity.factor_preserved
#print axioms ATK.Multiplicity.cofactor_nonzero
#print axioms ATK.Multiplicity.removable_example
