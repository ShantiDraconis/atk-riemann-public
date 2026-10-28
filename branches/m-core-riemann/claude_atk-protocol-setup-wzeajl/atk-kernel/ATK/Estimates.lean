import Mathlib

/-!
# ATK — Estimates (reflexao, inversao de Mobius, desigualdade triangular inversa)

Tres fatos elementares que apareceram repetidamente na discussao, cada um
formalizado em sua forma generica — nenhum decide nada sobre ξ, ζ ou RH.

1. `D_R_eq_neg_D`: a reflexao `R(σ,t) = (1-σ, t)` troca o sinal do
   deslocamento `D(σ,t) = σ - 1/2`. Pura algebra de pares reais.
2. `inv_sq_reciprocal`: o comportamento de `f(z)=1/z²` sob `z ↦ 1/w`
   (usado na discussao de "zero no infinito" via projecao de Mobius).
3. `reverse_triangle_bound`: a desigualdade triangular inversa na forma
   exata usada nas tentativas de "L_n > E_n ⇒ |η| > 0" — aqui como fato
   generico sobre numeros reais, sem nenhum aproximante ou erro
   especifico de η/ζ anexado.
-/

namespace ATK.Estimates

/-- Deslocamento horizontal de um ponto `(σ, t)` em relacao a `1/2`. -/
noncomputable def D (s : ℝ × ℝ) : ℝ := s.1 - 1 / 2

/-- Reflexao `R(σ,t) = (1-σ, t)` (correspondendo a `R(s) = 1 - s̄` em `ℂ`,
    em coordenadas). -/
noncomputable def R (s : ℝ × ℝ) : ℝ × ℝ := (1 - s.1, s.2)

/-- A reflexao troca o sinal do deslocamento: `D(R(s)) = -D(s)`. -/
theorem D_R_eq_neg_D (s : ℝ × ℝ) : D (R s) = - D s := by
  unfold D R
  ring

/-- `R` e uma involucao: `R(R(s)) = s`. -/
theorem R_involutive (s : ℝ × ℝ) : R (R s) = s := by
  unfold R
  simp

/-- Comportamento de `f(z) = 1/z²` sob a inversao `z ↦ 1/w` (Mobius),
    para `w ≠ 0`: `1/(1/w)² = w²`. E o fato algebrico por tras de
    "f tem zero de ordem 2 no infinito". -/
theorem inv_sq_reciprocal (w : ℝ) (hw : w ≠ 0) :
    1 / (1 / w) ^ 2 = w ^ 2 := by
  have h1 : (1 / w) ^ 2 = 1 / w ^ 2 := by
    rw [div_pow, one_pow]
  rw [h1, one_div_one_div]

/-- Desigualdade triangular inversa, na forma exata usada nas tentativas
    de certificado `|F| ≥ |P| - |F-P|`: se `|F-P|` e pequeno e `|P|` e
    grande, `|F|` e forcado a ser positivo. Aqui provada como fato
    generico sobre reais — sem nenhum `F`, `P` especifico de η ou ζ. -/
theorem reverse_triangle_bound (F P : ℝ) :
    |P| - |F - P| ≤ |F| := by
  have h : |P| - |F| ≤ |P - F| := abs_sub_abs_le_abs_sub P F
  rw [abs_sub_comm P F] at h
  linarith

/-- Consequencia direta, na forma em que foi usada repetidamente:
    se `L ≤ |P|` e `|F - P| ≤ E` e `L > E`, entao `F ≠ 0`. Se `F` fosse
    zero, `|F-P| = |P| ≥ L`, mas `|F-P| ≤ E < L` — contradicao. -/
theorem nonzero_from_bounds (F P L E : ℝ)
    (hL : L ≤ |P|) (hE : |F - P| ≤ E) (hgt : E < L) : F ≠ 0 := by
  intro hF
  rw [hF] at hE
  simp only [zero_sub, abs_neg] at hE
  linarith

end ATK.Estimates

#print axioms ATK.Estimates.D_R_eq_neg_D
#print axioms ATK.Estimates.R_involutive
#print axioms ATK.Estimates.inv_sq_reciprocal
#print axioms ATK.Estimates.reverse_triangle_bound
#print axioms ATK.Estimates.nonzero_from_bounds
