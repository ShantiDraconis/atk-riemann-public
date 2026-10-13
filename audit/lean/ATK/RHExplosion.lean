import Mathlib
import ATK.Exact
import ATK.RHBridge

/-!
# ATK — Linha de explosão para Riemann

Adaptação da linha de explosão do NS (testemunha / refutação / dicotomia):

* **testemunha de explosão** `OffLineZero`: um zero de `ζ` com `Re s > 1/2`. Pela reflexão
  `s ↦ 1 − s` (certificada em `RHBridge.left_zero_reflects`), todo contraexemplo de RH produz uma
  testemunha deste tipo (`explosion_of_not_rh`);
* **refutação** `explosion_refutes : OffLineZero → ¬ RiemannHypothesis`;
* **dicotomia** `rh_iff_no_explosion : RiemannHypothesis ↔ IsEmpty OffLineZero`;
* **localização** `explosion_location`: uma explosão só pode viver na faixa `1/2 < Re s < 1`.

Sentido de "explosão": um zero `ρ` com `Re ρ = β > 1/2` faz o erro dos primos `ψ(x) − x` oscilar
com amplitude da ordem de `x^{β−ε}` (teorema clássico, não formalizado aqui) — a explosão do termo
de erro além de `√x`. Nenhuma testemunha é conhecida; a verificação numérica dos zeros na reta
crítica vai até alturas muito grandes (Platt–Trudgian, 2021: até `3·10¹²`).
-/

noncomputable section

namespace ATK.RHExplosion

/-- Testemunha de explosão: um zero de `ζ` à direita da reta crítica. -/
structure OffLineZero where
  s : ℂ
  zero : riemannZeta s = 0
  right : 1 / 2 < s.re

theorem explosion_refutes (w : OffLineZero) : ¬ RiemannHypothesis :=
  ATK.RHBridge.not_rh_of_zero w.right w.zero

/-- Dicotomia: RH ⇔ não existe explosão. -/
theorem rh_iff_no_explosion : RiemannHypothesis ↔ IsEmpty OffLineZero := by
  constructor
  · intro h
    exact ⟨fun w => explosion_refutes w h⟩
  · intro h
    apply ATK.RHBridge.rh_of_noZerosRightOfHalf
    intro s hs hz
    exact h.1 ⟨s, hz, hs⟩

/-- Todo contraexemplo de RH (inclusive com `Re s < 1/2`) produz uma testemunha normalizada. -/
theorem explosion_of_not_rh (h : ¬ RiemannHypothesis) : Nonempty OffLineZero := by
  rw [rh_iff_no_explosion, not_isEmpty_iff] at h
  exact h

/-- A explosão não pode estar em `Re s ≥ 1` (Mathlib: `riemannZeta_ne_zero_of_one_le_re`). -/
theorem explosion_location (w : OffLineZero) : 1 / 2 < w.s.re ∧ w.s.re < 1 := by
  refine ⟨w.right, ?_⟩
  by_contra h
  push_neg at h
  exact riemannZeta_ne_zero_of_one_le_re h w.zero

end ATK.RHExplosion

end

#print axioms ATK.RHExplosion.explosion_refutes
#print axioms ATK.RHExplosion.rh_iff_no_explosion
#print axioms ATK.RHExplosion.explosion_of_not_rh
#print axioms ATK.RHExplosion.explosion_location
