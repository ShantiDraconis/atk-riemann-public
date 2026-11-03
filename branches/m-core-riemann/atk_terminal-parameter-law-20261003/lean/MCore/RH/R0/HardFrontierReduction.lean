import MCore.RH.R0.ConcreteGramLogRate
import MCore.RH.R0.CriticalLineWeightedErrorRate
import MCore.RH.R0.ConcreteZeroObstruction

namespace MCore.RH.R0

open MCore.RH.NB

/--
Exact terminal target in the repository's notation.
Note: `DN` is already the squared projection residual, so this theorem does
not square `DN` again.
-/
def HardFrontierTarget : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ N : ℕ,
      concreteNBData.DN concreteGeneratorFamily N ≤
        logMajorant K N

/-- Positive K version of the existing hard frontier. -/
theorem hardFrontierTarget_implies_ConcreteUniformLogDNBound
    (h : HardFrontierTarget) :
    ConcreteUniformLogDNBound := by
  rcases h with ⟨K, hK, hDN⟩
  exact ⟨K, hK.le, hDN⟩

/-- Any genuine quantitative Gram certificate closes the terminal target. -/
theorem hard_frontier_of_ConcreteGramLogRate
    (h : ConcreteGramLogRate) :
    HardFrontierTarget := by
  refine ⟨h.K + 1, by linarith [h.hK], ?_⟩
  intro N
  have hU := h.toUniformLogDNBound
  rcases hU with ⟨K, hK, hDN⟩
  have hlogpos : 0 < Real.log ((N : ℝ) + 2) := by
    exact Real.log_pos (by positivity)
  have hmono :
      logMajorant K N ≤ logMajorant (h.K + 1) N := by
    unfold logMajorant
    have hK_eq : K = h.K := by rfl
    rw [hK_eq]
    exact div_le_div_of_nonneg_right (by linarith) hlogpos.le
  exact (hDN N).trans hmono

/-- Any genuine weighted critical-line L2 error certificate closes the target. -/
theorem hard_frontier_of_CriticalLineWeightedErrorRate
    (h : CriticalLineWeightedErrorRate) :
    HardFrontierTarget :=
  hard_frontier_of_ConcreteGramLogRate
    (uniformLogDNBound_to_ConcreteGramLogRate h.toUniformLogDNBound)

/--
Negative route: a nontrivial concrete orthogonal witness is incompatible with
the terminal target.
-/
theorem no_HardFrontierTarget_of_orthogonal_witness
    (w : concreteNBData.H)
    (hw : w ≠ 0)
    (hchi : inner ℝ concreteNBData.chi w ≠ 0)
    (hgen : ∀ n : ℕ, inner ℝ (concreteGeneratorFamily n) w = 0) :
    ¬ HardFrontierTarget := by
  intro h
  exact
    (no_ConcreteUniformLogDNBound_of_orthogonal_witness w hw hchi hgen)
      (hardFrontierTarget_implies_ConcreteUniformLogDNBound h)

#print axioms MCore.RH.R0.hardFrontierTarget_implies_ConcreteUniformLogDNBound
#print axioms MCore.RH.R0.hard_frontier_of_ConcreteGramLogRate
#print axioms MCore.RH.R0.hard_frontier_of_CriticalLineWeightedErrorRate
#print axioms MCore.RH.R0.no_HardFrontierTarget_of_orthogonal_witness

end MCore.RH.R0
