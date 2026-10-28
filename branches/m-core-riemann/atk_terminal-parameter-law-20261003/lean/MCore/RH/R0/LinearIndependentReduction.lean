import MCore.RH.R0.GramExplicit
import MCore.RH.Analytic.MellinConcrete
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open scoped BigOperators

namespace MCore.RH.R0

open MeasureTheory
open MCore.RH.NB

/-- The concrete Mellin scaling parameter attached to generator n. -/
noncomputable def mellinScale (n : ℕ) (s : ℝ) : ℝ :=
  ((rhoIndex n : ℝ) : ℝ) ^ (-s)

/-- Distinct concrete indices give distinct positive dilation parameters. -/
theorem rhoIndex_cast_injective :
    Function.Injective (fun n : ℕ => ((rhoIndex n : ℕ) : ℝ)) := by
  intro m n h
  have hnat : rhoIndex m = rhoIndex n := Nat.cast_inj.mp h
  exact rhoIndex_injective hnat

theorem rhoIndex_cast_pos (n : ℕ) :
    0 < ((rhoIndex n : ℕ) : ℝ) := by
  exact_mod_cast rhoIndex_pos n

/--
Finite coefficient combination in the Hilbert carrier.
This is exactly the expression used by Fintype.linearIndependent_iff.
-/
noncomputable def concreteFiniteCombination
    {N : ℕ} (c : Fin N → ℝ) : concreteNBData.H :=
  ∑ i : Fin N, c i • concreteGeneratorFamily i

/--
Moment-side finite exponential polynomial suggested by Mellin scaling.
No zeta identity is used here.
-/
noncomputable def concreteMomentPolynomial
    {N : ℕ} (c : Fin N → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin N, c i * mellinScale i s

/--
Producer interface for the purely analytic bridge from a zero L2 combination
to vanishing Mellin moment polynomial on the convergence strip.
This proposition is exposed for discovery; no inhabitant is asserted here.
-/
def ConcreteMomentBridge (N : ℕ) : Prop :=
  ∀ c : Fin N → ℝ,
    concreteFiniteCombination c = 0 →
      ∀ s : ℝ, 0 < s → s < 1 →
        concreteMomentPolynomial c s = 0

/--
Producer interface for uniqueness of the finite exponential polynomial
with the concrete distinct positive bases n+1.
This is real analysis/algebra and does not mention RH.
-/
def ConcreteMomentUniqueness (N : ℕ) : Prop :=
  ∀ c : Fin N → ℝ,
    (∀ s : ℝ, 0 < s → s < 1 →
      concreteMomentPolynomial c s = 0) →
    ∀ i : Fin N, c i = 0

/--
Once the Mellin bridge and finite exponential uniqueness are available,
finite linear independence of the concrete generators is automatic.
-/
theorem concreteGeneratorFamily_linearIndependent_of_moments
    (N : ℕ)
    (hBridge : ConcreteMomentBridge N)
    (hUnique : ConcreteMomentUniqueness N) :
    LinearIndependent ℝ (fun i : Fin N => concreteGeneratorFamily i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  exact hUnique c (hBridge c (by simpa [concreteFiniteCombination] using hc))

/-- Consequently the finite concrete Gram matrix is positive definite. -/
theorem concreteGramMatrix_posDef_of_moments
    (N : ℕ)
    (hBridge : ConcreteMomentBridge N)
    (hUnique : ConcreteMomentUniqueness N) :
    (concreteGramMatrix N).PosDef := by
  rw [concreteGramMatrix_posDef_iff_linearIndependent]
  exact concreteGeneratorFamily_linearIndependent_of_moments N hBridge hUnique

#print axioms MCore.RH.R0.rhoIndex_cast_injective
#print axioms MCore.RH.R0.concreteGeneratorFamily_linearIndependent_of_moments
#print axioms MCore.RH.R0.concreteGramMatrix_posDef_of_moments

end MCore.RH.R0
