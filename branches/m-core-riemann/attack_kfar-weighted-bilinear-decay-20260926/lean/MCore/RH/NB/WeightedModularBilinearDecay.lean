import MCore.RH.NB.QuantitativeUpperBound

namespace MCore.RH.NB

/--
Fail-closed interface for the unique remaining material producer.

The concrete arithmetic layer must instantiate `S` with the frozen FAR
bilinear form.  This file deliberately provides no inhabitant.
-/
structure WeightedModularBilinearDecayData where
  S : ℕ → ℝ
  N₀ : ℕ

/-- Exact material obligation: a vanishing uniform envelope for the FAR term. -/
def KFarVanishes (D : WeightedModularBilinearDecayData) : Prop :=
  ∃ eps : ℕ → ℝ,
    (∀ N, 0 ≤ eps N) ∧
    Filter.Tendsto eps Filter.atTop (nhds 0) ∧
    ∀ N, D.N₀ ≤ N → |D.S N| ≤ eps N

/--
The transport layer consumes exactly one real proof of `KFarVanishes`.
No constructor is provided in this module.
-/
structure ArithmeticTransformData (D : WeightedModularBilinearDecayData) where
  kfar_vanishes : KFarVanishes D

theorem kfar_vanishes_of_data
    {D : WeightedModularBilinearDecayData}
    (h : ArithmeticTransformData D) :
    KFarVanishes D :=
  h.kfar_vanishes

def farBoundStatus : String :=
  "OPEN_MATH_CORE: WEIGHTED_MODULAR_BILINEAR_DECAY"

def arithmeticTransformStatus : String :=
  "NO_INHABITANT: prove kfar_vanishes"

#print axioms kfar_vanishes_of_data

end MCore.RH.NB
