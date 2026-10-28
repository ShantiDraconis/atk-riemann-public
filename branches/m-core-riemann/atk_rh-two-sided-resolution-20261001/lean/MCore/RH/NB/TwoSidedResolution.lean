import MCore.RH.NB.QuantitativeUpperBound
import MCore.RH.R0.RhoConcrete

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
Material negative producer for the DN=0 frontier:
a strictly positive lower barrier valid at every finite stage.
-/
structure PersistentPositiveLowerBound
    (rho : D.GeneratorFamily) where
  eps : ℝ
  eps_pos : 0 < eps
  eps_le : ∀ N : ℕ, eps ≤ D.DN rho N

/--
A persistent positive lower barrier forces the canonical DN limit to be
strictly positive, hence not zero.
-/
theorem DNLimit_pos_of_persistentPositiveLowerBound
    (rho : D.GeneratorFamily)
    (h : PersistentPositiveLowerBound D rho) :
    0 < D.DNLimit rho := by
  have hle : h.eps ≤ D.DNLimit rho := by
    unfold DNLimit
    exact le_ciInf h.eps_le
  exact lt_of_lt_of_le h.eps_pos hle

theorem DNLimit_ne_zero_of_persistentPositiveLowerBound
    (rho : D.GeneratorFamily)
    (h : PersistentPositiveLowerBound D rho) :
    D.DNLimit rho ≠ 0 := by
  have hpos := D.DNLimit_pos_of_persistentPositiveLowerBound rho h
  exact ne_of_gt hpos

/--
Two-sided material resolution state for the exact DN frontier.
The positive route is the already-certified vanishing upper-bound producer.
The negative route is a persistent positive lower-bound producer.
-/
def DNMateriallyResolved (rho : D.GeneratorFamily) : Prop :=
  Nonempty (VanishingUpperBound D rho) ∨
  Nonempty (PersistentPositiveLowerBound D rho)

/-- Either material route closes one side of the exact DN frontier. -/
theorem DNMateriallyResolved_outcome
    (rho : D.GeneratorFamily)
    (h : D.DNMateriallyResolved rho) :
    D.DNLimit rho = 0 ∨ D.DNLimit rho ≠ 0 := by
  rcases h with hp | hn
  · rcases hp with ⟨p⟩
    exact Or.inl (D.DNLimit_eq_zero_of_vanishingUpperBound rho p)
  · rcases hn with ⟨n⟩
    exact Or.inr (D.DNLimit_ne_zero_of_persistentPositiveLowerBound rho n)

/--
If both material routes are inhabited, the model/adapters are inconsistent.
-/
theorem DN_positive_and_negative_routes_contradict
    (rho : D.GeneratorFamily)
    (hp : Nonempty (VanishingUpperBound D rho))
    (hn : Nonempty (PersistentPositiveLowerBound D rho)) :
    False := by
  rcases hp with ⟨p⟩
  rcases hn with ⟨n⟩
  exact (D.DNLimit_ne_zero_of_persistentPositiveLowerBound rho n)
    (D.DNLimit_eq_zero_of_vanishingUpperBound rho p)

end NBHilbertData
end MCore.RH.NB

namespace MCore.RH.R0

open MCore.RH.NB

/-- Concrete positive producer for the canonical Báez-Duarte family. -/
abbrev ConcretePositiveDNProducer :=
  VanishingUpperBound concreteNBData concreteGeneratorFamily

/-- Concrete negative producer for the canonical Báez-Duarte family. -/
abbrev ConcreteNegativeDNProducer :=
  NBHilbertData.PersistentPositiveLowerBound
    concreteNBData concreteGeneratorFamily

def ConcreteDNMateriallyResolved : Prop :=
  Nonempty ConcretePositiveDNProducer ∨
  Nonempty ConcreteNegativeDNProducer

theorem concreteDNMateriallyResolved_outcome
    (h : ConcreteDNMateriallyResolved) :
    concreteNBData.DNLimit concreteGeneratorFamily = 0 ∨
    concreteNBData.DNLimit concreteGeneratorFamily ≠ 0 := by
  exact concreteNBData.DNMateriallyResolved_outcome concreteGeneratorFamily h

theorem concreteDN_both_routes_contradict
    (hp : Nonempty ConcretePositiveDNProducer)
    (hn : Nonempty ConcreteNegativeDNProducer) :
    False := by
  exact concreteNBData.DN_positive_and_negative_routes_contradict
    concreteGeneratorFamily hp hn

#print axioms MCore.RH.NB.NBHilbertData.DNLimit_pos_of_persistentPositiveLowerBound
#print axioms MCore.RH.NB.NBHilbertData.DNMateriallyResolved_outcome
#print axioms MCore.RH.R0.concreteDNMateriallyResolved_outcome

end MCore.RH.R0
