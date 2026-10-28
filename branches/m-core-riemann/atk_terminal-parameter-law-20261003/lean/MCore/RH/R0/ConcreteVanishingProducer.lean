import MCore.RH.NB.ExactFinalProducer
import MCore.RH.R0.ConcreteGramClosure
import MCore.RH.R0.TerminalLaw

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final

/--
Concrete specialization of the already-frozen quantitative producer.
An inhabitant of this type is exactly the missing material RH producer:
a nonnegative majorant for the concrete DN sequence which dominates DN
pointwise and tends to zero.

No axiom, oracle, endpoint assumption, or equivalent RH proposition is
inserted here.
-/
abbrev ConcreteVanishingUpperBound : Type :=
  concreteNBData.VanishingUpperBound concreteGeneratorFamily

/-- The concrete quantitative inhabitant closes the kernel-level final root. -/
theorem concreteVanishingUpperBound_to_FINAL_ROOT
    (h : ConcreteVanishingUpperBound) :
    FINAL_ROOT concreteNBData concreteGeneratorFamily :=
  MCore.RH.NB.Final.finalRoot_of_vanishingUpperBound
    concreteNBData concreteGeneratorFamily h

/-- Reuse the certified Gram equivalence; no additional mathematical bridge. -/
theorem concreteVanishingUpperBound_to_ConcreteGramResidual
    (h : ConcreteVanishingUpperBound) :
    ConcreteGramResidual :=
  FINAL_ROOT_to_concreteGramResidual
    (concreteVanishingUpperBound_to_FINAL_ROOT h)

/-- Reuse the frozen finite-span equivalence. -/
theorem concreteVanishingUpperBound_to_FiniteSpanApproximatesChi
    (h : ConcreteVanishingUpperBound) :
    concreteNBData.FiniteSpanApproximatesChi concreteGeneratorFamily := by
  exact concreteGramResidual_iff_finiteSpanApproximatesChi.mp
    (concreteVanishingUpperBound_to_ConcreteGramResidual h)

/-- Terminal-law consumer.  This is the exact endpoint used by the central law. -/
theorem concreteVanishingUpperBound_to_RiemannTerminalCertifies
    (h : ConcreteVanishingUpperBound) :
    RiemannTerminalCertifies :=
  concreteGramResidual_certifies_terminal
    (concreteVanishingUpperBound_to_ConcreteGramResidual h)

/--
Exact decomposition of the only missing inhabitant.  This theorem is useful
for producer-first work: constructing the concrete inhabitant means providing
exactly eps, nonnegativity, DN domination, and eps -> 0.
-/
theorem concreteVanishingUpperBound_iff_exists_majorant :
    Nonempty ConcreteVanishingUpperBound ↔
      ∃ eps : ℕ → ℝ,
        (∀ N, 0 ≤ eps N) ∧
        (∀ N, concreteNBData.DN concreteGeneratorFamily N ≤ eps N) ∧
        Filter.Tendsto eps Filter.atTop (nhds 0) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.eps, h.eps_nonneg, h.dn_le, h.eps_tendsto_zero⟩
  · rintro ⟨eps, hnonneg, hdn, htendsto⟩
    exact ⟨{
      eps := eps
      eps_nonneg := hnonneg
      dn_le := hdn
      eps_tendsto_zero := htendsto
    }⟩

#print axioms MCore.RH.R0.concreteVanishingUpperBound_to_FINAL_ROOT
#print axioms MCore.RH.R0.concreteVanishingUpperBound_to_ConcreteGramResidual
#print axioms MCore.RH.R0.concreteVanishingUpperBound_to_FiniteSpanApproximatesChi
#print axioms MCore.RH.R0.concreteVanishingUpperBound_to_RiemannTerminalCertifies
#print axioms MCore.RH.R0.concreteVanishingUpperBound_iff_exists_majorant

end MCore.RH.R0
