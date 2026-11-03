import MCore.RH.R0.HardFrontierReduction
import MCore.RH.R0.ConcreteGramLogRate
import MCore.RH.R0.ExplicitCoefficientLogRate
import MCore.RH.R0.ConcreteZeroObstruction
import MCore.RH.Analytic.MellinConcrete

namespace MCore.RH.R0

open MCore.RH.NB

/--
Fail-closed frontier exposure for the RH lane.

This file contains only definitions and reductions already justified by the
kernel.  It deliberately does NOT manufacture an inhabitant of
`ConcreteUniformLogDNBound`.
-/

/-- Exact material producer required for terminal promotion. -/
abbrev RHMaterialGap : Prop := ConcreteUniformLogDNBound

/-- Equivalent finite-coefficient presentation of the same quantitative gap. -/
abbrev RHCoefficientMaterialGap : Prop :=
  Nonempty ConcreteCoefficientLogRate

/-- Equivalent finite Gram normal-equation presentation of the same gap. -/
abbrev RHGramMaterialGap : Prop :=
  Nonempty ConcreteGramLogRate

theorem coefficient_gap_iff_material_gap :
    RHCoefficientMaterialGap ↔ RHMaterialGap :=
  concreteCoefficientLogRate_iff_uniformLogDNBound

theorem gram_gap_iff_material_gap :
    RHGramMaterialGap ↔ RHMaterialGap :=
  concreteGramLogRate_iff_uniformLogDNBound

/-- Any inhabitant of the material gap reaches the already-closed terminal chain. -/
theorem material_gap_closes_terminal
    (h : RHMaterialGap) :
    RiemannTerminalCertifies :=
  terminal_of_concreteUniformLogDNBound h

/--
A concrete orthogonal witness blocks the material producer.  This is the
negative route used to expose any off-line-zero obstruction once such a
witness is constructed analytically.
-/
theorem orthogonal_witness_blocks_material_gap
    (w : concreteNBData.H)
    (hw : w ≠ 0)
    (hchi : inner ℝ concreteNBData.chi w ≠ 0)
    (hgen : ∀ n : ℕ, inner ℝ (concreteGeneratorFamily n) w = 0) :
    ¬ RHMaterialGap :=
  no_ConcreteUniformLogDNBound_of_orthogonal_witness w hw hchi hgen

#check RHMaterialGap
#check RHCoefficientMaterialGap
#check RHGramMaterialGap
#check material_gap_closes_terminal
#check orthogonal_witness_blocks_material_gap

#print axioms MCore.RH.R0.coefficient_gap_iff_material_gap
#print axioms MCore.RH.R0.gram_gap_iff_material_gap
#print axioms MCore.RH.R0.material_gap_closes_terminal
#print axioms MCore.RH.R0.orthogonal_witness_blocks_material_gap

end MCore.RH.R0
