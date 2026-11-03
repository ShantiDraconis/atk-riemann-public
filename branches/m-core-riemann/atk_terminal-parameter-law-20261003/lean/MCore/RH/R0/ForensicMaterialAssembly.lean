import MCore.RH.Analytic.MellinRhoReduction
import MCore.RH.Analytic.MellinStripConvergence
import MCore.RH.Analytic.MellinTarget
import MCore.RH.R0.CriticalLineWeightedErrorRate
import MCore.RH.R0.ExplicitGramRate
import MCore.RH.R0.ConcreteGramLogRate
import MCore.RH.R0.FinalKernelComposition

namespace MCore.RH.R0

open MCore.RH.NB
open MCore.RH.NB.Final
open Complex

/--
Forensic reconstruction of the concrete Mellin identity for every frozen
Báez--Duarte generator.  The only analytic input is the raw fractional-part
Mellin identity; dilation and all indexing are already kernel-proved.
-/
theorem mellin_rhoRepresentativeC_of_fractionalZeta
    (hfrac : FractionalZetaMellinIdentity)
    (n : ℕ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (rhoRepresentativeC n) s =
      (((rhoIndex n : ℕ) : ℂ) ^ (-s)) * (-riemannZeta s / s) := by
  rw [mellin_rhoRepresentativeC_dilate]
  rw [mellin_rho_base_of_fractionalZeta hfrac s hs0 hs1]

/-- Same identity in the customary single-fraction presentation. -/
theorem mellin_rhoRepresentativeC_zeta_formula
    (hfrac : FractionalZetaMellinIdentity)
    (n : ℕ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (rhoRepresentativeC n) s =
      -((((rhoIndex n : ℕ) : ℂ) ^ (-s)) * riemannZeta s) / s := by
  rw [mellin_rhoRepresentativeC_of_fractionalZeta hfrac n s hs0 hs1]
  ring

/--
A genuine weighted critical-line L2 rate is already sufficient to inhabit
the canonical material producer.
-/
theorem uniformLogDNBound_of_weightedCriticalLineRate
    (h : CriticalLineWeightedErrorRate) :
    ConcreteUniformLogDNBound :=
  h.toUniformLogDNBound

/-- The same weighted error rate closes the full terminal chain mechanically. -/
theorem terminal_of_weightedCriticalLineRate
    (h : CriticalLineWeightedErrorRate) :
    RiemannTerminalCertifies :=
  terminal_of_concreteUniformLogDNBound
    (uniformLogDNBound_of_weightedCriticalLineRate h)

/--
The explicit inverse-Gram rate target is exactly sufficient for the terminal
certificate.  No placeholder DN is involved: ExplicitGramRate already proves
concreteDN_eq_explicitGramResidual.
-/
theorem terminal_of_explicitGramRateTarget
    (h : ExplicitGramRateTarget) :
    RiemannTerminalCertifies :=
  terminal_of_concreteUniformLogDNBound
    (explicitGramRateTarget_iff_uniformLogDNBound.mp h)

/--
Likewise, a concrete Gram normal-equation rate certificate closes the terminal.
-/
theorem terminal_of_concreteGramLogRate
    (h : ConcreteGramLogRate) :
    RiemannTerminalCertifies :=
  terminal_of_concreteUniformLogDNBound h.toUniformLogDNBound

/--
Forensic mincut: either of the two quantitative concrete presentations below
is sufficient to produce the exact material endpoint.
This theorem is an assembler, not an inhabitant generator.
-/
theorem terminal_of_forensic_quantitative_fragment
    (h :
      CriticalLineWeightedErrorRate ∨
      ExplicitGramRateTarget ∨
      Nonempty ConcreteGramLogRate) :
    RiemannTerminalCertifies := by
  rcases h with hw | hg | hgr
  · exact terminal_of_weightedCriticalLineRate hw
  · exact terminal_of_explicitGramRateTarget hg
  · rcases hgr with ⟨gr⟩
    exact terminal_of_concreteGramLogRate gr

#print axioms MCore.RH.R0.mellin_rhoRepresentativeC_of_fractionalZeta
#print axioms MCore.RH.R0.mellin_rhoRepresentativeC_zeta_formula
#print axioms MCore.RH.R0.uniformLogDNBound_of_weightedCriticalLineRate
#print axioms MCore.RH.R0.terminal_of_weightedCriticalLineRate
#print axioms MCore.RH.R0.terminal_of_explicitGramRateTarget
#print axioms MCore.RH.R0.terminal_of_concreteGramLogRate
#print axioms MCore.RH.R0.terminal_of_forensic_quantitative_fragment

end MCore.RH.R0
