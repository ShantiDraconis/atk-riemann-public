import MCore.RH.NB.QuantitativeUpperBound

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
Fail-closed interface for the next concrete R2 attack.

The literature audit isolates an unconditional BCF decomposition, but the
scientific blocker is the unconditional control of the zero-residue term.
This structure records only the exact consequence needed by the already
certified quantitative terminal producer: a pointwise upper bound sequence
for DN together with its vanishing limit.

No theorem below constructs such control.
-/
structure BCFZeroResidueControl (rho : D.GeneratorFamily) where
  eps : ℕ → ℝ
  eps_nonneg : ∀ N, 0 ≤ eps N
  dn_le_from_bcf : ∀ N, D.DN rho N ≤ eps N
  eps_tendsto_zero : Filter.Tendsto eps Filter.atTop (nhds 0)

/-- BCF zero-residue control is sufficient to instantiate the frozen
VanishingUpperBound producer. -/
def BCFZeroResidueControl.toVanishingUpperBound
    {rho : D.GeneratorFamily}
    (h : BCFZeroResidueControl D rho) :
    VanishingUpperBound D rho where
  eps := h.eps
  eps_nonneg := h.eps_nonneg
  dn_le := h.dn_le_from_bcf
  eps_tendsto_zero := h.eps_tendsto_zero

/-- Once the unconditional zero-residue control exists, the already-certified
terminal chain closes DNLimit = 0. -/
theorem DNLimit_eq_zero_of_BCFZeroResidueControl
    (rho : D.GeneratorFamily)
    (h : BCFZeroResidueControl D rho) :
    D.DNLimit rho = 0 :=
  D.DNLimit_eq_zero_of_vanishingUpperBound rho h.toVanishingUpperBound

def bcfTerminalStatus : String :=
  "OPEN_MATH: ZERO_RESIDUE_SUM_UNCONDITIONAL_CONTROL"

#print axioms DNLimit_eq_zero_of_BCFZeroResidueControl

end NBHilbertData
end MCore.RH.NB
