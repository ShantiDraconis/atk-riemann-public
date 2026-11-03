import MCore.RH.NB.QuantitativeUpperBound

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
Quantitative three-term decomposition of the concrete DN error.

This theorem layer does not assert the external BCF identity.  Instead it
records exactly the inequality that a future formalization of that identity
must prove after passing to the repository's Hilbert norm.

The three nonnegative terms correspond to:
* logarithmicDerivative;
* zeroResidue;
* entireRemainder.

Only zeroResidue is intended to remain mathematically open in the BCF route.
-/
structure BCFThreeTermMajorant (rho : D.GeneratorFamily) where
  logarithmicDerivative : ℕ → ℝ
  zeroResidue : ℕ → ℝ
  entireRemainder : ℕ → ℝ

  logarithmicDerivative_nonneg :
    ∀ N, 0 ≤ logarithmicDerivative N
  zeroResidue_nonneg :
    ∀ N, 0 ≤ zeroResidue N
  entireRemainder_nonneg :
    ∀ N, 0 ≤ entireRemainder N

  dn_le :
    ∀ N,
      D.DN rho N ≤
        logarithmicDerivative N +
        zeroResidue N +
        entireRemainder N

  logarithmicDerivative_tendsto_zero :
    Filter.Tendsto logarithmicDerivative Filter.atTop (nhds 0)

  entireRemainder_tendsto_zero :
    Filter.Tendsto entireRemainder Filter.atTop (nhds 0)

/--
The sole additional analytic input needed by the three-term decomposition is
vanishing of the zero-residue contribution.
-/
def ZeroResidueVanishing
    {rho : D.GeneratorFamily}
    (B : BCFThreeTermMajorant D rho) : Prop :=
  Filter.Tendsto B.zeroResidue Filter.atTop (nhds 0)

/--
A certified three-term BCF majorant plus unconditional zero-residue vanishing
constructs the exact VanishingUpperBound used by the canonical RH pipeline.
-/
def vanishingUpperBound_of_bcfThreeTerm
    {rho : D.GeneratorFamily}
    (B : BCFThreeTermMajorant D rho)
    (hzero : D.ZeroResidueVanishing B) :
    D.VanishingUpperBound rho where
  eps := fun N =>
    B.logarithmicDerivative N +
    B.zeroResidue N +
    B.entireRemainder N
  eps_nonneg := by
    intro N
    positivity
  dn_le := B.dn_le
  eps_tendsto_zero := by
    have hsum₁ :
        Filter.Tendsto
          (fun N =>
            B.logarithmicDerivative N + B.zeroResidue N)
          Filter.atTop
          (nhds (0 + 0)) :=
      B.logarithmicDerivative_tendsto_zero.add hzero
    have hsum₂ :
        Filter.Tendsto
          (fun N =>
            (B.logarithmicDerivative N + B.zeroResidue N) +
              B.entireRemainder N)
          Filter.atTop
          (nhds ((0 + 0) + 0)) :=
      hsum₁.add B.entireRemainder_tendsto_zero
    simpa using hsum₂

/--
The BCF route therefore closes DN->0 once the zero-residue term is proved to
vanish in the same quantitative Hilbert norm.
-/
theorem DNToZero_of_bcfThreeTerm
    {rho : D.GeneratorFamily}
    (B : BCFThreeTermMajorant D rho)
    (hzero : D.ZeroResidueVanishing B) :
    D.DNToZero rho :=
  D.DNToZero_of_vanishingUpperBound rho
    (D.vanishingUpperBound_of_bcfThreeTerm B hzero)

/--
Equivalent DNLimit=0 closing theorem for the same material inputs.
-/
theorem DNLimit_eq_zero_of_bcfThreeTerm
    {rho : D.GeneratorFamily}
    (B : BCFThreeTermMajorant D rho)
    (hzero : D.ZeroResidueVanishing B) :
    D.DNLimit rho = 0 :=
  D.DNLimit_eq_zero_of_vanishingUpperBound rho
    (D.vanishingUpperBound_of_bcfThreeTerm B hzero)

/--
If the two closed terms have already been certified, the only live field in
this route is ZeroResidueVanishing.  No converse is asserted: the BCF route is
a sufficient strategy, not a new endpoint equivalence.
-/
theorem bcf_three_term_materializer
    {rho : D.GeneratorFamily}
    (B : BCFThreeTermMajorant D rho) :
    D.ZeroResidueVanishing B →
      D.DNLimit rho = 0 :=
  fun hzero => D.DNLimit_eq_zero_of_bcfThreeTerm B hzero

#print axioms MCore.RH.NB.NBHilbertData.vanishingUpperBound_of_bcfThreeTerm
#print axioms MCore.RH.NB.NBHilbertData.DNToZero_of_bcfThreeTerm
#print axioms MCore.RH.NB.NBHilbertData.DNLimit_eq_zero_of_bcfThreeTerm
#print axioms MCore.RH.NB.NBHilbertData.bcf_three_term_materializer

end NBHilbertData
end MCore.RH.NB
