import MCore.RH.NB.BCFThreeTermMaterializer
import MCore.RH.NB.LogMajorantFinalProducer

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/--
Primitive quantitative law for a three-term BCF decomposition.

No endpoint-equivalent proposition is accepted as an argument.
The only inputs are explicit nonnegative constants and pointwise inequalities
for the three concrete error terms.
-/
structure BCFExplicitLogBounds
    {rho : D.GeneratorFamily}
    (B : BCFThreeTermMajorant D rho) where
  A : ℝ
  Z : ℝ
  F : ℝ

  hA : 0 ≤ A
  hZ : 0 ≤ Z
  hF : 0 ≤ F

  logarithmicDerivative_le :
    ∀ N,
      B.logarithmicDerivative N ≤
        A / Real.log ((N : ℝ) + 2)

  zeroResidue_le :
    ∀ N,
      B.zeroResidue N ≤
        Z / Real.log ((N : ℝ) + 2)

  entireRemainder_le :
    ∀ N,
      B.entireRemainder N ≤
        F / Real.log ((N : ℝ) + 2)

def BCFExplicitLogBounds.K
    {rho : D.GeneratorFamily}
    {B : BCFThreeTermMajorant D rho}
    (H : BCFExplicitLogBounds D B) : ℝ :=
  H.A + H.Z + H.F

theorem BCFExplicitLogBounds.K_nonneg
    {rho : D.GeneratorFamily}
    {B : BCFThreeTermMajorant D rho}
    (H : BCFExplicitLogBounds D B) :
    0 ≤ H.K := by
  unfold BCFExplicitLogBounds.K
  positivity

/--
If the three concrete BCF terms are bounded by A/log, Z/log and F/log,
then DN is bounded by (A+Z+F)/log.
-/
theorem dn_le_combined_log_majorant
    {rho : D.GeneratorFamily}
    {B : BCFThreeTermMajorant D rho}
    (H : BCFExplicitLogBounds D B)
    (N : ℕ) :
    D.DN rho N ≤
      H.K / Real.log ((N : ℝ) + 2) := by
  have hden : 0 ≤ Real.log ((N : ℝ) + 2) := by
    apply Real.log_nonneg
    have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith
  have h1 := H.logarithmicDerivative_le N
  have h2 := H.zeroResidue_le N
  have h3 := H.entireRemainder_le N
  have hdn := B.dn_le N
  calc
    D.DN rho N
        ≤ B.logarithmicDerivative N +
            B.zeroResidue N +
            B.entireRemainder N := hdn
    _ ≤ H.A / Real.log ((N : ℝ) + 2) +
          H.Z / Real.log ((N : ℝ) + 2) +
          H.F / Real.log ((N : ℝ) + 2) := by
          gcongr
    _ = (H.A + H.Z + H.F) / Real.log ((N : ℝ) + 2) := by
          ring
    _ = H.K / Real.log ((N : ℝ) + 2) := rfl

/--
The explicit three-term inequalities directly instantiate the canonical
logarithmic majorant certificate.
-/
def logMajorantCertificate_of_explicit_bcf_bounds
    {rho : D.GeneratorFamily}
    {B : BCFThreeTermMajorant D rho}
    (H : BCFExplicitLogBounds D B) :
    LogMajorantCertificate D rho where
  K := H.K
  hK := H.K_nonneg
  dn_le := by
    intro N
    exact dn_le_combined_log_majorant D H N

/--
Consequently the final root follows from concrete inequalities only.
No OpenMath proposition or endpoint-equivalent hypothesis occurs here.
-/
theorem FINAL_ROOT_of_explicit_bcf_bounds
    {rho : D.GeneratorFamily}
    {B : BCFThreeTermMajorant D rho}
    (H : BCFExplicitLogBounds D B) :
    Final.FINAL_ROOT D rho :=
  Final.FINAL_ROOT_of_logMajorant D rho
    (logMajorantCertificate_of_explicit_bcf_bounds D H)

#print axioms MCore.RH.NB.NBHilbertData.dn_le_combined_log_majorant
#print axioms MCore.RH.NB.NBHilbertData.logMajorantCertificate_of_explicit_bcf_bounds
#print axioms MCore.RH.NB.NBHilbertData.FINAL_ROOT_of_explicit_bcf_bounds

end NBHilbertData
end MCore.RH.NB
