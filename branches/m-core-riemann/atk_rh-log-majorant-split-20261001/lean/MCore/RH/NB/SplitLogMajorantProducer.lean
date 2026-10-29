import MCore.RH.NB.LogMajorantFinalProducer

namespace MCore.RH.NB
namespace Final

/--
A two-piece quantitative decomposition for the exact logarithmic RH producer.

This does not assume DN -> 0, FiniteSpanApproximatesChi, or the final RH root.
It isolates a concrete analytic route:
  DN(N) <= C1/log(N+2) + residual(N)
  residual(N) <= C2/log(N+2)
with C1,C2 >= 0.
-/
structure SplitLogMajorantCertificate
    (D : NBHilbertData)
    (rho : D.GeneratorFamily) where
  C1 : ℝ
  C2 : ℝ
  hC1 : 0 ≤ C1
  hC2 : 0 ≤ C2
  residual : ℕ → ℝ
  primary :
    ∀ N : ℕ,
      D.DN rho N ≤ logMajorant C1 N + residual N
  residual_le :
    ∀ N : ℕ,
      residual N ≤ logMajorant C2 N

theorem logMajorant_add
    (C1 C2 : ℝ) (N : ℕ) :
    logMajorant (C1 + C2) N =
      logMajorant C1 N + logMajorant C2 N := by
  simp only [logMajorant]
  ring

/--
The split estimate materializes the exact LogMajorantCertificate with
K = C1 + C2.
-/
def SplitLogMajorantCertificate.toLogMajorantCertificate
    {D : NBHilbertData}
    {rho : D.GeneratorFamily}
    (S : SplitLogMajorantCertificate D rho) :
    LogMajorantCertificate D rho where
  K := S.C1 + S.C2
  hK := add_nonneg S.hC1 S.hC2
  dn_le := by
    intro N
    calc
      D.DN rho N
          ≤ logMajorant S.C1 N + S.residual N := S.primary N
      _ ≤ logMajorant S.C1 N + logMajorant S.C2 N := by
          exact add_le_add_left (S.residual_le N) _
      _ = logMajorant (S.C1 + S.C2) N := by
          symm
          exact logMajorant_add S.C1 S.C2 N

theorem FINAL_ROOT_of_splitLogMajorant
    {D : NBHilbertData}
    {rho : D.GeneratorFamily}
    (S : SplitLogMajorantCertificate D rho) :
    FINAL_ROOT D rho :=
  FINAL_ROOT_of_logMajorant D rho S.toLogMajorantCertificate

#print axioms MCore.RH.NB.Final.logMajorant_add
#print axioms MCore.RH.NB.Final.SplitLogMajorantCertificate.toLogMajorantCertificate
#print axioms MCore.RH.NB.Final.FINAL_ROOT_of_splitLogMajorant

end Final
end MCore.RH.NB
