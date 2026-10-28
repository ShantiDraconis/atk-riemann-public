import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.OpenMath.RH

open MCore.RH.NB

def FirstRealOpenMath
    (D : NBHilbertData) (rho : D.GeneratorFamily) : Prop :=
  D.FiniteSpanApproximatesChi rho

theorem close_DNToZero_from_first_real_open_math
    (D : NBHilbertData) (rho : D.GeneratorFamily)
    (h : FirstRealOpenMath D rho) :
    D.DNToZero rho :=
  D.DNToZero_of_finiteSpanApproximatesChi rho h

#print axioms MCore.OpenMath.RH.close_DNToZero_from_first_real_open_math

end MCore.OpenMath.RH
