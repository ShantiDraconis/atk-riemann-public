import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.RH.NB
namespace Final

abbrev FinalExternalCertificate (D : NBHilbertData) (rho : D.GeneratorFamily) : Prop :=
  D.DNToZero rho

def FINAL_ROOT (D : NBHilbertData) (rho : D.GeneratorFamily) : Prop :=
  D.DNLimit rho = 0

theorem finalExternal_to_FINAL_ROOT
    (D : NBHilbertData) (rho : D.GeneratorFamily)
    (E : FinalExternalCertificate D rho) :
    FINAL_ROOT D rho :=
  (D.DNToZero_iff_DNLimit_eq_zero rho).mp E

theorem FINAL_ROOT_to_finalExternal
    (D : NBHilbertData) (rho : D.GeneratorFamily)
    (h : FINAL_ROOT D rho) :
    FinalExternalCertificate D rho :=
  (D.DNToZero_iff_DNLimit_eq_zero rho).mpr h

theorem finalExternal_iff_FINAL_ROOT
    (D : NBHilbertData) (rho : D.GeneratorFamily) :
    FinalExternalCertificate D rho ↔ FINAL_ROOT D rho :=
  D.DNToZero_iff_DNLimit_eq_zero rho

end Final
end MCore.RH.NB
