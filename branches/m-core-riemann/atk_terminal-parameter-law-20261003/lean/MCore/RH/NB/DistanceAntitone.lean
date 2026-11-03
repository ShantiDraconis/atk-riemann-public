import MCore.RH.NB.Distance

namespace MCore.RH.NB
namespace NBHilbertData

variable {D : NBHilbertData}

/-- The finite generator sets grow with the truncation index. -/
theorem finiteGenerators_mono (rho : D.GeneratorFamily) :
    Monotone (fun N => D.finiteGenerators rho N) := by
  intro N M hNM x hx
  rcases hx with ⟨k, rfl⟩
  refine ⟨⟨k.1, lt_of_lt_of_le k.2 hNM⟩, ?_⟩
  rfl

/-- Consequently the finite approximation subspaces are nested. -/
theorem V_mono (rho : D.GeneratorFamily) :
    Monotone (fun N => D.V rho N) := by
  intro N M hNM
  exact Submodule.span_mono (finiteGenerators_mono rho hNM)

/-- The best-approximation residual norm is antitone in N. -/
theorem dN_antitone (rho : D.GeneratorFamily) :
    Antitone (fun N => D.dN rho N) := by
  intro N M hNM
  have hV : D.V rho N ≤ D.V rho M := V_mono rho hNM
  have hmem : (D.P rho N D.chi : D.H) ∈ D.V rho M :=
    hV (D.P_mem rho N D.chi)
  have hbdd :
      BddBelow (Set.range (fun v : D.V rho M => ‖D.chi - (v : D.H)‖)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨v, rfl⟩
    exact norm_nonneg _
  calc
    D.dN rho M
        = ‖D.chi - (D.P rho M D.chi : D.H)‖ := rfl
    _ = ⨅ v : D.V rho M, ‖D.chi - (v : D.H)‖ :=
        D.P_minimal rho M D.chi
    _ ≤ ‖D.chi - (⟨(D.P rho N D.chi : D.H), hmem⟩ : D.V rho M)‖ := by
        exact ciInf_le hbdd ⟨(D.P rho N D.chi : D.H), hmem⟩
    _ = D.dN rho N := rfl

/-- The squared finite-stage defect is antitone as well. -/
theorem DN_antitone (rho : D.GeneratorFamily) :
    Antitone (fun N => D.DN rho N) := by
  intro N M hNM
  have hd : D.dN rho M ≤ D.dN rho N := dN_antitone rho hNM
  have hM : 0 ≤ D.dN rho M := D.dN_nonneg rho M
  have hN : 0 ≤ D.dN rho N := D.dN_nonneg rho N
  unfold DN
  nlinarith

#print axioms MCore.RH.NB.NBHilbertData.finiteGenerators_mono
#print axioms MCore.RH.NB.NBHilbertData.V_mono
#print axioms MCore.RH.NB.NBHilbertData.dN_antitone
#print axioms MCore.RH.NB.NBHilbertData.DN_antitone

end NBHilbertData
end MCore.RH.NB
