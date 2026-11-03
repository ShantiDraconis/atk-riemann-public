import MCore.RH.NB.ZeroLimitFrontier
import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace MCore.RH.NB
namespace NBHilbertData

variable {D : NBHilbertData}

/-- A vector orthogonal to every generator is orthogonal to every finite span V_N. -/
theorem mem_V_orthogonal_of_forall_generator_inner_eq_zero
    (rho : D.GeneratorFamily) (w : D.H)
    (hgen : ∀ n : ℕ, inner ℝ (rho n) w = 0) (N : ℕ) :
    w ∈ (D.V rho N)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  change v ∈ Submodule.span ℝ (D.finiteGenerators rho N) at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨n, rfl⟩
      exact hgen n
  | zero =>
      simp
  | add x y hx hy =>
      simpa [inner_add_left, hx, hy]
  | smul a x hx =>
      simpa [inner_smul_left, hx]

/--
Orthogonal-witness obstruction, multiplicative form.
If w is orthogonal to every generator, then every finite projection residual
retains the chi-component seen by w. Cauchy--Schwarz therefore gives a
uniform lower bound on DN after multiplication by ||w||^2.
-/
theorem orthogonal_witness_lower_bound_mul
    (rho : D.GeneratorFamily) (w : D.H)
    (hgen : ∀ n : ℕ, inner ℝ (rho n) w = 0) (N : ℕ) :
    |inner ℝ D.chi w| ^ 2 ≤ D.DN rho N * ‖w‖ ^ 2 := by
  have hwV : w ∈ (D.V rho N)ᗮ :=
    D.mem_V_orthogonal_of_forall_generator_inner_eq_zero rho w hgen N
  have hp : inner ℝ (D.P rho N D.chi : D.H) w = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (D.P_mem rho N D.chi) hwV
  have hres :
      inner ℝ (D.chi - (D.P rho N D.chi : D.H)) w =
        inner ℝ D.chi w := by
    rw [inner_sub_left, hp, sub_zero]
  have hcs :
      |inner ℝ (D.chi - (D.P rho N D.chi : D.H)) w| ≤
        ‖D.chi - (D.P rho N D.chi : D.H)‖ * ‖w‖ :=
    abs_real_inner_le_norm _ _
  rw [hres] at hcs
  have hl : 0 ≤ |inner ℝ D.chi w| := abs_nonneg _
  have hr : 0 ≤ D.dN rho N * ‖w‖ :=
    mul_nonneg (D.dN_nonneg rho N) (norm_nonneg w)
  have hsq :
      |inner ℝ D.chi w| ^ 2 ≤ (D.dN rho N * ‖w‖) ^ 2 := by
    nlinarith
  simpa [DN, mul_pow] using hsq

/-- Normalized positive obstruction constant associated to a nonzero witness. -/
noncomputable def orthogonalWitnessDelta
    (w : D.H) : ℝ :=
  |inner ℝ D.chi w| ^ 2 / ‖w‖ ^ 2

theorem orthogonalWitnessDelta_nonneg (w : D.H) :
    0 ≤ D.orthogonalWitnessDelta w := by
  unfold orthogonalWitnessDelta
  positivity

/-- For a nonzero witness, the normalized obstruction is a pointwise lower bound for DN. -/
theorem orthogonalWitnessDelta_le_DN
    (rho : D.GeneratorFamily) (w : D.H)
    (hw : w ≠ 0)
    (hgen : ∀ n : ℕ, inner ℝ (rho n) w = 0) :
    ∀ N : ℕ, D.orthogonalWitnessDelta w ≤ D.DN rho N := by
  intro N
  have hmul := D.orthogonal_witness_lower_bound_mul rho w hgen N
  have hn : 0 < ‖w‖ ^ 2 := by
    positivity
  unfold orthogonalWitnessDelta
  exact (div_le_iff₀ hn).2 (by
    simpa [mul_comm] using hmul)

/-- If chi has nonzero component along the witness, the obstruction is strictly positive. -/
theorem orthogonalWitnessDelta_pos
    (w : D.H) (hw : w ≠ 0)
    (hchi : inner ℝ D.chi w ≠ 0) :
    0 < D.orthogonalWitnessDelta w := by
  unfold orthogonalWitnessDelta
  have hnum : 0 < |inner ℝ D.chi w| ^ 2 := by
    positivity
  have hden : 0 < ‖w‖ ^ 2 := by
    positivity
  exact div_pos hnum hden

#print axioms MCore.RH.NB.NBHilbertData.mem_V_orthogonal_of_forall_generator_inner_eq_zero
#print axioms MCore.RH.NB.NBHilbertData.orthogonal_witness_lower_bound_mul
#print axioms MCore.RH.NB.NBHilbertData.orthogonalWitnessDelta_le_DN
/-- A nontrivial orthogonal witness forbids DN convergence to zero. -/
theorem not_DNToZero_of_orthogonal_witness
    (rho : D.GeneratorFamily) (w : D.H)
    (hw : w ≠ 0)
    (hchi : inner ℝ D.chi w ≠ 0)
    (hgen : ∀ n : ℕ, inner ℝ (rho n) w = 0) :
    ¬ D.DNToZero rho := by
  intro hzero
  have hδpos : 0 < D.orthogonalWitnessDelta w :=
    D.orthogonalWitnessDelta_pos w hw hchi
  have hlt :
      ∀ᶠ N : ℕ in Filter.atTop,
        D.DN rho N < D.orthogonalWitnessDelta w :=
    (tendsto_order.1 hzero).2 _ hδpos
  rcases hlt.exists with ⟨N, hN⟩
  exact (not_lt_of_ge
    (D.orthogonalWitnessDelta_le_DN rho w hw hgen N)) hN

#print axioms MCore.RH.NB.NBHilbertData.orthogonalWitnessDelta_pos
#print axioms MCore.RH.NB.NBHilbertData.not_DNToZero_of_orthogonal_witness

end NBHilbertData
end MCore.RH.NB
