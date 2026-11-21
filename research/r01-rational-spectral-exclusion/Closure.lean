import Mathlib

namespace R01

/-- Store the point; derive the geometry and the zeta value from it. -/
structure PointState where
  point : ℂ

noncomputable def PointState.u (state : PointState) : ℝ :=
  state.point.re - 1 / 2

noncomputable def PointState.v (state : PointState) : ℝ :=
  ‖riemannZeta state.point‖ ^ 2

theorem PointState.u_eq_zero (state : PointState) :
    state.u = 0 ↔ state.point.re = 1 / 2 := by
  unfold PointState.u
  exact sub_eq_zero

theorem PointState.v_eq_zero (state : PointState) :
    state.v = 0 ↔ riemannZeta state.point = 0 := by
  unfold PointState.v
  constructor
  · intro h
    have hn : ‖riemannZeta state.point‖ = 0 := by
      exact (pow_eq_zero h)
    exact norm_eq_zero.mp hn
  · intro h
    simp [h]

/-- Exhaust arbitrary positive bounds using certificates at finite indices. -/
def ArbitrarilySmallUpperCertificates (D : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, D N < ε

/-- The Mellin estimate plus arbitrarily small certificates exclude right-strip zeros. -/
theorem no_right_strip_zeros
    (D : ℕ → ℝ) (lower : ℂ → ℝ)
    (hcert : ArbitrarilySmallUpperCertificates D)
    (hpos : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → 0 < lower s)
    (hmellin : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      riemannZeta s = 0 → ∀ N : ℕ, lower s ≤ D N) :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro s hl hr hz
  obtain ⟨N, hN⟩ := hcert (lower s) (hpos s hl hr)
  exact (not_lt_of_ge (hmellin s hl hr hz N)) hN

/-- Reflection transfers right-strip exclusion to the full open strip. -/
theorem critical_strip_of_right_exclusion
    (hright : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hreflect : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      riemannZeta s = 0 → riemannZeta (1 - s) = 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s h0 h1 hz
  rcases lt_trichotomy s.re (1 / 2 : ℝ) with hl | he | hr
  · have hre : (1 - s).re = 1 - s.re := by simp
    exact False.elim
      (hright (1 - s) (by rw [hre]; linarith) (by rw [hre]; linarith)
        (hreflect s h0 hl hz))
  · exact he
  · exact False.elim (hright s hr h1 hz)

/-- The functional equation reflects a zero in the open critical strip. -/
theorem reflect_strip_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  have hnat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n he
    rw [he] at h0
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn' : (0 : ℝ) < -(n : ℝ) := by simpa using h0
    linarith
  have hone : s ≠ 1 := by
    intro he
    rw [he] at h1
    simp at h1
  rw [riemannZeta_one_sub hnat hone, hz, mul_zero]

/-- Apply the Mellin obstruction and reflection with no separate symmetry premise. -/
theorem strip_of_mellin_certificates
    (D : ℕ → ℝ) (lower : ℂ → ℝ)
    (hcert : ArbitrarilySmallUpperCertificates D)
    (hpos : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → 0 < lower s)
    (hmellin : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      riemannZeta s = 0 → ∀ N : ℕ, lower s ≤ D N) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  apply critical_strip_of_right_exclusion (no_right_strip_zeros D lower hcert hpos hmellin)
  intro s h0 hhalf hz
  exact reflect_strip_zero h0 (by linarith) hz

#print axioms reflect_strip_zero
#print axioms strip_of_mellin_certificates

#print axioms PointState.u_eq_zero
#print axioms PointState.v_eq_zero
#print axioms no_right_strip_zeros
#print axioms critical_strip_of_right_exclusion

end R01
