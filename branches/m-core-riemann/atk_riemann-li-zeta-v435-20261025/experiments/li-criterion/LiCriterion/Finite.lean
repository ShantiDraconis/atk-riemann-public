import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Li's criterion — the finite core

Li (1997): RH ⟺ λₙ ≥ 0 for all n ≥ 1, where λₙ = Σ_ρ [1 − (1 − 1/ρ)ⁿ] over the
non-trivial zeros of ζ. Bombieri–Lagarias (1999) isolated the underlying fact
about multisets of points. This file proves that fact for **finite** families,
in both directions, with no hypotheses beyond `ρ ≠ 1`:

* `norm_liPoint_eq_one_iff` — the Möbius map ρ ↦ ρ/(ρ−1) sends the critical line
  `Re ρ = 1/2` exactly onto the unit circle, and the half-plane `Re ρ ≤ 1/2`
  onto the closed unit disc.
* `li_criterion_finite` — for a finite family:
  `(∀ n, 0 ≤ Re λₙ) ↔ ∀ i, Re ρᵢ ≤ 1/2`.
* `li_criterion_finite_symm` — if the family is closed under ρ ↦ 1 − ρ (the
  symmetry of the zeros of ζ from the functional equation), then
  `(∀ n, 0 ≤ Re λₙ) ↔` every point lies **on** the critical line.
* `liCoeff_eq_li_original` — under that symmetry the coefficients equal Li's
  original form Σ [1 − (1 − 1/ρ)ⁿ].

What this file does NOT do:
* the infinite version (Bombieri–Lagarias Theorem 1, needs a summability
  hypothesis and an analytic argument);
* the fact that the non-trivial zeros of ζ form such a summable multiset
  (Hadamard product / zero counting; known mathematics, not yet in Mathlib);
* RH itself, which remains open. Even with both items above, the criterion is
  an equivalence, not a proof.
-/

namespace LiCriterion

open Filter Topology

/-! ## The Möbius map: critical line ↦ unit circle -/

/-- ρ ↦ ρ / (ρ − 1). -/
noncomputable def liPoint (ρ : ℂ) : ℂ := ρ / (ρ - 1)

theorem normSq_sub_one (ρ : ℂ) :
    Complex.normSq (ρ - 1) = Complex.normSq ρ - 2 * ρ.re + 1 := by
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  ring

theorem norm_le_norm_sub_one_iff (ρ : ℂ) : ‖ρ‖ ≤ ‖ρ - 1‖ ↔ ρ.re ≤ 1 / 2 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_sub_one]
  constructor <;> intro h <;> linarith

theorem norm_sub_one_le_norm_iff (ρ : ℂ) : ‖ρ - 1‖ ≤ ‖ρ‖ ↔ 1 / 2 ≤ ρ.re := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_sub_one]
  constructor <;> intro h <;> linarith

/-- The half-plane `Re ρ ≤ 1/2` is mapped onto the closed unit disc. -/
theorem norm_liPoint_le_one_iff {ρ : ℂ} (h1 : ρ ≠ 1) :
    ‖liPoint ρ‖ ≤ 1 ↔ ρ.re ≤ 1 / 2 := by
  have hpos : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  rw [liPoint, norm_div, div_le_one₀ hpos]
  exact norm_le_norm_sub_one_iff ρ

/-- The critical line `Re ρ = 1/2` is mapped onto the unit circle. -/
theorem norm_liPoint_eq_one_iff {ρ : ℂ} (h1 : ρ ≠ 1) :
    ‖liPoint ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hpos : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  rw [liPoint, norm_div, div_eq_one_iff_eq hpos.ne']
  constructor
  · intro h
    have a := (norm_le_norm_sub_one_iff ρ).mp h.le
    have b := (norm_sub_one_le_norm_iff ρ).mp h.ge
    linarith
  · intro h
    exact le_antisymm ((norm_le_norm_sub_one_iff ρ).mpr h.le)
      ((norm_sub_one_le_norm_iff ρ).mpr h.ge)

theorem one_lt_norm_liPoint_iff {ρ : ℂ} (h1 : ρ ≠ 1) :
    1 < ‖liPoint ρ‖ ↔ 1 / 2 < ρ.re := by
  rw [← not_le, norm_liPoint_le_one_iff h1, not_le]

/-- Li's original term at the reflected point `1 − ρ` is our term at `ρ`. -/
theorem one_sub_inv_one_sub {ρ : ℂ} (h1 : ρ ≠ 1) : 1 - 1 / (1 - ρ) = liPoint ρ := by
  have h : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h' : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [liPoint, eq_div_iff h', sub_mul, one_mul]
  have hm : 1 / (1 - ρ) * (ρ - 1) = -1 := by
    rw [show ρ - 1 = -(1 - ρ) by ring, mul_neg, one_div_mul_cancel h]
  rw [hm]
  ring

/-! ## Li coefficients of a finite family -/

/-- `λₙ = Σᵢ (1 − (ρᵢ/(ρᵢ−1))ⁿ)` for a finite family (a multiset with multiplicity). -/
noncomputable def liCoeff {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i, (1 - liPoint (ρ i) ^ n)

theorem liCoeff_re {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (n : ℕ) :
    (liCoeff ρ n).re = (Fintype.card ι : ℝ) - ∑ i, (liPoint (ρ i) ^ n).re := by
  unfold liCoeff
  rw [Complex.re_sum]
  simp only [Complex.sub_re, Complex.one_re]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Easy direction: points in `Re ρ ≤ 1/2` give `Re λₙ ≥ 0` for every `n`. -/
theorem liCoeff_re_nonneg {ι : Type*} [Fintype ι] {ρ : ι → ℂ} (h1 : ∀ i, ρ i ≠ 1)
    (hre : ∀ i, (ρ i).re ≤ 1 / 2) (n : ℕ) : 0 ≤ (liCoeff ρ n).re := by
  unfold liCoeff
  rw [Complex.re_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hz : ‖liPoint (ρ i)‖ ≤ 1 := (norm_liPoint_le_one_iff (h1 i)).mpr (hre i)
  have hpow : ‖liPoint (ρ i) ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz
  have hre' : (liPoint (ρ i) ^ n).re ≤ 1 := (Complex.re_le_norm _).trans hpow
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-! ## Simultaneous recurrence on the unit circle -/

/-- Finitely many points of the unit circle return simultaneously close to 1,
at arbitrarily large times (compactness of the torus). -/
theorem exists_pow_near_one {κ : Type*} [Fintype κ] (w : κ → ℂ) (hw : ∀ k, ‖w k‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (L : ℕ) : ∃ n, L ≤ n ∧ ∀ k, ‖w k ^ n - 1‖ < ε := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : κ => Metric.closedBall (0 : ℂ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have hu : ∀ m : ℕ, (fun k => w k ^ ((L + 1) * m)) ∈
      Set.pi Set.univ (fun _ : κ => Metric.closedBall (0 : ℂ) 1) := by
    intro m
    rw [Set.mem_univ_pi]
    intro k
    rw [Metric.mem_closedBall, dist_zero_right, norm_pow, hw k, one_pow]
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hu
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq ε hε
  have hd := hN (N + 1) (Nat.le_succ N)
  rw [dist_pi_lt_iff hε] at hd
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨(L + 1) * (φ (N + 1) - φ N), ?_, fun k => ?_⟩
  · have h1 : 1 ≤ φ (N + 1) - φ N := Nat.sub_pos_of_lt hlt
    calc L ≤ (L + 1) * 1 := by omega
      _ ≤ (L + 1) * (φ (N + 1) - φ N) := Nat.mul_le_mul_left _ h1
  · have hk := hd k
    simp only [Function.comp_apply, dist_eq_norm] at hk
    have hsplit : w k ^ ((L + 1) * φ (N + 1)) =
        w k ^ ((L + 1) * φ N) * w k ^ ((L + 1) * (φ (N + 1) - φ N)) := by
      rw [← pow_add, ← Nat.mul_add, Nat.add_sub_of_le hlt.le]
    rw [hsplit, ← mul_sub_one, norm_mul, norm_pow, hw k, one_pow, one_mul] at hk
    exact hk

/-! ## Hard direction: a point right of the line forces some `Re λₙ < 0` -/

theorem exists_liCoeff_re_neg {ι : Type*} [Fintype ι] {ρ : ι → ℂ} (h1 : ∀ i, ρ i ≠ 1)
    (hbad : ∃ i, 1 / 2 < (ρ i).re) : ∃ n, (liCoeff ρ n).re < 0 := by
  classical
  obtain ⟨j, hj⟩ := hbad
  have hj' : 1 < ‖liPoint (ρ j)‖ := (one_lt_norm_liPoint_iff (h1 j)).mpr hj
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => ‖liPoint (ρ i)‖)
    ⟨j, Finset.mem_univ j⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ‖liPoint (ρ i0)‖ := ⟨_, rfl⟩
  have hle : ∀ i, ‖liPoint (ρ i)‖ ≤ M := by
    intro i
    rw [hM]
    exact hi0 i (Finset.mem_univ i)
  have hM1 : 1 < M := lt_of_lt_of_le hj' (hle j)
  have hM0 : 0 < M := by linarith
  have hMne : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM0.ne'
  -- the points of maximal modulus, normalised to the unit circle
  have hw : ∀ k : {i : ι // ‖liPoint (ρ i)‖ = M}, ‖liPoint (ρ k.1) / (M : ℂ)‖ = 1 := by
    intro k
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, k.2, div_self hM0.ne']
  -- the remaining points decay after normalisation
  have hE : Tendsto (fun n : ℕ => ∑ i,
      (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0)) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset ι)
      (f := fun i (n : ℕ) => if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0)
      (a := fun _ => (0 : ℝ)) (x := atTop) (fun i _ => by
        by_cases hlt : ‖liPoint (ρ i)‖ < M
        · simp only [if_pos hlt]
          exact tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (norm_nonneg _) hM0.le)
            ((div_lt_one hM0).mpr hlt)
        · simp only [if_neg hlt]
          exact tendsto_const_nhds)
    simpa using h
  have hC : Tendsto (fun n : ℕ => (Fintype.card ι : ℝ) * (1 / M) ^ n) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / M)
      ((div_lt_one hM0).mpr hM1)).const_mul (Fintype.card ι : ℝ)
    simpa using h
  have hev : ∀ᶠ n in atTop, (Fintype.card ι : ℝ) * (1 / M) ^ n +
      ∑ i, (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0) < 1 / 2 := by
    have h := hC.add hE
    rw [add_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨n, hnL, hnear⟩ := exists_pow_near_one
    (fun k : {i : ι // ‖liPoint (ρ i)‖ = M} => liPoint (ρ k.1) / (M : ℂ)) hw
    (by norm_num : (0 : ℝ) < 1 / 2) L
  have hbound := hL n hnL
  have hMn : 0 < M ^ n := pow_pos hM0 n
  -- maximal points contribute at least Mⁿ/2 each
  have htop : ∀ i, ‖liPoint (ρ i)‖ = M → M ^ n / 2 ≤ (liPoint (ρ i) ^ n).re := by
    intro i heq
    have hk : ‖(liPoint (ρ i) / (M : ℂ)) ^ n - 1‖ < 1 / 2 := hnear ⟨i, heq⟩
    have hre : 1 / 2 ≤ ((liPoint (ρ i) / (M : ℂ)) ^ n).re := by
      have h := Complex.abs_re_le_norm ((liPoint (ρ i) / (M : ℂ)) ^ n - 1)
      rw [Complex.sub_re, Complex.one_re] at h
      have := (abs_le.mp h).1
      linarith
    have hsplit : liPoint (ρ i) ^ n = ((M ^ n : ℝ) : ℂ) * (liPoint (ρ i) / (M : ℂ)) ^ n := by
      rw [Complex.ofReal_pow, div_pow, ← mul_div_assoc,
        mul_div_cancel_left₀ _ (pow_ne_zero n hMne)]
    rw [hsplit, Complex.re_ofReal_mul]
    nlinarith
  -- every point is bounded below
  have hpt : ∀ i, -(M ^ n * (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0))
      ≤ (liPoint (ρ i) ^ n).re := by
    intro i
    by_cases hlt : ‖liPoint (ρ i)‖ < M
    · rw [if_pos hlt]
      have h := Complex.abs_re_le_norm (liPoint (ρ i) ^ n)
      have h2 : ‖liPoint (ρ i) ^ n‖ = M ^ n * (‖liPoint (ρ i)‖ / M) ^ n := by
        rw [norm_pow, div_pow, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero n hM0.ne')]
      rw [h2] at h
      exact (abs_le.mp h).1
    · rw [if_neg hlt, mul_zero, neg_zero]
      have heq : ‖liPoint (ρ i)‖ = M := le_antisymm (hle i) (not_lt.mp hlt)
      have := htop i heq
      linarith
  -- sum: the maximal point i0 dominates
  have hsum_lower : M ^ n / 2 - M ^ n * ∑ i,
      (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0)
      ≤ ∑ i, (liPoint (ρ i) ^ n).re := by
    rw [← Finset.add_sum_erase Finset.univ (fun i => (liPoint (ρ i) ^ n).re)
      (Finset.mem_univ i0)]
    have hA := htop i0 hM.symm
    have hB : ∑ i ∈ Finset.univ.erase i0,
        -(M ^ n * (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0))
        ≤ ∑ i ∈ Finset.univ.erase i0, (liPoint (ρ i) ^ n).re :=
      Finset.sum_le_sum (fun i _ => hpt i)
    have hC' : ∑ i ∈ Finset.univ.erase i0,
        (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0)
        ≤ ∑ i, (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro i _ _
      split_ifs
      · exact pow_nonneg (div_nonneg (norm_nonneg _) hM0.le) n
      · exact le_refl 0
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hB
    have hD := mul_le_mul_of_nonneg_left hC' hMn.le
    linarith
  have hprod : M ^ n * (1 / M) ^ n = 1 := by
    rw [← mul_pow, mul_one_div_cancel hM0.ne', one_pow]
  have hcard : (Fintype.card ι : ℝ) = M ^ n * ((Fintype.card ι : ℝ) * (1 / M) ^ n) := by
    rw [mul_left_comm, hprod, mul_one]
  have hlt2 : M ^ n * ((Fintype.card ι : ℝ) * (1 / M) ^ n) <
      M ^ n / 2 - M ^ n * ∑ i,
        (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0) := by
    have h := mul_lt_mul_of_pos_left
      (show (Fintype.card ι : ℝ) * (1 / M) ^ n < 1 / 2 - ∑ i,
        (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0) by linarith) hMn
    calc _ < M ^ n * (1 / 2 - ∑ i,
          (if ‖liPoint (ρ i)‖ < M then (‖liPoint (ρ i)‖ / M) ^ n else 0)) := h
      _ = _ := by ring
  refine ⟨n, ?_⟩
  rw [liCoeff_re]
  linarith

/-! ## The finite criterion -/

/-- **Finite Li criterion.** For a finite family of points (none equal to 1):
all Li coefficients have non-negative real part iff every point lies in the
half-plane `Re ρ ≤ 1/2`. -/
theorem li_criterion_finite {ι : Type*} [Fintype ι] {ρ : ι → ℂ} (h1 : ∀ i, ρ i ≠ 1) :
    (∀ n, 0 ≤ (liCoeff ρ n).re) ↔ ∀ i, (ρ i).re ≤ 1 / 2 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn⟩ := exists_liCoeff_re_neg h1 hcon
    linarith [h n]
  · intro h n
    exact liCoeff_re_nonneg h1 h n

/-- **Finite Li criterion, symmetric form.** If the family is closed under
`ρ ↦ 1 − ρ` (as the zeros of ζ are, by the functional equation), then all Li
coefficients are non-negative iff every point lies **on** the critical line. -/
theorem li_criterion_finite_symm {ι : Type*} [Fintype ι] {ρ : ι → ℂ} (h1 : ∀ i, ρ i ≠ 1)
    (σ : ι → ι) (hσ : ∀ i, ρ (σ i) = 1 - ρ i) :
    (∀ n, 0 ≤ (liCoeff ρ n).re) ↔ ∀ i, (ρ i).re = 1 / 2 := by
  rw [li_criterion_finite h1]
  constructor
  · intro h i
    have a := h i
    have b := h (σ i)
    rw [hσ i, Complex.sub_re, Complex.one_re] at b
    linarith
  · intro h i
    exact (h i).le

/-- Under the symmetry, our coefficients are Li's original ones. -/
theorem liCoeff_eq_li_original {ι : Type*} [Fintype ι] {ρ : ι → ℂ} (h1 : ∀ i, ρ i ≠ 1)
    (σ : ι ≃ ι) (hσ : ∀ i, ρ (σ i) = 1 - ρ i) (n : ℕ) :
    ∑ i, (1 - (1 - 1 / ρ i) ^ n) = liCoeff ρ n := by
  unfold liCoeff
  rw [← Equiv.sum_comp σ (fun i => 1 - (1 - 1 / ρ i) ^ n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hσ i, one_sub_inv_one_sub (h1 i)]

/-! ## Concrete demonstrations -/

open Complex in
/-- Two points on the critical line: every Li coefficient is ≥ 0. -/
theorem example_on_line (n : ℕ) :
    0 ≤ (liCoeff ![((1 / 2 : ℝ) : ℂ) + I, ((1 / 2 : ℝ) : ℂ) - I] n).re := by
  apply liCoeff_re_nonneg
  · intro i
    fin_cases i <;> norm_num [Complex.ext_iff]
  · intro i
    fin_cases i <;> norm_num

open Complex in
/-- A symmetric pair off the critical line (3/5 + i and 2/5 − i): some Li
coefficient is negative. -/
theorem example_off_line :
    ∃ n, (liCoeff ![((3 / 5 : ℝ) : ℂ) + I, ((2 / 5 : ℝ) : ℂ) - I] n).re < 0 := by
  apply exists_liCoeff_re_neg
  · intro i
    fin_cases i <;> norm_num [Complex.ext_iff]
  · exact ⟨0, by norm_num⟩

end LiCriterion
