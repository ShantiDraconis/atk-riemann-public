import Mathlib
import LiCriterion.Finite

/-!
# Li's criterion for the Riemann zeta function, truncated at height `T`

`LiCriterion.Finite` proves Li's criterion for finite families of points. This file applies it to the
actual zeros of `riemannZeta`, using two facts from Mathlib v4.35.0:

* `IsCompact.inter_riemannZetaZeros_finite` (`Mathlib.NumberTheory.LSeries.ZetaZeros`): a compact set
  contains only finitely many zeros of `ζ`; so the zeros in the critical strip with `|Im ρ| ≤ T` form a
  finite set;
* `riemannZeta_one_sub` (the functional equation): that set is closed under `ρ ↦ 1 − ρ`.

For each height `T` define the **truncated Li coefficients**

  `λₙ(T) = Σ_{ρ zero of ζ, 0 < Re ρ < 1, |Im ρ| ≤ T} (1 − (ρ / (ρ − 1))ⁿ)`

(each zero counted once). Main results:

* `liTrunc_criterion` — for every `T`: `(∀ n, 0 ≤ Re λₙ(T)) ↔` every zero up to height `T` lies on the
  critical line;
* `trivial_of_re_nonpos` — the zeros of `ζ` with `Re s ≤ 0` are exactly the trivial ones `−2(n+1)`;
* `riemannHypothesis_iff_liTrunc` — **Mathlib's `RiemannHypothesis` ⟺ `∀ T n, 0 ≤ Re λₙ(T)`**;
* `exists_liTrunc_re_neg_of_not_RH` — a zero off the line forces a negative truncated coefficient at
  some finite height and index;
* `liTrunc_eq_li_original` — `λₙ(T)` equals Li's original form `Σ (1 − (1 − 1/ρ)ⁿ)`;
* `exists_lowest_offline_zero`, `liTrunc_threshold_of_not_RH` — if RH fails, there is a lowest
  off-line zero, and negativity of `λₙ(T)` starts exactly at its height `T₀` (finite);
* `li_two_worlds` — either `∀ T n, 0 ≤ Re λₙ(T)` (RH), or a finite threshold `T₀` as above;
* `hardyZ_im_eq_zero`, `stripZero_of_hardyZ` — zeros on the line ⟷ zeros of Hardy's `Z`
  (`Mathlib.NumberTheory.LSeries.HardyZ`, new in v4.35.0).

This is a reformulation of RH, not a proof of it, and not Li's original criterion: Li's coefficients
sum over all zeros with multiplicity (an infinite sum); here every sum is finite and each zero is
counted once.
-/

namespace LiCriterion.Zeta

open Complex

/-- Zeros of `ζ` in the open critical strip. -/
def StripZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- Strip zeros of height at most `T`. -/
def zerosUpTo (T : ℝ) : Set ℂ :=
  {s | StripZero s ∧ |s.im| ≤ T}

theorem zerosUpTo_subset (T : ℝ) :
    zerosUpTo T ⊆ Metric.closedBall (0 : ℂ) (1 + |T|) ∩ riemannZetaZeros := by
  intro s hs
  refine ⟨?_, mem_riemannZetaZeros.mpr hs.1.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := Complex.norm_le_abs_re_add_abs_im s
  have h2 : |s.re| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1.2.1, hs.1.2.2]
  have h3 : |s.im| ≤ |T| := hs.2.trans (le_abs_self T)
  linarith

/-- Finitely many zeros up to each height (discreteness of the zeros, Mathlib). -/
theorem zerosUpTo_finite (T : ℝ) : (zerosUpTo T).Finite :=
  ((isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite).subset
    (zerosUpTo_subset T)

theorem ne_neg_natCast_of_re_pos {s : ℂ} (h : 0 < s.re) : ∀ n : ℕ, s ≠ -n := by
  intro n hn
  have hre : s.re = -(n : ℝ) := by
    rw [hn, Complex.neg_re, Complex.natCast_re]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem ne_one_of_re_lt_one {s : ℂ} (h : s.re < 1) : s ≠ 1 := by
  intro h1
  have hre : s.re = 1 := by
    rw [h1, Complex.one_re]
  linarith

/-- The functional equation sends strip zeros to strip zeros. -/
theorem stripZero_one_sub {s : ℂ} (hs : StripZero s) : StripZero (1 - s) := by
  obtain ⟨hz, h0, h1⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_one_sub (ne_neg_natCast_of_re_pos h0) (ne_one_of_re_lt_one h1), hz, mul_zero]
  · rw [Complex.sub_re, Complex.one_re]
    linarith
  · rw [Complex.sub_re, Complex.one_re]
    linarith

theorem one_sub_mem_zerosUpTo {T : ℝ} {s : ℂ} (hs : s ∈ zerosUpTo T) :
    1 - s ∈ zerosUpTo T := by
  refine ⟨stripZero_one_sub hs.1, ?_⟩
  rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  exact hs.2

/-- The zeros up to height `T`, as a finite set. -/
noncomputable def zerosFinset (T : ℝ) : Finset ℂ :=
  (zerosUpTo_finite T).toFinset

theorem mem_zerosFinset {T : ℝ} {s : ℂ} : s ∈ zerosFinset T ↔ s ∈ zerosUpTo T :=
  Set.Finite.mem_toFinset _

/-- **Truncated Li coefficients**: `λₙ(T) = Σ_{ρ ∈ zeros up to T} (1 − (ρ/(ρ−1))ⁿ)`. -/
noncomputable def liTrunc (T : ℝ) (n : ℕ) : ℂ :=
  ∑ ρ ∈ zerosFinset T, (1 - liPoint ρ ^ n)

theorem liTrunc_eq_liCoeff (T : ℝ) (n : ℕ) :
    liTrunc T n = liCoeff (fun ρ : zerosFinset T => (ρ : ℂ)) n := by
  unfold liTrunc liCoeff
  exact (Finset.sum_coe_sort (zerosFinset T) (fun ρ => 1 - liPoint ρ ^ n)).symm

theorem ne_one_of_mem_zerosFinset {T : ℝ} (ρ : zerosFinset T) : (ρ : ℂ) ≠ 1 :=
  ne_one_of_re_lt_one (mem_zerosFinset.mp ρ.2).1.2.2

/-- The reflection `ρ ↦ 1 − ρ` on the zeros up to height `T`. -/
noncomputable def reflect (T : ℝ) (ρ : zerosFinset T) : zerosFinset T :=
  ⟨1 - (ρ : ℂ), mem_zerosFinset.mpr (one_sub_mem_zerosUpTo (mem_zerosFinset.mp ρ.2))⟩

theorem reflect_coe (T : ℝ) (ρ : zerosFinset T) : ((reflect T ρ : zerosFinset T) : ℂ) = 1 - ρ :=
  rfl

theorem reflect_involutive (T : ℝ) : Function.Involutive (reflect T) := by
  intro ρ
  apply Subtype.ext
  rw [reflect_coe, reflect_coe, sub_sub_cancel]

/-- **Truncated Li criterion at height `T`.** -/
theorem liTrunc_criterion (T : ℝ) :
    (∀ n, 0 ≤ (liTrunc T n).re) ↔ ∀ s ∈ zerosUpTo T, s.re = 1 / 2 := by
  have key := li_criterion_finite_symm (ρ := fun x : zerosFinset T => (x : ℂ))
    (ne_one_of_mem_zerosFinset (T := T)) (reflect T) (reflect_coe T)
  constructor
  · intro h s hs
    have h' : ∀ n, 0 ≤ (liCoeff (fun x : zerosFinset T => (x : ℂ)) n).re := by
      intro n
      rw [← liTrunc_eq_liCoeff]
      exact h n
    exact key.mp h' ⟨s, mem_zerosFinset.mpr hs⟩
  · intro h n
    rw [liTrunc_eq_liCoeff]
    exact key.mpr (fun ρ => h ρ (mem_zerosFinset.mp ρ.2)) n

/-- RH stated for the open critical strip. -/
def StripRH : Prop :=
  ∀ s, StripZero s → s.re = 1 / 2

theorem stripRH_iff_liTrunc : StripRH ↔ ∀ T : ℝ, ∀ n : ℕ, 0 ≤ (liTrunc T n).re := by
  constructor
  · intro h T
    refine (liTrunc_criterion T).mpr ?_
    intro s hs
    exact h s hs.1
  · intro h s hs
    exact (liTrunc_criterion |s.im|).mp (h |s.im|) s ⟨hs, le_refl _⟩

/-- The zeros of `ζ` with `Re s ≤ 0` are the trivial zeros `−2(n+1)`. -/
theorem trivial_of_re_nonpos {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hz
    norm_num at hz
  have hu_re : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hun : ∀ n : ℕ, (1 - s) ≠ -n := ne_neg_natCast_of_re_pos (by linarith)
  have hu1 : (1 - s) ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hfe := riemannZeta_one_sub hun hu1
  rw [sub_sub_cancel, hz] at hfe
  have hzu : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hu_re
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hun
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero two_ne_zero hpi h.1
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = 0 := by
    by_contra hc
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hG) hc) hzu)
      hfe.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hmul : (Real.pi : ℂ) * (1 - s) = (Real.pi : ℂ) * (2 * k + 1) := by
    linear_combination 2 * hk
  have hu : 1 - s = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hpi hmul
  have hs_eq : s = -2 * (k : ℂ) := by
    linear_combination -hu
  have hre_eq : s.re = -2 * (k : ℝ) := by
    rw [hs_eq, Complex.mul_re]
    simp
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hk0' : (0 : ℤ) ≤ k := by exact_mod_cast hk0
  have hkne : k ≠ 0 := by
    rintro rfl
    apply hs0
    rw [hs_eq]
    simp
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k - 1 by omega)
  refine ⟨m, ?_⟩
  have hkm : (k : ℂ) = (m : ℂ) + 1 := by
    have h := congrArg (fun z : ℤ => (z : ℂ)) hm
    push_cast at h
    linear_combination h
  rw [hs_eq, hkm]

/-- Mathlib's `RiemannHypothesis` is RH on the open strip. -/
theorem riemannHypothesis_iff_stripRH : RiemannHypothesis ↔ StripRH := by
  constructor
  · intro h s hs
    refine h s hs.1 ?_ (ne_one_of_re_lt_one hs.2.2)
    rintro ⟨n, hn⟩
    have h0 := hs.2.1
    have hre : s.re = -2 * ((n : ℝ) + 1) := by
      rw [hn, Complex.mul_re]
      simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h s hz htriv hs1
    apply h s
    refine ⟨hz, ?_, ?_⟩
    · by_contra hle
      push_neg at hle
      exact htriv (trivial_of_re_nonpos hz hle)
    · by_contra hge
      push_neg at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hz

/-- **RH ⟺ every truncated Li coefficient has non-negative real part.** -/
theorem riemannHypothesis_iff_liTrunc :
    RiemannHypothesis ↔ ∀ T : ℝ, ∀ n : ℕ, 0 ≤ (liTrunc T n).re :=
  riemannHypothesis_iff_stripRH.trans stripRH_iff_liTrunc

/-- If RH fails, a negative truncated Li coefficient appears at a finite height and index. -/
theorem exists_liTrunc_re_neg_of_not_RH (h : ¬ RiemannHypothesis) :
    ∃ T : ℝ, ∃ n : ℕ, (liTrunc T n).re < 0 := by
  rw [riemannHypothesis_iff_liTrunc] at h
  push_neg at h
  exact h

/-- The truncated coefficients equal Li's original form `Σ (1 − (1 − 1/ρ)ⁿ)`. -/
theorem liTrunc_eq_li_original (T : ℝ) (n : ℕ) :
    ∑ ρ ∈ zerosFinset T, (1 - (1 - 1 / ρ) ^ n) = liTrunc T n := by
  rw [liTrunc_eq_liCoeff, ← Finset.sum_coe_sort (zerosFinset T)]
  exact liCoeff_eq_li_original (ρ := fun x : zerosFinset T => (x : ℂ))
    (ne_one_of_mem_zerosFinset (T := T))
    (Function.Involutive.toPerm (reflect T) (reflect_involutive T)) (fun ρ => rfl) n

/-! ## The first off-line zero, and the two worlds -/

/-- If RH fails on the strip, there is a lowest off-line zero: below its height every strip zero
lies on the critical line. -/
theorem exists_lowest_offline_zero (h : ¬ StripRH) :
    ∃ ρ, StripZero ρ ∧ ρ.re ≠ 1 / 2 ∧ ∀ s, StripZero s → |s.im| < |ρ.im| → s.re = 1 / 2 := by
  classical
  unfold StripRH at h
  push_neg at h
  obtain ⟨s0, hs0, hne0⟩ := h
  let F : Finset ℂ := (zerosFinset |s0.im|).filter (fun s => s.re ≠ 1 / 2)
  have hF : s0 ∈ F := Finset.mem_filter.mpr ⟨mem_zerosFinset.mpr ⟨hs0, le_refl _⟩, hne0⟩
  obtain ⟨ρ, hρF, hmin⟩ := F.exists_min_image (fun s => |s.im|) ⟨s0, hF⟩
  have hρ := Finset.mem_filter.mp hρF
  have hρz := mem_zerosFinset.mp hρ.1
  refine ⟨ρ, hρz.1, hρ.2, ?_⟩
  intro s hs hlt
  by_contra hsne
  have hsF : s ∈ F := by
    refine Finset.mem_filter.mpr ⟨mem_zerosFinset.mpr ⟨hs, ?_⟩, hsne⟩
    exact (le_of_lt hlt).trans hρz.2
  have hle := hmin s hsF
  linarith

/-- If RH fails, negativity of the truncated Li coefficients starts at a finite threshold height
`T₀` (the height of the lowest off-line zero): below `T₀` every coefficient is non-negative, at
`T₀` some coefficient is negative. -/
theorem liTrunc_threshold_of_not_RH (h : ¬ RiemannHypothesis) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ (∀ T < T₀, ∀ n, 0 ≤ (liTrunc T n).re) ∧ ∃ n, (liTrunc T₀ n).re < 0 := by
  rw [riemannHypothesis_iff_stripRH] at h
  obtain ⟨ρ, hρ, hne, hlow⟩ := exists_lowest_offline_zero h
  refine ⟨|ρ.im|, abs_nonneg _, ?_, ?_⟩
  · intro T hT n
    refine (liTrunc_criterion T).mpr ?_ n
    intro s hs
    exact hlow s hs.1 (lt_of_le_of_lt hs.2 hT)
  · by_contra hcon
    push_neg at hcon
    exact hne ((liTrunc_criterion |ρ.im|).mp hcon ρ ⟨hρ, le_refl _⟩)

/-- **The two worlds as one theorem.** Either every truncated Li coefficient is non-negative at
every height (this is RH), or negativity appears at a finite threshold height `T₀`, below which all
coefficients are non-negative. An off-line zero cannot be pushed "past infinity". -/
theorem li_two_worlds :
    (∀ T : ℝ, ∀ n : ℕ, 0 ≤ (liTrunc T n).re) ∨
      ∃ T₀ : ℝ, 0 ≤ T₀ ∧ (∀ T < T₀, ∀ n, 0 ≤ (liTrunc T n).re) ∧
        ∃ n, (liTrunc T₀ n).re < 0 := by
  by_cases h : RiemannHypothesis
  · exact Or.inl (riemannHypothesis_iff_liTrunc.mp h)
  · exact Or.inr (liTrunc_threshold_of_not_RH h)

/-! ## Link with Hardy's `Z` function (Mathlib v4.35.0) -/

/-- A strip zero on the critical line is a zero of Hardy's `Z` at its height. -/
theorem hardyZ_im_eq_zero {s : ℂ} (hs : StripZero s) (h : s.re = 1 / 2) : hardyZ s.im = 0 := by
  rw [hardyZ_eq_zero_iff]
  have hs' : (1 : ℂ) / 2 + (s.im : ℂ) * I = s := by
    apply Complex.ext <;> simp [h]
  rw [hs']
  exact hs.1

/-- A zero of Hardy's `Z` gives a strip zero on the critical line. -/
theorem stripZero_of_hardyZ {t : ℝ} (h : hardyZ t = 0) :
    StripZero (1 / 2 + (t : ℂ) * I) ∧ ((1 : ℂ) / 2 + (t : ℂ) * I).re = 1 / 2 := by
  have hre : ((1 : ℂ) / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  refine ⟨⟨(hardyZ_eq_zero_iff t).mp h, ?_, ?_⟩, hre⟩
  · rw [hre]; norm_num
  · rw [hre]; norm_num

end LiCriterion.Zeta
