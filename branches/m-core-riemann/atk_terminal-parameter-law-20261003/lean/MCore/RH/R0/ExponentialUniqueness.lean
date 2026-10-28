import MCore.RH.R0.LinearIndependentReduction
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace MCore.RH.R0

/-- Rational sample point in the Mellin strip used to turn exponentials into a Vandermonde system. -/
noncomputable def mellinSample (N : ℕ) (j : Fin N) : ℝ :=
  ((j.1 + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)

theorem mellinSample_pos {N : ℕ} (j : Fin N) : 0 < mellinSample N j := by
  unfold mellinSample
  positivity

theorem mellinSample_lt_one {N : ℕ} (j : Fin N) : mellinSample N j < 1 := by
  unfold mellinSample
  have hj : j.1 + 1 ≤ N := Nat.succ_le_iff.mpr j.2
  have hNp : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_one hNp]
  exact_mod_cast Nat.lt_succ_of_le hj

/-- Base whose integer powers encode the sampled Mellin factors. -/
noncomputable def vandermondeBase (N : ℕ) (i : Fin N) : ℝ :=
  Real.rpow (((rhoIndex i : ℕ) : ℝ)) (-1 / ((N + 1 : ℕ) : ℝ))

theorem vandermondeBase_pos (N : ℕ) (i : Fin N) :
    0 < vandermondeBase N i := by
  unfold vandermondeBase
  exact Real.rpow_pos_of_pos (rhoIndex_cast_pos i) _

/--
Key algebraic identity: at the rational sample points, the Mellin scale is
an integer power of one fixed base. This is the bridge to an ordinary
Vandermonde matrix.
-/
theorem mellinScale_sample_eq_pow (N : ℕ) (i j : Fin N) :
    mellinScale i (mellinSample N j) =
      (vandermondeBase N i) ^ (j.1 + 1) := by
  unfold mellinScale mellinSample vandermondeBase
  let A : ℝ := ((rhoIndex i : ℕ) : ℝ)
  have hA : 0 ≤ A := (rhoIndex_cast_pos i).le
  have hexp :
      -(((j.1 + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) =
        (-1 / ((N + 1 : ℕ) : ℝ)) * ((j.1 + 1 : ℕ) : ℝ) := by
    field_simp
  change A ^ (-(((j.1 + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ))) =
    (A ^ (-1 / ((N + 1 : ℕ) : ℝ))) ^ (j.1 + 1)
  rw [hexp, Real.rpow_mul hA,
    Real.rpow_natCast]

/-- Distinct concrete indices give distinct Vandermonde bases. -/
theorem vandermondeBase_injective (N : ℕ) :
    Function.Injective (vandermondeBase N) := by
  intro i j h
  unfold vandermondeBase at h
  let e : ℝ := -1 / ((N + 1 : ℕ) : ℝ)
  have hden : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  have he : e < 0 := by
    dsimp [e]
    exact div_neg_of_neg_of_pos (by norm_num) hden
  have hi : 0 < (((rhoIndex i : ℕ) : ℝ)) := rhoIndex_cast_pos i
  have hj : 0 < (((rhoIndex j : ℕ) : ℝ)) := rhoIndex_cast_pos j
  have hji : (((rhoIndex j : ℕ) : ℝ)) ≤ (((rhoIndex i : ℕ) : ℝ)) :=
    (Real.rpow_le_rpow_iff_of_neg hi hj he).mp (by simpa [e] using h.le)
  have hij : (((rhoIndex i : ℕ) : ℝ)) ≤ (((rhoIndex j : ℕ) : ℝ)) :=
    (Real.rpow_le_rpow_iff_of_neg hj hi he).mp (by simpa [e] using h.symm.le)
  have hpow :
      (((rhoIndex i : ℕ) : ℝ)) = (((rhoIndex j : ℕ) : ℝ)) :=
    le_antisymm hij hji
  exact Fin.ext (rhoIndex_cast_injective hpow)

/--
A2 in finite form: values at N rational points produce an invertible
Vandermonde system, so every coefficient vanishes.
-/
theorem concreteMomentUniqueness_vandermonde (N : ℕ) :
    ConcreteMomentUniqueness N := by
  unfold ConcreteMomentUniqueness
  intro c h i
  let q : Fin N → ℝ := vandermondeBase N
  have hsample :
      ∀ j : Fin N,
        ∑ k : Fin N, c k * (q k) ^ (j.1 + 1) = 0 := by
    intro j
    have hj := h (mellinSample N j) (mellinSample_pos j) (mellinSample_lt_one j)
    simpa [concreteMomentPolynomial, q, mellinScale_sample_eq_pow] using hj
  -- Factor one q_k from each column. Since q_k ≠ 0, this reduces to the
  -- standard Vandermonde system with exponents 0..N-1.
  have hq : Function.Injective q := by
    simpa [q] using vandermondeBase_injective N
  have hq0 : ∀ k, q k ≠ 0 := fun k => ne_of_gt (vandermondeBase_pos N k)
  -- Reduce q_k^(j+1) = q_k * q_k^j and use Mathlib's
  -- finite Vandermonde kernel theorem directly.
  have hsystem :
      ∀ j : Fin N,
        ∑ k : Fin N, (c k * q k) * q k ^ (j : ℕ) = 0 := by
    intro j
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hsample j
  have hz : (fun k => c k * q k) = 0 := by
    exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hq hsystem
  have hi := congr_fun hz i
  simp only [Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_right (hq0 i)

#print axioms MCore.RH.R0.concreteMomentUniqueness_vandermonde

end MCore.RH.R0
