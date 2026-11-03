import MCore.RH.R0.VasyuninFormulaReduction
import Mathlib.Data.Nat.Factorization.Basic

namespace MCore.RH.R0

/-- Scaling of the explicit autocorrelation Gram entry under a common positive factor. -/
theorem explicitGramEntryNat_mul_common
    (d h k : ℕ) (hd : 0 < d) (hh : 0 < h) (hk : 0 < k) :
    explicitGramEntryNat (d * h) (d * k) =
      (1 / (d : ℝ)) * explicitGramEntryNat h k := by
  unfold explicitGramEntryNat
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hratio :
      (((d * h : ℕ) : ℝ) / ((d * k : ℕ) : ℝ)) =
        ((h : ℝ) / (k : ℝ)) := by
    push_cast
    field_simp [hdR, hkR]
  rw [hratio]
  push_cast
  field_simp [hdR, hhR]
  ring

/--
Scaling of Vasyunin's finite cotangent formula under a common positive factor,
assuming the reduced pair is coprime.
-/
theorem vasyuninGramEntry_mul_common
    (d h k : ℕ) (hd : 0 < d) (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) :
    vasyuninGramEntry (d * h) (d * k) =
      (1 / (d : ℝ)) * vasyuninGramEntry h k := by
  have hgcdhk : Nat.gcd h k = 1 := hcop.gcd_eq_one
  have hgcd :
      Nat.gcd (d * h) (d * k) = d := by
    rw [Nat.gcd_mul_left, hgcdhk, Nat.mul_one]
  have hdvdh : (d * h) / d = h := by
    exact Nat.mul_div_left _ _ hd
  have hdvdk : (d * k) / d = k := by
    exact Nat.mul_div_left _ _ hd
  have hhself : h / Nat.gcd h k = h := by simp [hgcdhk]
  have hkself : k / Nat.gcd h k = k := by simp [hgcdhk]
  unfold vasyuninGramEntry reducedNumerator reducedDenominator
  rw [hgcd, hdvdh, hdvdk, hgcdhk, hhself, hkself]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  have hlog :
      Real.log (((d : ℝ) * k) / ((d : ℝ) * h)) =
        Real.log ((k : ℝ) / (h : ℝ)) := by
    congr 1
    field_simp [hdR, hhR]
  rw [hlog]
  field_simp [hdR, hhR, hkR]
  ring

/-- The gcd reduction required by the Vasyunin formula is purely arithmetic. -/
theorem vasyuninGCDReduction_realized :
    VasyuninGCDReduction := by
  intro p q hp hq
  let d := Nat.gcd p q
  let h := p / d
  let k := q / d
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left q hp
  have hh : 0 < h := by
    dsimp [h, d]
    exact Nat.div_pos (Nat.gcd_le_left p q) hd
  have hk : 0 < k := by
    dsimp [k, d]
    exact Nat.div_pos (Nat.gcd_le_right p q) hd
  have hcop : Nat.Coprime h k := by
    dsimp [h, k, d]
    exact gcd_div_gcd_div_gcd_of_pos_left hp
  have hp_rebuild : p = d * h := by
    dsimp [d, h]
    rw [mul_comm]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left p q)).symm
  have hq_rebuild : q = d * k := by
    dsimp [d, k]
    rw [mul_comm]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right p q)).symm
  refine ⟨hcop, ?_, ?_⟩
  · rw [hp_rebuild, hq_rebuild]
    exact explicitGramEntryNat_mul_common d h k hd hh hk
  · rw [hp_rebuild, hq_rebuild]
    exact vasyuninGramEntry_mul_common d h k hd hh hk hcop

/-- Full Vasyunin matrix identity is now reduced to the coprime analytic core only. -/
theorem vasyuninGramFormula_of_coprime
    (hcop : CoprimeVasyuninFormula) :
    VasyuninGramFormula := by
  exact vasyuninGramFormula_of_coprime_and_gcd
    hcop vasyuninGCDReduction_realized

#print axioms MCore.RH.R0.explicitGramEntryNat_mul_common
#print axioms MCore.RH.R0.vasyuninGramEntry_mul_common
#print axioms MCore.RH.R0.vasyuninGCDReduction_realized
#print axioms MCore.RH.R0.vasyuninGramFormula_of_coprime

end MCore.RH.R0
