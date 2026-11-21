import Mathlib

namespace R01
open Finset

def cellWeight (j : ℕ) : ℝ := (j : ℝ) * (j + 1)
def cellEnergy (M : ℕ) (d : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Icc 1 M, cellWeight j * d j ^ 2

def multiplierValue (N : ℕ) (a : ℝ) (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  a + ∑ k ∈ Icc 2 N, v k * (j % k : ℕ)

noncomputable def multiplierLoss (N M : ℕ) (a : ℝ) (v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Icc 1 M, multiplierValue N a v j ^ 2 / cellWeight j

theorem multiplier_pairing {N M : ℕ} {d : ℕ → ℝ} (a : ℝ) (v : ℕ → ℝ)
    (hn : ∑ j ∈ Icc 1 M, d j = 1)
    (hz : ∀ k ∈ Icc 2 N, ∑ j ∈ Icc 1 M, ((j % k : ℕ) : ℝ) * d j = 0) :
    ∑ j ∈ Icc 1 M, multiplierValue N a v j * d j = a := by
  simp only [multiplierValue, add_mul, sum_add_distrib, sum_mul]
  rw [← mul_sum, hn, mul_one, sum_comm]
  simp only [mul_assoc, ← mul_sum]
  simp only [add_eq_left]
  exact sum_eq_zero fun k hk => by rw [hz k hk, mul_zero]

/-- Complete the square for every cell and sum. Choosing the scale a/loss
gives the weighted Cauchy-Schwarz certificate without extracting square roots. -/
theorem dual_energy_lower_bound {N M : ℕ} {d : ℕ → ℝ} (a : ℝ) (v : ℕ → ℝ)
    (hn : ∑ j ∈ Icc 1 M, d j = 1)
    (hz : ∀ k ∈ Icc 2 N, ∑ j ∈ Icc 1 M, ((j % k : ℕ) : ℝ) * d j = 0)
    (hpos : 0 < multiplierLoss N M a v) :
    a^2 / multiplierLoss N M a v ≤ cellEnergy M d := by
  let t := a / multiplierLoss N M a v
  have hcell (j : ℕ) (hj : j ∈ Icc 1 M) :
      2*t*(multiplierValue N a v j * d j) -
        t^2*(multiplierValue N a v j ^ 2 / cellWeight j) ≤ cellWeight j * d j^2 := by
    have hnat : 0 < j := (mem_Icc.mp hj).1
    have hw : 0 < cellWeight j := by unfold cellWeight; positivity
    apply (le_of_sub_nonneg)
    have he : cellWeight j * d j^2 -
        (2*t*(multiplierValue N a v j * d j) -
        t^2*(multiplierValue N a v j ^ 2 / cellWeight j)) =
        (cellWeight j*d j - t*multiplierValue N a v j)^2 / cellWeight j := by
      field_simp [hw.ne']; ring
    rw [he]
    positivity
  have hs := sum_le_sum hcell
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, multiplier_pairing a v hn hz] at hs
  change 2*t*a - t^2 * multiplierLoss N M a v ≤ cellEnergy M d at hs
  have hid : 2*t*a - t^2 * multiplierLoss N M a v = a^2 / multiplierLoss N M a v := by
    dsimp [t]
    field_simp [hpos.ne']; ring
  rwa [hid] at hs

#print axioms multiplier_pairing
#print axioms dual_energy_lower_bound

/-- Telescoping with both boundary terms displayed. -/
theorem sum_cell_increments (F : ℕ → ℝ) {m M : ℕ} (hm : m ≤ M) :
    ∑ j ∈ Icc m M, (F j - F (j+1)) = F m - F (M+1) := by
  induction M with
  | zero =>
    have : m = 0 := by omega
    simp [this]
  | succ M ih =>
    by_cases h : m ≤ M
    · rw [sum_Icc_succ_top (by omega), ih h]
      abel
    · have : m = M+1 := by omega
      simp [this]

/-- Count the positive multiples of k up to each column index. -/
theorem sum_multiple_tails (d : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (M : ℕ) :
    (∑ r ∈ Icc 1 (M/k), ∑ j ∈ Icc (k*r) M, d j) =
      ∑ j ∈ Icc 1 M, ((j/k : ℕ) : ℝ) * d j := by
  have tail (r : ℕ) (hr : r ∈ Icc 1 (M/k)) :
      (∑ j ∈ Icc (k*r) M, d j) =
        ∑ j ∈ Icc 1 M, if k*r ≤ j then d j else 0 := by
    rw [← sum_filter]
    have hp : 0 < r := (mem_Icc.mp hr).1
    have hkr := Nat.mul_pos hk hp
    congr 1
    ext j
    simp only [mem_Icc, mem_filter]
    omega
  rw [sum_congr rfl tail, sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [← sum_filter]
  have he : (Icc 1 (M/k)).filter (fun r => k*r ≤ j) = Icc 1 (j/k) := by
    ext r
    simp only [mem_filter, mem_Icc]
    have hdiv : j/k ≤ M/k := Nat.div_le_div_right (mem_Icc.mp hj).2
    have hiff : r ≤ j/k ↔ k*r ≤ j := by
      rw [Nat.le_div_iff_mul_le hk, Nat.mul_comm]
    omega
  rw [he]
  simp [Nat.card_Icc]

/-- The difference of the two sums of F is precisely the modular moment. -/
theorem multiple_link_identity (F : ℕ → ℝ) {k M : ℕ} (hk : 0 < k)
    (hend : F (M+1) = 0) :
    (∑ m ∈ Icc 1 M, F m) - (k : ℝ)*(∑ r ∈ Icc 1 (M/k), F (k*r)) =
      ∑ j ∈ Icc 1 M, ((j%k : ℕ) : ℝ)*(F j - F (j+1)) := by
  let d := fun j => F j - F (j+1)
  have atK (l : ℕ) (hl : 0 < l) :
      (∑ r ∈ Icc 1 (M/l), F (l*r)) = ∑ j ∈ Icc 1 M, ((j/l : ℕ) : ℝ)*d j := by
    rw [← sum_multiple_tails d hl M]
    refine sum_congr rfl fun r hr => ?_
    have hm : l*r ≤ M := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hl).mp (mem_Icc.mp hr).2
    simpa only [d, hend, sub_zero] using (sum_cell_increments F hm).symm
  have one := atK 1 (by decide)
  simp only [Nat.div_one, one_mul] at one
  rw [one, atK k hk, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h : (j : ℝ) = ((j%k : ℕ) : ℝ) + (k : ℝ)*((j/k : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div j k).symm
  dsimp only [d]
  nlinarith only [congrArg (fun x : ℝ => x * (F j - F (j+1))) h]

theorem dual_energy_from_multiple_links {N M : ℕ} (hM : 1 ≤ M)
    (F : ℕ → ℝ) (hfirst : F 1 = 1) (hend : F (M+1) = 0)
    (links : ∀ k ∈ Icc 2 N, (∑ m ∈ Icc 1 M, F m) =
      (k : ℝ)*(∑ r ∈ Icc 1 (M/k), F (k*r)))
    (a : ℝ) (v : ℕ → ℝ) (hpos : 0 < multiplierLoss N M a v) :
    a^2 / multiplierLoss N M a v ≤ cellEnergy M (fun j => F j - F (j+1)) := by
  apply dual_energy_lower_bound a v _ _ hpos
  · simpa only [hend, hfirst, sub_zero] using sum_cell_increments F hM
  · intro k hk
    have hp : 0 < k := by have := (mem_Icc.mp hk).1; omega
    rw [← multiple_link_identity F hp hend, links k hk, sub_self]

#print axioms sum_cell_increments
#print axioms sum_multiple_tails
#print axioms multiple_link_identity
#print axioms dual_energy_from_multiple_links


/-- Exact two-generator optimum over six cells, in the sign convention of multiplierLoss. -/
theorem six_cell_gap (x y : ℝ) :
    multiplierLoss 3 6 1 (fun k => if k = 2 then -x else -y) - 233/3682 =
      (37/60) * ((x-1059/1841) + (34/37)*(y-851/1841))^2 +
      (1841/2220) * (y-851/1841)^2 := by
  norm_num [multiplierLoss, multiplierValue, cellWeight,
    show Icc 1 6 = ({1,2,3,4,5,6} : Finset ℕ) by decide,
    show Icc 2 3 = ({2,3} : Finset ℕ) by decide] <;> ring

theorem six_cell_exact_loss :
    IsLeast {q : ℝ | ∃ x y : ℝ,
      q = multiplierLoss 3 6 1 (fun k => if k = 2 then -x else -y)} (233/3682) := by
  constructor
  · refine ⟨1059/1841, 851/1841, ?_⟩
    have h := six_cell_gap (1059/1841) (851/1841)
    linarith only [h]
  · rintro q ⟨x, y, rfl⟩
    have h := six_cell_gap x y
    nlinarith only [h, sq_nonneg ((x-1059/1841) + (34/37)*(y-851/1841)),
      sq_nonneg (y-851/1841)]

#print axioms six_cell_gap
#print axioms six_cell_exact_loss

end R01
