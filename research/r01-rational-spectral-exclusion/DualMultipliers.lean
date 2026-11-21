import Mathlib

namespace R01
open Finset

def cellWeight (j : ℕ) : ℝ := (j : ℝ) * (j + 1)
def cellEnergy (M : ℕ) (d : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Icc 1 M, cellWeight j * d j ^ 2

def multiplierValue (N : ℕ) (a : ℝ) (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  a + ∑ k ∈ Icc 2 N, v k * (j % k : ℕ)

def multiplierLoss (N M : ℕ) (a : ℝ) (v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Icc 1 M, multiplierValue N a v j ^ 2 / cellWeight j

theorem multiplier_pairing {N M : ℕ} {d : ℕ → ℝ} (a : ℝ) (v : ℕ → ℝ)
    (hn : ∑ j ∈ Icc 1 M, d j = 1)
    (hz : ∀ k ∈ Icc 2 N, ∑ j ∈ Icc 1 M, ((j % k : ℕ) : ℝ) * d j = 0) :
    ∑ j ∈ Icc 1 M, multiplierValue N a v j * d j = a := by
  simp only [multiplierValue, add_mul, sum_add_distrib, sum_mul]
  rw [← mul_sum, hn, mul_one, sum_comm]
  simp only [mul_assoc, ← mul_sum]
  simp [hz]

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
end R01
