import Mathlib

/-!
# Finite algebra of the two prime ramps

The rational expression in the second term is the value of
`∫ t in n..x, (1 - n / t) / t^2`. The analytic evaluation and the
identification with the integral of the step sum are separate obligations.
-/

namespace RiemannRamps

theorem ramp_term (x n : ℝ) (hx : x ≠ 0) (hn : n ≠ 0) :
    x / n - 1 =
      (1 - n / x) + 2 * x * (1 / (2 * n) - 1 / x + n / (2 * x ^ 2)) := by
  field_simp [hx, hn] <;> ring

theorem ramp_weighted_sum {ι : Type*} (indices : Finset ι)
    (weight location : ι → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hn : ∀ i ∈ indices, location i ≠ 0) :
    (∑ i ∈ indices, weight i * (x / location i - 1)) =
      ∑ i ∈ indices,
        weight i * ((1 - location i / x) +
          2 * x * (1 / (2 * location i) - 1 / x + location i / (2 * x ^ 2))) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun t : ℝ => weight i * t) (ramp_term x (location i) hx (hn i hi))

#print axioms ramp_term
#print axioms ramp_weighted_sum

end RiemannRamps
