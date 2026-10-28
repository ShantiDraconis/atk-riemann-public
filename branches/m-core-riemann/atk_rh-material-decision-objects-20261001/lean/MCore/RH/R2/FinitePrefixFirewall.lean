import Mathlib

namespace MCore.RH.FinitePrefixFirewall

/--
A concrete sequence that is identically zero on a prescribed finite prefix
and identically one afterwards.
-/
def prefixZeroThenOne (N0 n : ℕ) : ℝ :=
  if n ≤ N0 then 0 else 1

theorem prefixZeroThenOne_agrees_on_prefix
    (N0 n : ℕ)
    (hn : n ≤ N0) :
    prefixZeroThenOne N0 n = 0 := by
  simp [prefixZeroThenOne, hn]

theorem prefixZeroThenOne_tail
    (N0 n : ℕ)
    (hn : N0 < n) :
    prefixZeroThenOne N0 n = 1 := by
  have hnot : ¬ n ≤ N0 := Nat.not_le_of_gt hn
  simp [prefixZeroThenOne, hnot]

/--
No finite prefix can force all future values to remain small:
after matching the zero sequence through N0, the next value can already be 1.
-/
theorem finite_prefix_does_not_force_next_small
    (N0 : ℕ) :
    (∀ n ≤ N0, prefixZeroThenOne N0 n = 0) ∧
    prefixZeroThenOne N0 (N0 + 1) = 1 := by
  constructor
  · intro n hn
    exact prefixZeroThenOne_agrees_on_prefix N0 n hn
  · exact prefixZeroThenOne_tail N0 (N0 + 1) (Nat.lt_succ_self N0)

/--
More generally, for any finite observation horizon N0 and any proposed
eventual upper bound B < 1, there is a sequence agreeing with perfect zero data
on the whole observed prefix but violating the bound immediately afterwards.
-/
theorem finite_prefix_cannot_certify_eventual_bound
    (N0 : ℕ)
    (B : ℝ)
    (hB : B < 1) :
    ∃ f : ℕ → ℝ,
      (∀ n ≤ N0, f n = 0) ∧
      B < f (N0 + 1) := by
  refine ⟨prefixZeroThenOne N0, ?_, ?_⟩
  · intro n hn
    exact prefixZeroThenOne_agrees_on_prefix N0 n hn
  · rw [prefixZeroThenOne_tail N0 (N0 + 1) (Nat.lt_succ_self N0)]
    exact hB

/--
Firewall interpretation: a finite table of sampled DN values, by itself,
cannot entail a universal tail inequality. Any such promotion requires an
analytic theorem connecting the official observable to its entire tail.
-/
theorem no_finite_zero_prefix_implies_uniform_tail_bound :
    ¬ (∀ (N0 : ℕ) (f : ℕ → ℝ),
        (∀ n ≤ N0, f n = 0) →
        ∀ n > N0, f n ≤ (1 / 2 : ℝ)) := by
  intro H
  let N0 : ℕ := 8
  let f := prefixZeroThenOne N0
  have hp : ∀ n ≤ N0, f n = 0 := by
    intro n hn
    exact prefixZeroThenOne_agrees_on_prefix N0 n hn
  have htail := H N0 f hp (N0 + 1) (Nat.lt_succ_self N0)
  have hone : f (N0 + 1) = 1 :=
    prefixZeroThenOne_tail N0 (N0 + 1) (Nat.lt_succ_self N0)
  rw [hone] at htail
  norm_num at htail

#print axioms MCore.RH.FinitePrefixFirewall.finite_prefix_does_not_force_next_small
#print axioms MCore.RH.FinitePrefixFirewall.finite_prefix_cannot_certify_eventual_bound
#print axioms MCore.RH.FinitePrefixFirewall.no_finite_zero_prefix_implies_uniform_tail_bound

end MCore.RH.FinitePrefixFirewall
