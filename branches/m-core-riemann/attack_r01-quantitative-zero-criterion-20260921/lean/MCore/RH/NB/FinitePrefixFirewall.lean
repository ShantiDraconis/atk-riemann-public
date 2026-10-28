import Mathlib

namespace MCore.RHFinitePrefixFirewall

/-!
R01 finite-prefix firewall.

The certified finite Nyman--Beurling ladder is valuable evidence, but finite
values alone cannot determine an infinite asymptotic conclusion.  This file
constructs, after every finite prefix length N, two nonnegative antitone real
sequences agreeing on the whole prefix: one drops to zero immediately after
the prefix, while the other remains identically one.

This is a logical countercertificate against finite-to-infinite promotion.
It is not a statement that the actual DN sequence has either continuation.
-/

def dropAfter (N n : ℕ) : ℝ :=
  if n ≤ N then 1 else 0

def ones (_ : ℕ) : ℝ := 1

theorem dropAfter_nonnegative (N n : ℕ) :
    0 ≤ dropAfter N n := by
  simp [dropAfter]
  split <;> norm_num

theorem dropAfter_antitone (N : ℕ) :
    Antitone (dropAfter N) := by
  intro a b hab
  by_cases ha : a ≤ N
  · by_cases hb : b ≤ N
    · simp [dropAfter, ha, hb]
    · simp [dropAfter, ha, hb]
  · have hb : ¬ b ≤ N := by
      intro hbN
      exact ha (hab.trans hbN)
    simp [dropAfter, ha, hb]

theorem ones_nonnegative (n : ℕ) :
    0 ≤ ones n := by
  simp [ones]

theorem ones_antitone :
    Antitone ones := by
  intro a b hab
  simp [ones]

theorem agree_on_prefix (N n : ℕ) (hn : n ≤ N) :
    dropAfter N n = ones n := by
  simp [dropAfter, ones, hn]

theorem drop_after_prefix_is_zero (N : ℕ) :
    dropAfter N (N + 1) = 0 := by
  simp [dropAfter]

theorem ones_after_prefix_is_one (N : ℕ) :
    ones (N + 1) = 1 := by
  rfl

theorem finite_prefix_has_distinct_antitone_nonnegative_extensions
    (N : ℕ) :
    ∃ f g : ℕ → ℝ,
      (∀ n, 0 ≤ f n) ∧
      (∀ n, 0 ≤ g n) ∧
      Antitone f ∧
      Antitone g ∧
      (∀ n, n ≤ N → f n = g n) ∧
      f (N + 1) = 0 ∧
      g (N + 1) = 1 := by
  refine ⟨dropAfter N, ones, ?_, ?_, dropAfter_antitone N,
    ones_antitone, ?_, drop_after_prefix_is_zero N, ones_after_prefix_is_one N⟩
  · exact dropAfter_nonnegative N
  · exact ones_nonnegative
  · intro n hn
    exact agree_on_prefix N n hn

#print axioms MCore.RHFinitePrefixFirewall.dropAfter_antitone
#print axioms MCore.RHFinitePrefixFirewall.finite_prefix_has_distinct_antitone_nonnegative_extensions

end MCore.RHFinitePrefixFirewall
