import Mathlib.NumberTheory.LSeries.RiemannZeta
import IndeterminateRiemann.Transform

/-!
# Applying the transform to the Riemann zeta function

`riemannZeta` and `RiemannHypothesis` are Mathlib's own definitions
(Mathlib v4.19.0, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`):

```
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

Question: what happens to RH when ζ is passed through the transform?
-/

namespace IndeterminateRiemann

/-- The zero set of ζ is preserved exactly. -/
theorem zeta_transform_zero_iff (s : ℂ) :
    IndeterminateTransform (riemannZeta s) = 0 ↔ riemannZeta s = 0 :=
  transform_eq_zero_iff _

/-- A trivial zero, ζ(-2) = 0, is sent to 0. -/
theorem transform_zeta_neg_two : IndeterminateTransform (riemannZeta (-2)) = 0 := by
  have h : riemannZeta (-2) = 0 := by
    have := riemannZeta_neg_two_mul_nat_add_one 0
    simpa using this
  exact (zeta_transform_zero_iff (-2)).mpr h

/-- The transform forgets where a zero is: any two zeros of ζ have the same
image, wherever they lie. In particular it carries no information about
`Re s`, which is what RH is about. -/
theorem transform_forgets_location (s t : ℂ)
    (hs : riemannZeta s = 0) (ht : riemannZeta t = 0) :
    IndeterminateTransform (riemannZeta s) = IndeterminateTransform (riemannZeta t) := by
  rw [(zeta_transform_zero_iff s).mpr hs, (zeta_transform_zero_iff t).mpr ht]

/-- RH written through the transform. -/
def TransformedRH : Prop :=
  ∀ s : ℂ, IndeterminateTransform (riemannZeta s) = 0 →
    (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2

/-- Main result: the transformed statement is exactly the Riemann Hypothesis.
Nothing is gained and nothing is lost; proving one is proving the other. -/
theorem transformedRH_iff_RH : TransformedRH ↔ RiemannHypothesis := by
  unfold TransformedRH RiemannHypothesis
  constructor
  · intro h s hz hn h1
    exact h s ((zeta_transform_zero_iff s).mpr hz) hn h1
  · intro h s hz hn h1
    exact h s ((zeta_transform_zero_iff s).mp hz) hn h1

/-- With propositional extensionality the two statements are the same
proposition, not merely equivalent ones. -/
theorem transformedRH_eq_RH : TransformedRH = RiemannHypothesis :=
  propext transformedRH_iff_RH

/-- Consequently a proof of either is a proof of the other. -/
theorem RH_of_transformedRH (h : TransformedRH) : RiemannHypothesis :=
  transformedRH_iff_RH.mp h

theorem transformedRH_of_RH (h : RiemannHypothesis) : TransformedRH :=
  transformedRH_iff_RH.mpr h

end IndeterminateRiemann
