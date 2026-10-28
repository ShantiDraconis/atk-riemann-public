import Mathlib.Analysis.SpecialFunctions.Zeta

namespace MCore.Audit

/--
Canonical typed endpoint for the classical Riemann Hypothesis.

This is a DEFINITION ONLY.  It does not assert or prove RH.
The source checkpoint 28033534e714b442d9cc6383f43a12917ee5cf53
recorded that the classical endpoint was not yet typed.
-/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ,
    riemannZeta s = 0 →
    s ≠ 0 →
    s ≠ 1 →
    0 < s.re →
    s.re < 1 →
    s.re = (1 : ℝ) / 2

/-- The backward-dense audit target is exactly the typed RH proposition. -/
def FINAL_STATEMENT : Prop := RiemannHypothesis

end MCore.Audit
