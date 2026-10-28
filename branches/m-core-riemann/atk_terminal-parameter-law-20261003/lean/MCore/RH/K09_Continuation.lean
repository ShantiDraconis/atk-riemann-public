import MCore.K8
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MCore

/-- Reused Mathlib result: the pole-subtracted completed zeta Λ₀ is entire. -/
theorem completedZeta_entire_real :
    Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedZeta₀

/-- The completed zeta Λ itself is differentiable away from 0 and 1. -/
theorem completedZeta_differentiable_off_poles
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedZeta h0 h1

end MCore
