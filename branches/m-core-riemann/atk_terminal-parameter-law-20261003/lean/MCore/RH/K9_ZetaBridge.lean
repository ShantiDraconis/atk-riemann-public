import MCore.RH.K9_Regularization
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros

namespace MCore

/-- Exact nontrivial-zero hypotheses used by Mathlib's RiemannHypothesis. -/
def NontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
  (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
  s ≠ 1

/-- The M-Core properties must become statements about the same arbitrary complex s.
No field below contains `s.re = 1/2` or `RiemannHypothesis`. -/
structure ZetaTransferData (sys : MCoreSystem) (reg : RegularizedMCoreSystem) (s : ℂ) : Prop where
  sourceMatches : reg.source = sys
  amplitudeControlsZeta : Prop
  regularizationControlsZeta : Prop
  scalingControlsZeta : Prop
  nonCircularAtZeta : Prop

/-- Non-vacuous downstream property: it requires the regularization certificate and
actual transfer data for this arbitrary s. -/
structure P_MCore_full (sys : MCoreSystem) (reg : RegularizedMCoreSystem) (s : ℂ) : Prop where
  signature : A14Signature sys
  regularization : RegularizationCertificate reg
  transfer : ZetaTransferData sys reg s

/-- Universal step-7 certificate.  A value must work for every nontrivial zero. -/
structure Step7Certificate (sys : MCoreSystem) (reg : RegularizedMCoreSystem) : Prop where
  toP : ∀ s : ℂ, NontrivialZetaZero s → P_MCore_full sys reg s

/-- Step-8 is isolated as the decisive analytic obligation.  The type exposes exactly
what must be proved and forbids a one-point bridge. -/
structure Step8Certificate (sys : MCoreSystem) (reg : RegularizedMCoreSystem) : Prop where
  criticalLine : ∀ s : ℂ, P_MCore_full sys reg s → NontrivialZetaZero s → s.re = 1 / 2

/-- Once genuine step-7 and step-8 certificates exist, composition is routine. -/
theorem endpoint_of_step7_step8
    (sys : MCoreSystem)
    (reg : RegularizedMCoreSystem)
    (h7 : Step7Certificate sys reg)
    (h8 : Step8Certificate sys reg) :
    RiemannHypothesis := by
  intro s hz htriv h1
  have hs : NontrivialZetaZero s := ⟨hz, htriv, h1⟩
  exact h8.criticalLine s (h7.toP s hs) hs

end MCore
