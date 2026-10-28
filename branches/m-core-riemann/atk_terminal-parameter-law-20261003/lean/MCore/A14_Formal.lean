import MCore.K8

namespace MCore

/-- The three distinguished approach directions used by the Python audit. -/
inductive ZeroDirection where
  | K0 | RHO | ETA
  deriving DecidableEq, Repr

/-- Abstract mathematical carrier for the M-Core audit. Numerical observations are
kept separate from theorem-level universal statements. -/
structure MCoreSystem where
  baseVal : ℝ
  amplitude : ℝ → ℝ
  scale : ℝ → ℝ
  zeroLimit : ZeroDirection → ℝ
  hasEdge : String → String → Prop
  phiObserved : ℝ → Prop

/-- Exact theorem-level A1. This is deliberately stronger than checking three delta values. -/
def A1_prop (sys : MCoreSystem) : Prop :=
  0 < sys.baseVal ∧
  ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧ sys.amplitude A > 1 - δ

/-- A2 records detection of the forbidden G1 ↔ G4 cycle. It does not claim that
self-reference has already been eliminated. -/
def A2_cycleDetected (sys : MCoreSystem) : Prop :=
  sys.hasEdge "G1" "G4" ∧ sys.hasEdge "G4" "G1"

/-- A3 records genuine path dependence of the zero-limit diagnostic. -/
def A3_pathDependent (sys : MCoreSystem) : Prop :=
  ∃ d₁ d₂ : ZeroDirection, d₁ ≠ d₂ ∧ sys.zeroLimit d₁ ≠ sys.zeroLimit d₂

/-- Exact theorem-level scale invariance. The finite scale tests belong to the numerical
harness and are not substituted for this universal quantifier. -/
def A4_scaleInvariant (sys : MCoreSystem) : Prop :=
  ∀ s : ℝ, 0 < s → sys.scale s = sys.baseVal

/-- The observed Phi≈0.6 values are evidence only and are intentionally not part of A4. -/
def PhiNumericalEvidence (sys : MCoreSystem) : Prop :=
  sys.phiObserved 0.309 ∧ sys.phiObserved 0.594 ∧ sys.phiObserved 0.609

/-- Combined non-vacuous audit signature. -/
def A14Signature (sys : MCoreSystem) : Prop :=
  A1_prop sys ∧ A2_cycleDetected sys ∧ A3_pathDependent sys ∧ A4_scaleInvariant sys

end MCore
