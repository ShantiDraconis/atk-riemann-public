import MCore.RH.Analytic.FourierMellinCriticalLine
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space

namespace MCore.RH.R0

open MeasureTheory
open scoped FourierTransform

/--
Standard Fourier-Plancherel theorem missing from the pinned Mathlib revision.
This proposition contains no zeta function, no RH statement and no Nyman--Beurling data.
It is therefore a library/infrastructure obligation, not OPEN_MATH(RH).
-/
def PinnedFourierPlancherel : Prop :=
  ∀ g : ℝ → ℂ,
    Integrable g volume →
    MemLp g 2 volume →
      (∫ u : ℝ, Complex.normSq (g u)) =
        ∫ ξ : ℝ, Complex.normSq (𝓕 g ξ)

/--
The exact specialization of standard Plancherel needed by D3.
-/
def CriticalPullbackFourierPlancherel : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    (∫ u : ℝ, Complex.normSq (criticalLogPullback c u)) =
      ∫ ξ : ℝ, Complex.normSq (𝓕 (criticalLogPullback c) ξ)

/--
Membership bridge needed to instantiate the standard L2 theorem.
Kept separate so the kernel distinguishes local L2 bookkeeping from Plancherel itself.
-/
def CriticalLogPullbackMemL2 : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    MemLp (criticalLogPullback c) 2 volume

/-- The critical pullback is also L1, so the old pointwise Fourier integral is legitimate. -/
def CriticalLogPullbackIntegrable : Prop :=
  ∀ {N : ℕ} (c : Fin N → ℝ),
    Integrable (criticalLogPullback c) volume

theorem criticalPullbackFourierPlancherel_of_pinned
    (hP : PinnedFourierPlancherel)
    (hL1 : CriticalLogPullbackIntegrable)
    (hL2 : CriticalLogPullbackMemL2) :
    CriticalPullbackFourierPlancherel := by
  intro N c
  exact hP (criticalLogPullback c) (hL1 c) (hL2 c)

/--
D3.2 is exactly the local specialization of the standard pinned-library gap.
-/
theorem d3_fourierPlancherel_of_pinned
    (hP : PinnedFourierPlancherel)
    (hL1 : CriticalLogPullbackIntegrable)
    (hL2 : CriticalLogPullbackMemL2) :
    ∀ {N : ℕ} (c : Fin N → ℝ),
      (∫ u : ℝ, Complex.normSq (criticalLogPullback c u)) =
        ∫ ξ : ℝ, Complex.normSq (𝓕 (criticalLogPullback c) ξ) := by
  exact criticalPullbackFourierPlancherel_of_pinned hP hL1 hL2

#print axioms MCore.RH.R0.criticalPullbackFourierPlancherel_of_pinned
#print axioms MCore.RH.R0.d3_fourierPlancherel_of_pinned

end MCore.RH.R0
