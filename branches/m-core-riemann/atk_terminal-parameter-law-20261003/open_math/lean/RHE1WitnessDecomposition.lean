import MCore.RH.R0.ConcreteZeroObstruction
import MCore.RH.Analytic.MellinConcrete
import MCore.RH.Analytic.RawPowerL2Obstruction
import Lean

open Lean Elab Tactic

namespace MCore.RH.R0

open MeasureTheory Set

elab "e1_gap " name:str : tactic => do
  let g ← getMainGoal
  let fmt ← g.withContext do ppGoal g
  let body := toString fmt
  logInfo m!"[RH-E1-GAP:{name.getString}]\n{body}"
  IO.FS.writeFile s!"/tmp/rh_e1_gap_{name.getString}.txt" body

/-!
# E1 zero-witness decomposition

The frozen Hilbert carrier is L2((0,infinity), dx).
The raw power x^(rho-1) cannot be globally square-integrable on both ends
for an off-critical zero with Re(rho) > 1/2. The discovery tree therefore
must construct the correct transformed/cutoff/reproducing-kernel witness.
-/

/-- Near zero, the real power model is square integrable exactly on the beta > 1/2 side. -/
def E1_RawPowerNearZeroCondition (β : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => x ^ (2 * β - 2)) (Set.Ioo 0 1)

/-- At infinity, the same raw power is square integrable exactly on the beta < 1/2 side. -/
def E1_RawPowerTailCondition (β : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => x ^ (2 * β - 2)) (Set.Ioi 1)

theorem DISCOVER_E1_NEAR_ZERO (β : ℝ) :
    E1_RawPowerNearZeroCondition β ↔ 1 / 2 < β := by
  exact rawPower_nearZero_iff β

theorem DISCOVER_E1_TAIL (β : ℝ) :
    E1_RawPowerTailCondition β ↔ β < 1 / 2 := by
  exact rawPower_tail_iff β

/-- The actual missing object: a genuine L2 witness in the frozen carrier. -/
def E1_CorrectWitnessProducer : Prop :=
  ∀ ρ : ℂ,
    riemannZeta ρ = 0 →
    1 / 2 < ρ.re →
    ∃ w : concreteNBData.H,
      w ≠ 0 ∧
      inner ℝ concreteNBData.chi w ≠ 0 ∧
      ∀ n : ℕ, inner ℝ (concreteGeneratorFamily n) w = 0

theorem DISCOVER_E1_CORRECT_WITNESS : E1_CorrectWitnessProducer := by
  unfold E1_CorrectWitnessProducer
  intro ρ hz hβ
  e1_gap "CORRECT_L2_ZERO_WITNESS"
  exact ?_

/--
Any proposed analytic witness must also provide these three exact identities:
membership in the carrier, generator orthogonality, and nonzero target pairing.
-/
structure E1WitnessData (ρ : ℂ) where
  w : concreteNBData.H
  nonzero : w ≠ 0
  generatorOrthogonal : ∀ n : ℕ, inner ℝ (concreteGeneratorFamily n) w = 0
  targetPairingNonzero : inner ℝ concreteNBData.chi w ≠ 0

end MCore.RH.R0
