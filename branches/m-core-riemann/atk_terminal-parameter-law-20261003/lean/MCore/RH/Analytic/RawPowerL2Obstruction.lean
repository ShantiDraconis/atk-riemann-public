import MCore.RH.R0.ConcreteZeroObstruction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace MCore.RH.R0

open MeasureTheory Set

/-- Near zero, the raw power model is square integrable exactly for beta > 1/2. -/
theorem rawPower_nearZero_iff
    (β : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * β - 2)) (Ioo 0 1)
      ↔ 1 / 2 < β := by
  rw [integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

/-- At infinity, the same raw power is square integrable exactly for beta < 1/2. -/
theorem rawPower_tail_iff
    (β : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * β - 2)) (Ioi 1)
      ↔ β < 1 / 2 := by
  rw [integrableOn_Ioi_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

/-- No real exponent can make the uncut raw-power witness square integrable at both ends. -/
theorem no_rawPower_global_L2_exponent (β : ℝ) :
    ¬ (IntegrableOn (fun x : ℝ => x ^ (2 * β - 2)) (Ioo 0 1) ∧
       IntegrableOn (fun x : ℝ => x ^ (2 * β - 2)) (Ioi 1)) := by
  rw [rawPower_nearZero_iff, rawPower_tail_iff]
  linarith

#print axioms MCore.RH.R0.rawPower_nearZero_iff
#print axioms MCore.RH.R0.rawPower_tail_iff
#print axioms MCore.RH.R0.no_rawPower_global_L2_exponent

end MCore.RH.R0
