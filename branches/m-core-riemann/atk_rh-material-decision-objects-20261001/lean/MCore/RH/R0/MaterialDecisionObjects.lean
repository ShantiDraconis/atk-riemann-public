import Mathlib.Analysis.SpecialFunctions.Zeta

namespace MCore.RH.MaterialDecision

/--
Exact classical RH statement used by this decision layer.
-/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ,
    riemannZeta s = 0 →
    s ≠ 0 →
    s ≠ 1 →
    0 < s.re →
    s.re < 1 →
    s.re = (1 : ℝ) / 2

/--
Concrete negative-side object: an actual nontrivial zeta zero in the critical
strip whose real part is not 1/2.
-/
structure OffCriticalZero where
  s : ℂ
  zero : riemannZeta s = 0
  nonzero : s ≠ 0
  nonone : s ≠ 1
  re_pos : 0 < s.re
  re_lt_one : s.re < 1
  off_line : s.re ≠ (1 : ℝ) / 2

/--
A concrete OffCriticalZero directly refutes RH.
No not-RH hypothesis appears as an input.
-/
theorem OffCriticalZero.refutes_rh
    (z : OffCriticalZero) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact z.off_line
    (hRH z.s z.zero z.nonzero z.nonone z.re_pos z.re_lt_one)

/--
A branch classifier for a concrete complex point.
It never declares a point to be a counterexample unless all official
counterexample conditions are actually proved.
-/
inductive ZeroClassification (s : ℂ) where
  | notRelevant
  | criticalLine
      (hz : riemannZeta s = 0)
      (hstrip0 : 0 < s.re)
      (hstrip1 : s.re < 1)
      (hre : s.re = (1 : ℝ) / 2)
  | offCritical
      (z : OffCriticalZero)
      (hs : z.s = s)

/--
Any off-critical classification yields a concrete refutation object.
-/
def ZeroClassification.toCounterexample?
    {s : ℂ} :
    ZeroClassification s → Option OffCriticalZero
  | .notRelevant => none
  | .criticalLine _ _ _ _ => none
  | .offCritical z _ => some z

/--
The negative branch is stable under exact equality of the zero.
-/
def OffCriticalZero.transport
    (z : OffCriticalZero)
    {t : ℂ}
    (h : z.s = t) :
    OffCriticalZero where
  s := t
  zero := by simpa [← h] using z.zero
  nonzero := by simpa [← h] using z.nonzero
  nonone := by simpa [← h] using z.nonone
  re_pos := by simpa [← h] using z.re_pos
  re_lt_one := by simpa [← h] using z.re_lt_one
  off_line := by simpa [← h] using z.off_line

/--
A claimed counterexample on the critical line is impossible.
-/
theorem no_offCriticalZero_on_critical_line
    (z : OffCriticalZero)
    (hre : z.s.re = (1 : ℝ) / 2) :
    False :=
  z.off_line hre

#print axioms MCore.RH.MaterialDecision.OffCriticalZero.refutes_rh
#print axioms MCore.RH.MaterialDecision.OffCriticalZero.transport
#print axioms MCore.RH.MaterialDecision.no_offCriticalZero_on_critical_line

end MCore.RH.MaterialDecision
