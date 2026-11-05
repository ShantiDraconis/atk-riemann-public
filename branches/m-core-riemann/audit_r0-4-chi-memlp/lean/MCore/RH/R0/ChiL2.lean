import MCore.RH.R0.ConcreteDomain
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MCore.RH.R0

open MeasureTheory

/-- The actual measure for the selected L²(0,∞) model: Lebesgue measure
restricted to the positive half-line.  This removes the ambiguity left open in
R0.2, where the base Lebesgue measure and ambient subset were recorded
separately. -/
noncomputable def zeroInfinityMeasure : Measure BaseDomain :=
  ambientMeasure.restrict zeroInfinityDomain

/-- The exponent used by the Hilbert realization. -/
noncomputable def twoExponent : ENNReal := 2

/-- R0.3's analytic obligation for the target representative. -/
def ChiMemLpTwo : Prop :=
  MemLp chiRepresentative twoExponent zeroInfinityMeasure

/-- Once the MemLp obligation is available, Mathlib supplies the Lp
equivalence-class representative.  R0.3 does not identify this object with the
abstract NB `chi`; that is a later bridge. -/
noncomputable def chiLp (hchi : ChiMemLpTwo) :
    Lp ℝ twoExponent zeroInfinityMeasure :=
  hchi.toLp chiRepresentative

end MCore.RH.R0
