import MCore.RH.R0.Normalization

namespace MCore.RH.R0

/-- R0.1 keeps the two L2 conventions as distinct types.  No coercion is
provided between them at this gate. -/
inductive L2Carrier where
  | zeroInfinity
  | zeroOne
  deriving DecidableEq, Repr

/-- The ambient carrier selected by R0.0. -/
def selectedCarrier : L2Carrier := .zeroInfinity

/-- Structural audit: R0.0 selected the large ambient space. -/
theorem selectedCarrier_eq_zeroInfinity : selectedCarrier = .zeroInfinity := by
  rfl

/-- A value tagged with its carrier.  This is intentionally only a type-level
boundary: no analytic realization or norm is introduced in R0.1. -/
structure CarrierTagged (c : L2Carrier) where
  label : String

/-- The future chi realization must enter through the large ambient carrier.
At R0.1 this is only a type signature, not existence of the analytic object. -/
abbrev AmbientTagged := CarrierTagged .zeroInfinity

/-- The restricted-space carrier is a different type. -/
abbrev RestrictedTagged := CarrierTagged .zeroOne

end MCore.RH.R0
