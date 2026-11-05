import MCore.RH.NB.Total

namespace MCore.RH.R0

/-- Concrete positive dilation parameter. It cannot represent zero. -/
structure PositiveIndex where
  val : ℕ
  positive : 0 < val

/-- The chosen bridge from the frozen zero-based abstract generator index to the
positive-integer arithmetic indexing used by the selected Báez-Duarte convention. -/
def baezDuarteIndex (n : ℕ) : PositiveIndex :=
  ⟨n + 1, Nat.succ_pos n⟩

@[simp] theorem baezDuarteIndex_val (n : ℕ) :
    (baezDuarteIndex n).val = n + 1 := rfl

@[simp] theorem baezDuarteIndex_zero :
    (baezDuarteIndex 0).val = 1 := rfl

/-- R0.0 records only the convention selected for the later concrete realization.
It deliberately contains no RH, density, closure, or zero-defect assertion. -/
inductive AmbientConvention where
  | L2ZeroInfinity

def selectedAmbient : AmbientConvention := AmbientConvention.L2ZeroInfinity

/-- Documentary provenance of the exact immutable NB_TOTAL scientific source consumed
by this R0 lineage. This string is evidence metadata, not a mathematical hypothesis. -/
def nbTotalSourceSHA : String :=
  "38aad03c90103ad9b6cf0a31169b1855869cba11"

end MCore.RH.R0
