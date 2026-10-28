import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic

namespace MCore.RH.R2

noncomputable section

/--
One petal of the weighted modular bilinear sum at scale N.

The three finite coordinates encode the multistate picture:
- d : the rose / gcd scale;
- u,v : the coprime modular coordinates on that rose.

Values are stored as Fin N and interpreted arithmetically as 1 + val,
so every denominator below is strictly positive.
-/
structure SNRoseState (N : ℕ) where
  d : Fin N
  u : Fin N
  v : Fin N
deriving DecidableEq, Fintype

namespace SNRoseState

def dNat {N : ℕ} (x : SNRoseState N) : ℕ := x.d.val + 1
def uNat {N : ℕ} (x : SNRoseState N) : ℕ := x.u.val + 1
def vNat {N : ℕ} (x : SNRoseState N) : ℕ := x.v.val + 1

end SNRoseState

/--
All data needed to instantiate the weighted modular bilinear expression.

coeff N n represents c_{N,n}.
V a b represents the Vasyunin/cotangent contribution V(a,b).
far N d u v is the frozen FAR selector.
-/
structure WeightedModularBilinearData where
  coeff : ℕ → ℕ → ℝ
  V : ℕ → ℕ → ℝ
  far : ℕ → ℕ → ℕ → ℕ → Prop
  farDecidable : ∀ N d u v, Decidable (far N d u v)

attribute [instance] WeightedModularBilinearData.farDecidable

/--
Arithmetic selector for admissible petals:
coprime (u,v) and membership in the FAR region.
-/
def admissiblePetal
    (D : WeightedModularBilinearData)
    {N : ℕ}
    (x : SNRoseState N) : Prop :=
  Nat.Coprime x.uNat x.vNat ∧
  D.far N x.dNat x.uNat x.vNat

instance admissiblePetalDecidable
    (D : WeightedModularBilinearData)
    {N : ℕ}
    (x : SNRoseState N) :
    Decidable (admissiblePetal D x) := by
  unfold admissiblePetal
  infer_instance

/--
A single petal contribution

  log N * (1/d) * c_{N,du} c_{N,dv}
        * (V(v,u)+V(u,v))/(uv).
-/
def petalContribution
    (D : WeightedModularBilinearData)
    {N : ℕ}
    (x : SNRoseState N) : ℝ :=
  Real.log N *
    (1 / (x.dNat : ℝ)) *
    D.coeff N (x.dNat * x.uNat) *
    D.coeff N (x.dNat * x.vNat) *
    ((D.V x.vNat x.uNat + D.V x.uNat x.vNat) /
      ((x.uNat : ℝ) * (x.vNat : ℝ)))

/--
The d-th rose: sum of all admissible coprime petals with fixed d-state.
-/
def roseContribution
    (D : WeightedModularBilinearData)
    (N : ℕ)
    (d : Fin N) : ℝ :=
  ∑ x : SNRoseState N,
    if x.d = d ∧ admissiblePetal D x
    then petalContribution D x
    else 0

/--
The scalar S_N as the bouquet of all d-roses.
Each rose internally sums its simultaneous (u,v) petals.
-/
def SN
    (D : WeightedModularBilinearData)
    (N : ℕ) : ℝ :=
  ∑ d : Fin N, roseContribution D N d

/--
Exact bouquet-of-roses decomposition.
-/
theorem SN_eq_sum_roses
    (D : WeightedModularBilinearData)
    (N : ℕ) :
    SN D N = ∑ d : Fin N, roseContribution D N d := by
  rfl

/--
The unique terminal analytic producer:
there is a vanishing majorant eventually dominating abs(S_N).

This is the formal WEIGHTED_MODULAR_BILINEAR_DECAY certificate.
-/
def WeightedModularBilinearDecay
    (D : WeightedModularBilinearData) : Prop :=
  ∃ eps : ℕ → ℝ,
    (∀ᶠ N : ℕ in Filter.atTop, |SN D N| ≤ eps N) ∧
    Filter.Tendsto eps Filter.atTop (nhds 0)

/--
Terminal F1 VANISHING theorem:
the decay certificate forces S_N -> 0.
-/
theorem SN_tendsto_zero_of_weighted_modular_bilinear_decay
    (D : WeightedModularBilinearData)
    (h : WeightedModularBilinearDecay D) :
    Filter.Tendsto (SN D) Filter.atTop (nhds 0) := by
  rcases h with ⟨eps, hupper, heps⟩
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun N => abs_nonneg (SN D N))
    hupper
    heps

/--
Equivalent terminal form: a direct proof S_N -> 0 supplies the
minimal decay certificate by taking eps_N = abs(S_N).
-/
theorem weighted_modular_bilinear_decay_iff_SN_tendsto_zero
    (D : WeightedModularBilinearData) :
    WeightedModularBilinearDecay D ↔
      Filter.Tendsto (SN D) Filter.atTop (nhds 0) := by
  constructor
  · exact SN_tendsto_zero_of_weighted_modular_bilinear_decay D
  · intro hSN
    refine ⟨fun N => |SN D N|, Filter.Eventually.of_forall ?_, ?_⟩
    · intro N
      exact le_rfl
    · simpa using hSN.abs

/--
ATK one-gap marker.  This file formalizes the exact theorem shape and
does not manufacture an inhabitant of the decay certificate.
-/
def materialProducerGaps : Nat := 1

theorem material_producer_gaps_eq_one :
    materialProducerGaps = 1 := by
  rfl

#print axioms MCore.RH.R2.SN_eq_sum_roses
#print axioms MCore.RH.R2.SN_tendsto_zero_of_weighted_modular_bilinear_decay
#print axioms MCore.RH.R2.weighted_modular_bilinear_decay_iff_SN_tendsto_zero
#print axioms MCore.RH.R2.material_producer_gaps_eq_one

end
end MCore.RH.R2
