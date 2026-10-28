import MCore.RH.NB.WeightedModularBilinearDecay
import Mathlib

namespace MCore.RH.NB

open scoped BigOperators

/--
One petal of the arithmetic bouquet.  The outer coordinate `d` selects the
rose; `u,v` are the coprime modular coordinates on that rose.

This is a state coordinate, not a second numerical value of `S_N`.
The scalar `S_N` is obtained only after contraction over all active states.
-/
structure ModularRoseState where
  d : ℕ
  u : ℕ
  v : ℕ
  d_pos : 0 < d
  u_pos : 0 < u
  v_pos : 0 < v
  coprime : Nat.Coprime u v

/--
Concrete algebraic ingredients of the weighted modular bilinear form.

`coeff N n` represents c_{N,n}.
`vasyunin p q` represents V(p,q).
`far N r` records the frozen FAR selector.
`states N` is the finite collection of active (d,u,v) states.
-/
structure WeightedModularMultiStateData
    (D : WeightedModularBilinearDecayData) where
  coeff : ℕ → ℕ → ℝ
  vasyunin : ℕ → ℕ → ℝ
  far : ℕ → ModularRoseState → Prop
  states : ℕ → Finset ModularRoseState
  state_is_far :
    ∀ N r, r ∈ states N → far N r
  exact_S :
    ∀ N,
      D.S N =
        ∑ r ∈ states N,
          Real.log (N : ℝ) *
            ((1 : ℝ) / (r.d : ℝ)) *
            coeff N (r.d * r.u) *
            coeff N (r.d * r.v) *
            ((vasyunin r.v r.u + vasyunin r.u r.v) /
              ((r.u : ℝ) * (r.v : ℝ)))

/-- The exact contribution of one multi-state petal. -/
def WeightedModularMultiStateData.petal
    {D : WeightedModularBilinearDecayData}
    (M : WeightedModularMultiStateData D)
    (N : ℕ) (r : ModularRoseState) : ℝ :=
  Real.log (N : ℝ) *
    ((1 : ℝ) / (r.d : ℝ)) *
    M.coeff N (r.d * r.u) *
    M.coeff N (r.d * r.v) *
    ((M.vasyunin r.v r.u + M.vasyunin r.u r.v) /
      ((r.u : ℝ) * (r.v : ℝ)))

/-- The bouquet contraction: all roses/petals are contracted to one scalar. -/
def WeightedModularMultiStateData.contract
    {D : WeightedModularBilinearDecayData}
    (M : WeightedModularMultiStateData D)
    (N : ℕ) : ℝ :=
  ∑ r ∈ M.states N, M.petal N r

theorem WeightedModularMultiStateData.contract_eq_S
    {D : WeightedModularBilinearDecayData}
    (M : WeightedModularMultiStateData D)
    (N : ℕ) :
    M.contract N = D.S N := by
  symm
  simpa [WeightedModularMultiStateData.contract,
    WeightedModularMultiStateData.petal] using M.exact_S N

/--
Three-stage status of the frozen reduction.

0 = Gram/norm start;
1 = dyadic + Vasyunin reduction;
2 = weighted modular bilinear endpoint.

The first two stages are representation/transport.  The only material theorem
still required is decay of the stage-2 contraction.
-/
inductive SNStage
  | gramNorm
  | vasyuninReduced
  | weightedModularDecay
  deriving DecidableEq, Repr

def SNStage.code : SNStage → Fin 3
  | .gramNorm => 0
  | .vasyuninReduced => 1
  | .weightedModularDecay => 2

/--
Exact multi-state formulation of the remaining material gap.

This is the requested theorem shape:
there is a nonnegative envelope eps_N -> 0 controlling the contraction of all
(d,u,v) states at once.  It deliberately does not replace the global
cancellation by termwise absolute bounds.
-/
def WeightedModularMultiStateGap
    {D : WeightedModularBilinearDecayData}
    (M : WeightedModularMultiStateData D) : Prop :=
  ∃ eps : ℕ → ℝ,
    (∀ N, 0 ≤ eps N) ∧
    Filter.Tendsto eps Filter.atTop (nhds 0) ∧
    ∀ N, D.N₀ ≤ N → |M.contract N| ≤ eps N

/--
The multi-state theorem-gap is exactly the already frozen
`WEIGHTED_MODULAR_BILINEAR_DECAY` obligation.  No strengthening, weakening,
or extra endpoint is introduced.
-/
theorem weightedModularMultiStateGap_iff_kfarVanishes
    {D : WeightedModularBilinearDecayData}
    (M : WeightedModularMultiStateData D) :
    WeightedModularMultiStateGap M ↔ KFarVanishes D := by
  constructor
  · rintro ⟨eps, hnonneg, heps, hbound⟩
    refine ⟨eps, hnonneg, heps, ?_⟩
    intro N hN
    rw [← M.contract_eq_S N]
    exact hbound N hN
  · rintro ⟨eps, hnonneg, heps, hbound⟩
    refine ⟨eps, hnonneg, heps, ?_⟩
    intro N hN
    rw [M.contract_eq_S N]
    exact hbound N hN

/--
A proof of the exact multi-state contraction theorem produces the unique
material arithmetic-transform witness consumed by the existing pipeline.
-/
def arithmeticTransformData_of_multiStateGap
    {D : WeightedModularBilinearDecayData}
    (M : WeightedModularMultiStateData D)
    (h : WeightedModularMultiStateGap M) :
    ArithmeticTransformData D where
  kfar_vanishes :=
    (weightedModularMultiStateGap_iff_kfarVanishes M).mp h

/--
Exact theorem-level identification of the remaining material producer.

For an exact multistate realization of S_N, proving the global bouquet
contraction bound is equivalent to producing the ArithmeticTransformData
consumed by the frozen downstream chain. Therefore this proposition is not
an auxiliary estimate: it is the material OPEN_MATH certificate itself.
-/
theorem weightedModularMultiStateGap_iff_arithmeticTransformData
    {D : WeightedModularBilinearDecayData}
    (M : WeightedModularMultiStateData D) :
    WeightedModularMultiStateGap M ↔
      Nonempty (ArithmeticTransformData D) := by
  constructor
  · intro h
    exact ⟨arithmeticTransformData_of_multiStateGap M h⟩
  · rintro ⟨A⟩
    exact (weightedModularMultiStateGap_iff_kfarVanishes M).2
      A.kfar_vanishes

/--
Named terminal theorem for the 0 -> 1 -> 2 reduction.

Stage 0 and stage 1 determine the exact scalar contraction S_N. Stage 2 is
closed exactly when its multistate weighted-modular decay certificate exists.
-/
theorem weighted_modular_bilinear_decay_is_exact_gap
    {D : WeightedModularBilinearDecayData}
    (M : WeightedModularMultiStateData D) :
    WeightedModularMultiStateGap M ↔
      KFarVanishes D :=
  weightedModularMultiStateGap_iff_kfarVanishes M

def multiStateGapStatus : String :=
  "OPEN_MATH_CORE: prove global bouquet contraction |S_N| <= eps_N -> 0"

#print axioms WeightedModularMultiStateData.contract_eq_S
#print axioms weightedModularMultiStateGap_iff_kfarVanishes
#print axioms arithmeticTransformData_of_multiStateGap
#print axioms weightedModularMultiStateGap_iff_arithmeticTransformData
#print axioms weighted_modular_bilinear_decay_is_exact_gap

end MCore.RH.NB
