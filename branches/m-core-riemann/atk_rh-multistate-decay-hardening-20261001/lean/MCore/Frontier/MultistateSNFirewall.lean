import MCore.Frontier.MultistateSN

namespace MCore.RiemannMultistate

/--
Counteraudit: the legacy `WeightedModularBilinearDecay` interface is too weak
to represent analytic decay because `vanishes` is an arbitrary proposition
with no relation to `sequence`.
-/
def trivialWeightedDecay
    {Scalar : Type}
    (s : Nat → Scalar) :
    WeightedModularBilinearDecay Scalar where
  sequence := s
  vanishes := True
  proof := trivial

theorem every_sequence_has_legacy_weighted_decay
    {Scalar : Type}
    (s : Nat → Scalar) :
    Nonempty (WeightedModularBilinearDecay Scalar) :=
  ⟨trivialWeightedDecay s⟩

/--
Hence the existence of the legacy decay object alone cannot certify any
analytic vanishing statement about S_N.
-/
theorem legacy_decay_is_structurally_trivial
    {Scalar : Type}
    (s : Nat → Scalar) :
    ∃ d : WeightedModularBilinearDecay Scalar,
      d.sequence = s := by
  exact ⟨trivialWeightedDecay s, rfl⟩

/--
Hardened scalar decay package.  For real-valued S_N the certificate now
contains the actual quantitative statement `S_N → 0`.
-/
structure RealWeightedModularBilinearDecay where
  sequence : Nat → ℝ
  tendsto_zero :
    Filter.Tendsto sequence Filter.atTop (nhds 0)

/--
A pointwise vanishing majorant is sufficient for the hardened decay package.
This is a genuine analytic condition rather than arbitrary metadata.
-/
def RealWeightedModularBilinearDecay.ofMajorant
    (S eps : Nat → ℝ)
    (hSnonneg : ∀ N, 0 ≤ |S N|)
    (hBound : ∀ N, |S N| ≤ eps N)
    (hEpsNonneg : ∀ N, 0 ≤ eps N)
    (hEpsZero : Filter.Tendsto eps Filter.atTop (nhds 0)) :
    RealWeightedModularBilinearDecay := by
  refine { sequence := S, tendsto_zero := ?_ }
  have hAbsZero :
      Filter.Tendsto (fun N => |S N|) Filter.atTop (nhds 0) := by
    have hzero :
        Filter.Tendsto (fun _ : Nat => (0 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds
    exact squeeze_zero'
      (Filter.Eventually.of_forall hSnonneg)
      (Filter.Eventually.of_forall hBound)
      hEpsZero
  exact (tendsto_zero_iff_norm_tendsto_zero).2 (by simpa [Real.norm_eq_abs] using hAbsZero)

#print axioms MCore.RiemannMultistate.every_sequence_has_legacy_weighted_decay
#print axioms MCore.RiemannMultistate.legacy_decay_is_structurally_trivial
#print axioms MCore.RiemannMultistate.RealWeightedModularBilinearDecay.ofMajorant

end MCore.RiemannMultistate
