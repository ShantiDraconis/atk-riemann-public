import MCore.RH.R0.LinearIndependentReduction
import MCore.RH.R0.RhoBasicFacts

open scoped BigOperators

namespace MCore.RH.R0

open MeasureTheory

/-- The frozen concrete generator has the literal rhoRepresentative as an a.e. representative. -/
theorem concreteGeneratorFamily_coeFn_ae (n : ℕ) :
    ((show ConcreteH from concreteGeneratorFamily n) : ℝ → ℝ) =ᵐ[zeroInfinityMeasure]
      rhoRepresentative n := by
  simpa [concreteGeneratorFamily, concreteNBData, ConcreteH, twoExponent, rhoLp] using
    (rho_memLp_two n).coeFn_toLp

/--
The finite Hilbert-space combination is represented almost everywhere by
the literal finite sum of the frozen rho representatives.
-/
theorem concreteFiniteCombination_coeFn_ae
    {N : ℕ} (c : Fin N → ℝ) :
    ((show ConcreteH from concreteFiniteCombination c) : ℝ → ℝ) =ᵐ[zeroInfinityMeasure]
      (fun x : ℝ => ∑ i : Fin N, c i * rhoRepresentative i x) := by
  classical
  have hsum : ∀ S : Finset (Fin N),
      ((show ConcreteH from ∑ i ∈ S, c i • concreteGeneratorFamily i) : ℝ → ℝ)
        =ᵐ[zeroInfinityMeasure]
      (fun x : ℝ => ∑ i ∈ S, c i * rhoRepresentative i x) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        exact Lp.coeFn_zero ℝ (2 : ENNReal) zeroInfinityMeasure
    | @insert a S ha ih =>
        filter_upwards [
          Lp.coeFn_add
            (c a • concreteGeneratorFamily a)
            (∑ i ∈ S, c i • concreteGeneratorFamily i),
          Lp.coeFn_smul (c a) (concreteGeneratorFamily a),
          concreteGeneratorFamily_coeFn_ae a,
          ih] with x hadd hsmul hgen hrest
        simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply] at *
        rw [hadd, hsmul, hgen, hrest]
        simp [smul_eq_mul, add_comm]
  change
    ((show ConcreteH from ∑ i : Fin N, c i • concreteGeneratorFamily i) : ℝ → ℝ)
      =ᵐ[zeroInfinityMeasure]
    (fun x : ℝ => ∑ i : Fin N, c i * rhoRepresentative i x)
  exact hsum Finset.univ

/-- A1.0: zero in Lp implies the literal finite rho combination vanishes a.e. -/
theorem concreteFiniteCombination_eq_zero_ae
    {N : ℕ} (c : Fin N → ℝ)
    (h : concreteFiniteCombination c = 0) :
    (fun x : ℝ => ∑ i : Fin N, c i * rhoRepresentative i x)
      =ᵐ[zeroInfinityMeasure] 0 := by
  have h' : (show ConcreteH from concreteFiniteCombination c) = 0 := by
    simpa [concreteNBData, ConcreteH] using h
  have hcarrier :
      ((show ConcreteH from concreteFiniteCombination c) : ℝ → ℝ)
        =ᵐ[zeroInfinityMeasure] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp h'
  exact (concreteFiniteCombination_coeFn_ae c).symm.trans hcarrier

#print axioms MCore.RH.R0.concreteGeneratorFamily_coeFn_ae
#print axioms MCore.RH.R0.concreteFiniteCombination_coeFn_ae
#print axioms MCore.RH.R0.concreteFiniteCombination_eq_zero_ae

end MCore.RH.R0
