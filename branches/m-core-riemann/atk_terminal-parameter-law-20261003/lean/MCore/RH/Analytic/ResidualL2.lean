import MCore.RH.Analytic.LogPullbackL2
import MCore.RH.R0.ChiMemLp
import MCore.RH.R0.RhoBasicFacts
import Mathlib.MeasureTheory.Function.L2Space

open scoped BigOperators

namespace MCore.RH.R0

open MeasureTheory Set

/-- Complexified target remains in L2. -/
theorem chiRepresentativeC_memLp_two :
    MemLp chiRepresentativeC 2 zeroInfinityMeasure := by
  simpa [chiRepresentativeC] using
    (chi_memLp_two.ofReal :
      MemLp (fun x : ℝ => (chiRepresentative x : ℂ)) 2 zeroInfinityMeasure)

/-- Every complexified rho generator remains in L2. -/
theorem rhoRepresentativeC_memLp_two (n : ℕ) :
    MemLp (rhoRepresentativeC n) 2 zeroInfinityMeasure := by
  simpa [rhoRepresentativeC] using
    (rhoRepresentative_memLp_two_public n).ofReal

/-- Finite complex rho combinations belong to L2. -/
theorem rhoCombinationC_memLp_two
    {N : ℕ} (c : Fin N → ℝ) :
    MemLp (rhoCombinationC c) 2 zeroInfinityMeasure := by
  classical
  unfold rhoCombinationC
  induction (Finset.univ : Finset (Fin N)) using Finset.induction_on with
  | empty =>
      simpa using (memLp_zero : MemLp (0 : ℝ → ℂ) 2 zeroInfinityMeasure)
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact ((rhoRepresentativeC_memLp_two a).const_smul (c a : ℂ)).add ih

/-- The complex residual belongs to the frozen L2 carrier. -/
theorem residualRepresentativeC_memLp_two
    {N : ℕ} (c : Fin N → ℝ) :
    MemLp (residualRepresentativeC c) 2 zeroInfinityMeasure := by
  unfold residualRepresentativeC
  exact chiRepresentativeC_memLp_two.sub (rhoCombinationC_memLp_two c)

/-- Square norm of the residual representative is integrable on the positive half-line. -/
theorem residual_normSq_integrable
    {N : ℕ} (c : Fin N → ℝ) :
    IntegrableOn
      (fun x : ℝ => ‖residualRepresentativeC c x‖ ^ 2)
      (Ioi 0) := by
  have h := residualRepresentativeC_memLp_two c
  rw [memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable] at h
  simpa [zeroInfinityMeasure] using h

/-- Literal measurability of the complex residual. -/
theorem residualRepresentativeC_measurable
    {N : ℕ} (c : Fin N → ℝ) :
    Measurable (residualRepresentativeC c) := by
  classical
  unfold residualRepresentativeC rhoCombinationC chiRepresentativeC rhoRepresentativeC
  apply Measurable.sub
  · exact chiRepresentative_measurable.ofReal
  · exact Finset.measurable_sum _ (fun i _ =>
      Measurable.mul measurable_const
        ((rhoRepresentative_measurable_public i).ofReal))

/-- The logarithmic pullback is measurable on the real line. -/
theorem residual_logPullback_measurable
    {N : ℕ} (c : Fin N → ℝ) :
    Measurable (logPullback (residualRepresentativeC c)) := by
  unfold logPullback
  apply Measurable.smul
  · exact (Real.measurable_exp.comp (measurable_id.neg.div_const 2))
  · exact (residualRepresentativeC_measurable c).comp
      (Real.measurable_exp.comp measurable_id.neg)

/-- Square norm of the logarithmic pullback is integrable. -/
theorem residual_logPullback_normSq_integrable
    {N : ℕ} (c : Fin N → ℝ) :
    Integrable
      (fun u : ℝ => ‖logPullback (residualRepresentativeC c) u‖ ^ 2)
      volume := by
  let g : ℝ → ℝ := fun x => ‖residualRepresentativeC c x‖ ^ 2
  have hg : IntegrableOn g (Ioi 0) := by
    simpa [g] using residual_normSq_integrable c
  have hexp :
      Integrable (fun u : ℝ => Real.exp u * g (Real.exp u)) volume := by
    simpa [smul_eq_mul] using (integrable_comp_exp g).2 hg
  have hneg :
      Integrable
        ((fun u : ℝ => Real.exp u * g (Real.exp u)) ∘ fun u : ℝ => -u)
        volume :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hexp
  apply Integrable.congr hneg
  exact Eventually.of_forall (fun u => by
    unfold Function.comp g logPullback
    simp only [neg_neg, Real.norm_eq_abs, norm_smul]
    rw [abs_of_pos (Real.exp_pos _)]
    rw [show - (u / 2) = (-u) / 2 by ring]
    rw [sq, mul_assoc, ← Real.exp_add]
    congr 1
    ring)

/-- The logarithmic pullback of the residual is L2 on the full real line. -/
theorem residual_logPullback_memLp_two
    {N : ℕ} (c : Fin N → ℝ) :
    MemLp (logPullback (residualRepresentativeC c)) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm
    (residual_logPullback_measurable c).aestronglyMeasurable]
  exact residual_logPullback_normSq_integrable c

#print axioms MCore.RH.R0.residualRepresentativeC_memLp_two
#print axioms MCore.RH.R0.residual_logPullback_memLp_two

end MCore.RH.R0
