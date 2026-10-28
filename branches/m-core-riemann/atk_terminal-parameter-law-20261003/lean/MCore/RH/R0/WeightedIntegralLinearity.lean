import MCore.RH.R0.WeightedIntegrability

open scoped BigOperators

namespace MCore.RH.R0

open MeasureTheory Set

/-- A1.2: finite weighted rho sums commute with the set integral on (0,∞). -/
theorem weighted_integral_finset_linearity
    {N : ℕ} (c : Fin N → ℝ) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ x : ℝ in Ioi 0,
      (∑ i : Fin N, c i * rhoRepresentative i x) * x ^ (s - 1)) =
    ∑ i : Fin N, c i *
      (∫ x : ℝ in Ioi 0, rhoRepresentative i x * x ^ (s - 1)) := by
  have hint : ∀ i : Fin N,
      IntegrableOn
        (fun x : ℝ => c i * (rhoRepresentative i x * x ^ (s - 1)))
        (Ioi 0) volume := by
    intro i
    exact (rho_weighted_integrableOn_Ioi i s hs0 hs1).const_mul (c i)
  calc
    (∫ x : ℝ in Ioi 0,
      (∑ i : Fin N, c i * rhoRepresentative i x) * x ^ (s - 1))
        = ∫ x : ℝ in Ioi 0,
            ∑ i : Fin N, c i *
              (rhoRepresentative i x * x ^ (s - 1)) := by
              apply integral_congr_ae
              filter_upwards with x
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring_nf
    _ = ∑ i : Fin N,
          ∫ x : ℝ in Ioi 0,
            c i * (rhoRepresentative i x * x ^ (s - 1)) := by
          exact integral_finset_sum Finset.univ (by
            intro i hi
            exact hint i)
    _ = ∑ i : Fin N, c i *
          (∫ x : ℝ in Ioi 0, rhoRepresentative i x * x ^ (s - 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact integral_const_mul _ _

#print axioms MCore.RH.R0.weighted_integral_finset_linearity

end MCore.RH.R0
