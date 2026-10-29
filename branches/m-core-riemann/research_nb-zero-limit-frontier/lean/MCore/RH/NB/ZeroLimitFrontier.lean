import MCore.RH.NB.Limit

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- The genuine zero-defect convergence proposition. This is a definition, not an assumption. -/
def DNToZero (rho : D.GeneratorFamily) : Prop :=
  Filter.Tendsto (D.DN rho) Filter.atTop (nhds 0)

/-- For the already-certified convergent defect sequence, convergence to zero is
exactly the statement that its canonical limit is zero. -/
theorem DNToZero_iff_DNLimit_eq_zero (rho : D.GeneratorFamily) :
    D.DNToZero rho ↔ D.DNLimit rho = 0 := by
  constructor
  · intro hzero
    exact tendsto_nhds_unique (D.tendsto_DN_DNLimit rho) hzero
  · intro hlim
    unfold DNToZero
    simpa [hlim] using D.tendsto_DN_DNLimit rho


/-- Exact geometric content behind zero defect: the distinguished target can be
approximated arbitrarily well by one of the finite generator spans.  This is
the material density statement; no density assumption is built into
`GeneratorFamily`. -/
def FiniteSpanApproximatesChi (rho : D.GeneratorFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∃ v : D.V rho N,
      ‖D.chi - (v : D.H)‖ < ε

/-- Union of all finite generator spans, viewed as an ambient subset. -/
def FiniteSpanUnion (rho : D.GeneratorFamily) : Set D.H :=
  {x : D.H | ∃ N : ℕ, x ∈ D.V rho N}

/-- The epsilon-approximation formulation is exactly closure membership of the
    distinguished target in the union of finite spans. -/
theorem finiteSpanApproximatesChi_iff_mem_closure
    (rho : D.GeneratorFamily) :
    D.FiniteSpanApproximatesChi rho ↔
      D.chi ∈ closure (D.FiniteSpanUnion rho) := by
  constructor
  · intro happrox
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases happrox ε hε with ⟨N, v, hv⟩
    refine ⟨(v : D.H), ?_, ?_⟩
    · exact ⟨N, v.property⟩
    · simpa [dist_eq_norm] using hv
  · intro hclosure ε hε
    rw [Metric.mem_closure_iff] at hclosure
    rcases hclosure ε hε with ⟨v, hv, hdist⟩
    rcases hv with ⟨N, hvN⟩
    refine ⟨N, ⟨v, hvN⟩, ?_⟩
    simpa [dist_eq_norm] using hdist

/-- Full density of the finite-span union is stronger than needed, but
    immediately supplies the target-specific approximation property. -/
theorem finiteSpanApproximatesChi_of_dense
    (rho : D.GeneratorFamily)
    (hdense : Dense (D.FiniteSpanUnion rho)) :
    D.FiniteSpanApproximatesChi rho := by
  apply (D.finiteSpanApproximatesChi_iff_mem_closure rho).2
  exact hdense D.chi

/-- Arbitrary finite-span approximation forces the canonical defect infimum to
be zero.  The proof uses only projection minimality, nonnegativity, and the
definition of the infimum. -/
theorem DNLimit_eq_zero_of_finiteSpanApproximatesChi
    (rho : D.GeneratorFamily)
    (happrox : D.FiniteSpanApproximatesChi rho) :
    D.DNLimit rho = 0 := by
  apply le_antisymm ?_ (D.DNLimit_nonneg rho)
  by_contra hnot
  have hpos : 0 < D.DNLimit rho := lt_of_not_ge hnot
  have hsqrtpos : 0 < Real.sqrt (D.DNLimit rho) := Real.sqrt_pos.2 hpos
  rcases happrox (Real.sqrt (D.DNLimit rho)) hsqrtpos with
    ⟨N, v, hv⟩
  have hb :
      BddBelow
        (Set.range
          (fun w : D.V rho N => ‖D.chi - (w : D.H)‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _
  have hproj :
      D.dN rho N ≤ ‖D.chi - (v : D.H)‖ := by
    unfold dN
    rw [D.P_minimal rho N D.chi]
    exact ciInf_le hb v
  have hdlt :
      D.dN rho N < Real.sqrt (D.DNLimit rho) :=
    lt_of_le_of_lt hproj hv
  have hdnnonneg : 0 ≤ D.dN rho N :=
    D.dN_nonneg rho N
  have hsum :
      0 < Real.sqrt (D.DNLimit rho) + D.dN rho N := by
    nlinarith
  have hprod :
      0 <
        (Real.sqrt (D.DNLimit rho) - D.dN rho N) *
          (Real.sqrt (D.DNLimit rho) + D.dN rho N) :=
    mul_pos (sub_pos.mpr hdlt) hsum
  have hsqrtsq :
      (Real.sqrt (D.DNLimit rho)) ^ 2 = D.DNLimit rho :=
    Real.sq_sqrt (le_of_lt hpos)
  have hDNlt :
      D.DN rho N < D.DNLimit rho := by
    unfold DN
    nlinarith
  have hinf :
      D.DNLimit rho ≤ D.DN rho N := by
    unfold DNLimit
    exact ciInf_le (D.DN_bddBelow rho) N
  linarith

/-- The same geometric approximation closes the zero-limit frontier. -/
theorem DNToZero_of_finiteSpanApproximatesChi
    (rho : D.GeneratorFamily)
    (happrox : D.FiniteSpanApproximatesChi rho) :
    D.DNToZero rho := by
  apply (D.DNToZero_iff_DNLimit_eq_zero rho).2
  exact D.DNLimit_eq_zero_of_finiteSpanApproximatesChi rho happrox

/-- A pointwise zero upper bound forces the zero-limit frontier. This theorem is
pure order logic and does not provide such a bound. -/
theorem DNToZero_of_le_zero (rho : D.GeneratorFamily)
    (hupper : ∀ N : ℕ, D.DN rho N ≤ 0) : D.DNToZero rho := by
  have hzero : D.DN rho = fun _ : ℕ => (0 : ℝ) := by
    funext N
    exact le_antisymm (hupper N) (D.DN_nonneg rho N)
  unfold DNToZero
  rw [hzero]
  exact tendsto_const_nhds

end NBHilbertData
end MCore.RH.NB
