import MCore.RH.R0.ExplicitGramRate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

open scoped BigOperators

namespace MCore.RH.R0

/--
Finite Vasyunin cotangent sum. The m=0 term is included for convenient Finset.range
indexing and is zero.
-/
noncomputable def vasyuninSum (h k : ℕ) : ℝ :=
  ∑ m in Finset.range k,
    Int.fract (((m * h : ℕ) : ℝ) / (k : ℝ)) *
      Real.cot (Real.pi * (m : ℝ) / (k : ℝ))

/-- Reduced numerator of p/q. -/
def reducedNumerator (p q : ℕ) : ℕ :=
  p / Nat.gcd p q

/-- Reduced denominator of p/q. -/
def reducedDenominator (p q : ℕ) : ℕ :=
  q / Nat.gcd p q

/--
The finite Vasyunin closed form for the weighted Gram entry
∫₀∞ {t/p}{t/q} dt/t².
For non-coprime p,q the reduced cotangent pair is multiplied by gcd(p,q).
-/
noncomputable def vasyuninGramEntry (p q : ℕ) : ℝ :=
  let d := Nat.gcd p q
  let h := reducedNumerator p q
  let k := reducedDenominator p q
  ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2) *
      (1 / (p : ℝ) + 1 / (q : ℝ))
    + ((p : ℝ) - (q : ℝ)) / (2 * (p : ℝ) * (q : ℝ)) *
        Real.log ((q : ℝ) / (p : ℝ))
    - Real.pi * (d : ℝ) / (2 * (p : ℝ) * (q : ℝ)) *
        (vasyuninSum k h + vasyuninSum h k)

/-- Finite-sum Gram matrix obtained from the Vasyunin formula. -/
noncomputable def vasyuninGramMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => vasyuninGramEntry (rhoIndex i) (rhoIndex j)

/--
Exact classical identity still to be kernel-formalized:
our autocorrelation Gram matrix equals the finite Vasyunin cotangent formula.
-/
def VasyuninGramFormula : Prop :=
  ∀ N : ℕ, explicitGramMatrix N = vasyuninGramMatrix N

/-- Once Vasyunin's identity is formalized, the explicit inverse-Gram residual
can be rewritten with a genuinely finite arithmetic matrix. -/
theorem explicitGramResidual_eq_vasyunin
    (hV : VasyuninGramFormula) (N : ℕ) :
    explicitGramResidual N =
      1 - dotProduct (explicitTargetVector N)
        ((vasyuninGramMatrix N)⁻¹ *ᵥ explicitTargetVector N) := by
  unfold explicitGramResidual explicitOptimalCoeff
  rw [hV N]

/-- H1 after eliminating the autocorrelation integral completely. -/
def FiniteVasyuninRateTarget : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ,
      1 - dotProduct (explicitTargetVector N)
        ((vasyuninGramMatrix N)⁻¹ *ᵥ explicitTargetVector N) ≤
          logMajorant K N

theorem finiteVasyuninRateTarget_iff_explicitGramRate
    (hV : VasyuninGramFormula) :
    FiniteVasyuninRateTarget ↔ ExplicitGramRateTarget := by
  constructor
  · rintro ⟨K, hK, hbound⟩
    refine ⟨K, hK, ?_⟩
    intro N
    rw [explicitGramResidual_eq_vasyunin hV N]
    exact hbound N
  · rintro ⟨K, hK, hbound⟩
    refine ⟨K, hK, ?_⟩
    intro N
    rw [explicitGramResidual_eq_vasyunin hV N] at hbound
    exact hbound N

#print axioms MCore.RH.R0.explicitGramResidual_eq_vasyunin
#print axioms MCore.RH.R0.finiteVasyuninRateTarget_iff_explicitGramRate

end MCore.RH.R0
