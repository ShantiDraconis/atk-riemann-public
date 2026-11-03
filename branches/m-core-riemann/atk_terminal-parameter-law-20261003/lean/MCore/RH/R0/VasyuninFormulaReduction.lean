import MCore.RH.R0.VasyuninStructural
import MCore.RH.R0.ExplicitGramRate

namespace MCore.RH.R0

/-- Pairwise explicit Gram kernel before matrix packaging. -/
noncomputable def explicitGramEntryNat (p q : ℕ) : ℝ :=
  (1 / (p : ℝ)) *
    fractionalAutocorrelation ((p : ℝ) / (q : ℝ))

/--
The genuine analytic core of Vasyunin's theorem, restricted to coprime positive integers.
-/
def CoprimeVasyuninFormula : Prop :=
  ∀ h k : ℕ,
    0 < h → 0 < k → Nat.Coprime h k →
      explicitGramEntryNat h k = vasyuninGramEntry h k

/--
Pure gcd/scaling layer: both the autocorrelation kernel and the finite cotangent
formula scale by the same factor after extracting d = gcd(p,q).
-/
def VasyuninGCDReduction : Prop :=
  ∀ p q : ℕ,
    0 < p → 0 < q →
      let d := Nat.gcd p q
      let h := p / d
      let k := q / d
      Nat.Coprime h k ∧
      explicitGramEntryNat p q =
        (1 / (d : ℝ)) * explicitGramEntryNat h k ∧
      vasyuninGramEntry p q =
        (1 / (d : ℝ)) * vasyuninGramEntry h k

/-- Coprime core plus gcd scaling yields the full finite Vasyunin Gram formula. -/
theorem vasyuninGramFormula_of_coprime_and_gcd
    (hcop : CoprimeVasyuninFormula)
    (hred : VasyuninGCDReduction) :
    VasyuninGramFormula := by
  intro N
  ext i j
  let p := rhoIndex i
  let q := rhoIndex j
  have hp : 0 < p := rhoIndex_pos i
  have hq : 0 < q := rhoIndex_pos j
  obtain ⟨hcoprime, hexp, hvas⟩ := hred p q hp hq
  let d := Nat.gcd p q
  let h := p / d
  let k := q / d
  have hcore : explicitGramEntryNat h k = vasyuninGramEntry h k :=
    hcop h k
      (by
        dsimp [h, d]
        exact Nat.div_pos (Nat.gcd_pos_of_pos_left q hp) (Nat.gcd_le_left q hp))
      (by
        dsimp [k, d]
        exact Nat.div_pos (Nat.gcd_pos_of_pos_right p hq) (Nat.gcd_le_right p hq))
      hcoprime
  change explicitGramEntryNat p q = vasyuninGramEntry p q
  calc
    explicitGramEntryNat p q
        = (1 / (d : ℝ)) * explicitGramEntryNat h k := hexp
    _ = (1 / (d : ℝ)) * vasyuninGramEntry h k := by rw [hcore]
    _ = vasyuninGramEntry p q := hvas.symm

#print axioms MCore.RH.R0.vasyuninGramFormula_of_coprime_and_gcd

end MCore.RH.R0
