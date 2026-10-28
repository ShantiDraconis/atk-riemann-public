import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

namespace MCore

/-!
# T7 deterministic rejection-zero invariant probe

Autocontained on Mathlib's `riemannZeta`.  This file intentionally avoids the
older K9 bridge so the rejection-zero probe can be kernel-tested independently.

Two reflections are kept distinct:

* `functionalReflect s = 1 - s`.
* `criticalReflect s = (1 - re s) + i (im s)`, i.e. reflection across Re(s)=1/2.

No theorem below derives orbit collapse from symmetry.
-/

def functionalReflect (s : ℂ) : ℂ := 1 - s

def criticalReflect (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩

noncomputable def observedDefect (s : ℂ) : ℝ :=
  s.re - (1 / 2 : ℝ)

theorem functionalReflect_involutive (s : ℂ) :
    functionalReflect (functionalReflect s) = s := by
  simp [functionalReflect]

theorem criticalReflect_involutive (s : ℂ) :
    criticalReflect (criticalReflect s) = s := by
  apply Complex.ext <;> simp [criticalReflect]

theorem observedDefect_functionalReflect (s : ℂ) :
    observedDefect (functionalReflect s) = - observedDefect s := by
  simp [observedDefect, functionalReflect]
  ring

theorem observedDefect_criticalReflect (s : ℂ) :
    observedDefect (criticalReflect s) = - observedDefect s := by
  simp [observedDefect, criticalReflect]
  ring

/-- Reflection across the critical line fixes exactly Re(s)=1/2. -/
theorem criticalReflect_fixed_iff (s : ℂ) :
    criticalReflect s = s ↔ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp [criticalReflect] at hr
    linarith
  · intro h
    apply Complex.ext
    · simp [criticalReflect]
      linarith
    · simp [criticalReflect]

theorem criticalReflect_preserves_im (s : ℂ) :
    (criticalReflect s).im = s.im := by
  simp [criticalReflect]

theorem criticalReflect_preserves_defect_abs (s : ℂ) :
    |observedDefect (criticalReflect s)| = |observedDefect s| := by
  rw [observedDefect_criticalReflect]
  exact abs_neg _

/-! Negative control: involution + sign flip does not imply zero defect. -/

structure ToyReflectionModel where
  Point : Type
  reflect : Point → Point
  defect : Point → ℝ
  reflect_reflect : ∀ x, reflect (reflect x) = x
  defect_reflect : ∀ x, defect (reflect x) = - defect x

def toyOffLine : ToyReflectionModel where
  Point := ℝ
  reflect := fun x => -x
  defect := id
  reflect_reflect := by
    intro x
    simp
  defect_reflect := by
    intro x
    rfl

theorem involution_and_flip_do_not_force_zero_defect :
    ∃ (M : ToyReflectionModel) (x : M.Point), M.defect x ≠ 0 := by
  refine ⟨toyOffLine, ?_⟩
  refine ⟨(1 : ℝ), ?_⟩
  change (1 : ℝ) ≠ 0
  norm_num

/-!
Local zero predicate used only to expose the structural endpoint without
depending on the broken historical K9 import surface.
-/

def ProbeNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
  (¬ ∃ n : ℕ, s = -(((2 * (n + 1) : ℕ) : ℂ))) ∧
  s ≠ 1

def ProbeCriticalLineStatement : Prop :=
  ∀ s : ℂ, ProbeNontrivialZetaZero s → s.re = (1 / 2 : ℝ)


/-- Q1 reduced exactly to Mathlib's side condition excluding negative naturals. -/
theorem functionalReflect_zero_closed_of_not_neg_nat
    {s : ℂ}
    (hz : riemannZeta s = 0)
    (hneg : ∀ n : ℕ, s ≠ -(n : ℂ))
    (h1 : s ≠ 1) :
    riemannZeta (functionalReflect s) = 0 := by
  rw [functionalReflect, riemannZeta_one_sub hneg h1, hz, mul_zero]


/-- Q3a: nonvanishing of ζ(2k) forces the corresponding even Bernoulli number to be nonzero. -/
theorem bernoulli_two_mul_ne_zero_of_zeta
    {k : ℕ} (hk : k ≠ 0)
    (hz : riemannZeta (2 * k) ≠ 0) :
    bernoulli (2 * k) ≠ 0 := by
  intro hB
  apply hz
  rw [riemannZeta_two_mul_nat hk, hB]
  simp

/-- Q3b: every negative odd integer is a nonzero point of ζ, once the matching
positive even zeta value is known to be nonzero. -/
theorem riemannZeta_neg_odd_ne_zero_of_pos_even
    (m : ℕ)
    (hzpos : riemannZeta (((2 * (m + 1) : ℕ) : ℂ)) ≠ 0) :
    riemannZeta (-((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by
  have hzpos' : riemannZeta (2 * (((m + 1 : ℕ) : ℂ))) ≠ 0 := by
    simpa [Nat.cast_add] using hzpos
  have hB : bernoulli (2 * (m + 1)) ≠ 0 :=
    bernoulli_two_mul_ne_zero_of_zeta (k := m + 1) (by omega) hzpos'
  rw [riemannZeta_neg_nat_eq_bernoulli (2 * m + 1)]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      simpa [hidx] using hB
  · have hn : (2 * m + 2 : ℕ) ≠ 0 := by omega
    have hc : (((2 * m + 2 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast hn
    convert hc using 1 <;> norm_num [Nat.cast_add, Nat.cast_mul] <;> ring


/-- The exact orbit-collapse obligation that symmetry alone does not provide. -/
def CriticalOrbitCollapse : Prop :=
  ∀ s : ℂ, ProbeNontrivialZetaZero s → criticalReflect s = s

theorem criticalOrbitCollapse_implies_probeCriticalLine
    (h : CriticalOrbitCollapse) :
    ProbeCriticalLineStatement := by
  intro s hs
  exact (criticalReflect_fixed_iff s).mp (h s hs)

/-!
Kernel frontier:

Q1. zero-closure under functionalReflect.
Q2. zero-closure under criticalReflect, using functional + conjugation symmetry.
Q3. exact side conditions at poles/trivial zeros.
Q4. involution, sign flip and |defect|-preservation are structural only.
Q5-Q9. none may be promoted to orbit collapse.
Q10. expose the first independent material law that implies CriticalOrbitCollapse.
-/

end MCore
