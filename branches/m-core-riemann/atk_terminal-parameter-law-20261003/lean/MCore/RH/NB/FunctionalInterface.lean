import MCore.RH.NB.A14NonImplication

namespace MCore.RH.NB

structure FunctionalCarrier where
  State : Type
  zero : State
  ampAction : ℝ → State → State
  scaleAction : ℝ → State → State
  testAt : ℕ → State
  defectAt : ℕ → ℝ
  coveringAt : ℕ → ℝ

/-- Observational compatibility is data-bearing: it contains witnesses and an
observation map, so it lives in `Type`, not `Prop`. -/
structure FunctionalCompatibility (sys : MCoreSystem) (F : FunctionalCarrier) where
  amplitudeWitness : ℝ → F.State
  scaleWitness : ℝ → F.State
  observe : F.State → ℝ
  amplitude_agrees : ∀ A, observe (F.ampAction A (amplitudeWitness A)) = sys.amplitude A
  scale_agrees : ∀ s, observe (F.scaleAction s (scaleWitness s)) = sys.scale s

def CoveringDecay (F : FunctionalCarrier) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → |F.coveringAt N| < eps

def TestDefectDecay (F : FunctionalCarrier) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → |F.defectAt N| < eps

def zeroCarrier (sys : MCoreSystem) : FunctionalCarrier where
  State := ℝ
  zero := 0
  ampAction := fun A _ => sys.amplitude A
  scaleAction := fun s _ => sys.scale s
  testAt := fun _ => 0
  defectAt := fun _ => 0
  coveringAt := fun _ => 0

def zeroCompatibility (sys : MCoreSystem) : FunctionalCompatibility sys (zeroCarrier sys) where
  amplitudeWitness := fun _ => (zeroCarrier sys).zero
  scaleWitness := fun _ => (zeroCarrier sys).zero
  observe := id
  amplitude_agrees := by intro A; rfl
  scale_agrees := by intro s; rfl

theorem zeroCarrier_covering_decay (sys : MCoreSystem) : CoveringDecay (zeroCarrier sys) := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _hN
  simpa [zeroCarrier] using heps

theorem zeroCarrier_testDefect_decay (sys : MCoreSystem) : TestDefectDecay (zeroCarrier sys) := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _hN
  simpa [zeroCarrier] using heps

def oneCarrier (sys : MCoreSystem) : FunctionalCarrier where
  State := ℝ
  zero := 0
  ampAction := fun A _ => sys.amplitude A
  scaleAction := fun s _ => sys.scale s
  testAt := fun _ => 0
  defectAt := fun _ => 1
  coveringAt := fun _ => 1

def oneCompatibility (sys : MCoreSystem) : FunctionalCompatibility sys (oneCarrier sys) where
  amplitudeWitness := fun _ => (oneCarrier sys).zero
  scaleWitness := fun _ => (oneCarrier sys).zero
  observe := id
  amplitude_agrees := by intro A; rfl
  scale_agrees := by intro s; rfl

theorem oneCarrier_not_covering_decay (sys : MCoreSystem) : ¬ CoveringDecay (oneCarrier sys) := by
  intro h
  obtain ⟨N0, hN0⟩ := h (1 / 2 : ℝ) (by norm_num)
  have hlt := hN0 N0 (le_refl N0)
  norm_num [oneCarrier] at hlt

theorem oneCarrier_not_testDefect_decay (sys : MCoreSystem) : ¬ TestDefectDecay (oneCarrier sys) := by
  intro h
  obtain ⟨N0, hN0⟩ := h (1 / 2 : ℝ) (by norm_num)
  have hlt := hN0 N0 (le_refl N0)
  norm_num [oneCarrier] at hlt

/-- Compatibility of the action/observation data alone does not constrain the
covering sequence. This is an interface-separation theorem, not an NB theorem. -/
theorem compatibility_alone_not_sufficient_for_covering :
    ¬ (∀ F : FunctionalCarrier,
        FunctionalCompatibility witnessSystem F → CoveringDecay F) := by
  intro h
  exact oneCarrier_not_covering_decay witnessSystem
    (h (oneCarrier witnessSystem) (oneCompatibility witnessSystem))

/-- Compatibility of the action/observation data alone does not constrain the
defect sequence. This is an interface-separation theorem, not an NB theorem. -/
theorem compatibility_alone_not_sufficient_for_testDefect :
    ¬ (∀ F : FunctionalCarrier,
        FunctionalCompatibility witnessSystem F → TestDefectDecay F) := by
  intro h
  exact oneCarrier_not_testDefect_decay witnessSystem
    (h (oneCarrier witnessSystem) (oneCompatibility witnessSystem))

end MCore.RH.NB