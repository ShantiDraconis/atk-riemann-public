namespace MCore.RH.NB.Functional

universe u

variable {F : Type u}
variable (L P : F → Prop)

def Sufficient : Prop := ∀ f : F, L f → P f

def Necessary : Prop := ∀ f : F, P f → L f

def StrictlyStronger : Prop :=
  Sufficient L P ∧ ∃ f : F, P f ∧ ¬ L f

def StrictlyWeaker : Prop :=
  Necessary L P ∧ ∃ f : F, L f ∧ ¬ P f

def Equivalent : Prop :=
  Sufficient L P ∧ Necessary L P

theorem sufficient_of_equivalent (h : Equivalent L P) : Sufficient L P := h.1

theorem necessary_of_equivalent (h : Equivalent L P) : Necessary L P := h.2

theorem strictlyStronger_implies_sufficient
    (h : StrictlyStronger L P) : Sufficient L P := h.1

theorem not_necessary_of_strictlyStronger
    (h : StrictlyStronger L P) : ¬ Necessary L P := by
  intro hNec
  obtain ⟨f, hP, hNotL⟩ := h.2
  exact hNotL (hNec f hP)

theorem strictlyWeaker_implies_necessary
    (h : StrictlyWeaker L P) : Necessary L P := h.1

theorem not_sufficient_of_strictlyWeaker
    (h : StrictlyWeaker L P) : ¬ Sufficient L P := by
  intro hSuf
  obtain ⟨f, hL, hNotP⟩ := h.2
  exact hNotP (hSuf f hL)

theorem strictlyStronger_not_equivalent
    (h : StrictlyStronger L P) : ¬ Equivalent L P := by
  intro hEq
  exact not_necessary_of_strictlyStronger L P h hEq.2

theorem strictlyWeaker_not_equivalent
    (h : StrictlyWeaker L P) : ¬ Equivalent L P := by
  intro hEq
  exact not_sufficient_of_strictlyWeaker L P h hEq.1

end MCore.RH.NB.Functional
