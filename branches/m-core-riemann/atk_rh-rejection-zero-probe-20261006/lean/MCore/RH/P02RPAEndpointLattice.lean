import MCore.RH.P02RPADualCertificate

namespace MCore

/-!
# RPA endpoint lattice

Raw states retain OPEN/CLOSED multiplicities. Canonical states quotient by
idempotence, yielding exactly four endpoint configurations.
-/

structure RPARawMultiplicity where
  openCount : Nat
  closedCount : Nat
  deriving DecidableEq, Repr

def rawEmpty : RPARawMultiplicity := ⟨0, 0⟩
def rawOpen : RPARawMultiplicity := ⟨1, 0⟩
def rawClosed : RPARawMultiplicity := ⟨0, 1⟩
def rawDual : RPARawMultiplicity := ⟨1, 1⟩

def rawAdd (a b : RPARawMultiplicity) : RPARawMultiplicity :=
  ⟨a.openCount + b.openCount, a.closedCount + b.closedCount⟩

theorem raw_open_plus_open :
    rawAdd rawOpen rawOpen = ⟨2, 0⟩ := rfl

theorem raw_closed_plus_closed :
    rawAdd rawClosed rawClosed = ⟨0, 2⟩ := rfl

theorem raw_open_plus_closed :
    rawAdd rawOpen rawClosed = rawDual := rfl

inductive RPACanonicalState
  | empty
  | open
  | closed
  | full
  deriving DecidableEq, Repr

def canonicalize (r : RPARawMultiplicity) : RPACanonicalState :=
  match decide (r.openCount = 0), decide (r.closedCount = 0) with
  | true,  true  => .empty
  | false, true  => .open
  | true,  false => .closed
  | false, false => .full

theorem canonicalize_empty :
    canonicalize rawEmpty = .empty := by
  native_decide

theorem canonicalize_open :
    canonicalize rawOpen = .open := by
  native_decide

theorem canonicalize_closed :
    canonicalize rawClosed = .closed := by
  native_decide

theorem canonicalize_dual :
    canonicalize rawDual = .full := by
  native_decide

theorem canonicalize_open_idempotent :
    canonicalize (rawAdd rawOpen rawOpen) = canonicalize rawOpen := by
  native_decide

theorem canonicalize_closed_idempotent :
    canonicalize (rawAdd rawClosed rawClosed) = canonicalize rawClosed := by
  native_decide

def canonicalJoin : RPACanonicalState → RPACanonicalState → RPACanonicalState
  | .empty, x => x
  | x, .empty => x
  | .open, .open => .open
  | .closed, .closed => .closed
  | .open, .closed => .full
  | .closed, .open => .full
  | .full, _ => .full
  | _, .full => .full

theorem canonical_open_idem :
    canonicalJoin .open .open = .open := rfl

theorem canonical_closed_idem :
    canonicalJoin .closed .closed = .closed := rfl

theorem canonical_open_closed_full :
    canonicalJoin .open .closed = .full := rfl

theorem canonical_full_absorbing_left (x : RPACanonicalState) :
    canonicalJoin .full x = .full := by
  cases x <;> rfl

theorem canonical_full_absorbing_right (x : RPACanonicalState) :
    canonicalJoin x .full = .full := by
  cases x <;> rfl


/-! Complete raw lattice through word length 3, plus the 2+2 FULL state. -/

def rawWord2 (a b : RPARawMultiplicity) : RPARawMultiplicity :=
  rawAdd a b

def rawWord3 (a b c : RPARawMultiplicity) : RPARawMultiplicity :=
  rawAdd (rawAdd a b) c

def rawWord4
    (a b c d : RPARawMultiplicity) : RPARawMultiplicity :=
  rawAdd (rawAdd (rawAdd a b) c) d

theorem raw_closed_plus_open :
    rawWord2 rawClosed rawOpen = rawDual := rfl

theorem raw_open_open_open :
    rawWord3 rawOpen rawOpen rawOpen = ⟨3, 0⟩ := rfl

theorem raw_closed_closed_closed :
    rawWord3 rawClosed rawClosed rawClosed = ⟨0, 3⟩ := rfl

theorem raw_open_open_closed :
    rawWord3 rawOpen rawOpen rawClosed = ⟨2, 1⟩ := rfl

theorem raw_open_closed_open :
    rawWord3 rawOpen rawClosed rawOpen = ⟨2, 1⟩ := rfl

theorem raw_closed_open_open :
    rawWord3 rawClosed rawOpen rawOpen = ⟨2, 1⟩ := rfl

theorem raw_open_closed_closed :
    rawWord3 rawOpen rawClosed rawClosed = ⟨1, 2⟩ := rfl

theorem raw_closed_open_closed :
    rawWord3 rawClosed rawOpen rawClosed = ⟨1, 2⟩ := rfl

theorem raw_closed_closed_open :
    rawWord3 rawClosed rawClosed rawOpen = ⟨1, 2⟩ := rfl

theorem raw_full_2_2 :
    rawWord4 rawOpen rawOpen rawClosed rawClosed = ⟨2, 2⟩ := rfl

theorem canonicalize_open_open :
    canonicalize (rawWord2 rawOpen rawOpen) = .open := by
  native_decide

theorem canonicalize_closed_closed :
    canonicalize (rawWord2 rawClosed rawClosed) = .closed := by
  native_decide

theorem canonicalize_closed_open :
    canonicalize (rawWord2 rawClosed rawOpen) = .full := by
  native_decide

theorem canonicalize_open_open_open :
    canonicalize (rawWord3 rawOpen rawOpen rawOpen) = .open := by
  native_decide

theorem canonicalize_closed_closed_closed :
    canonicalize (rawWord3 rawClosed rawClosed rawClosed) = .closed := by
  native_decide

theorem canonicalize_open_open_closed :
    canonicalize (rawWord3 rawOpen rawOpen rawClosed) = .full := by
  native_decide

theorem canonicalize_open_closed_open :
    canonicalize (rawWord3 rawOpen rawClosed rawOpen) = .full := by
  native_decide

theorem canonicalize_closed_open_open :
    canonicalize (rawWord3 rawClosed rawOpen rawOpen) = .full := by
  native_decide

theorem canonicalize_open_closed_closed :
    canonicalize (rawWord3 rawOpen rawClosed rawClosed) = .full := by
  native_decide

theorem canonicalize_closed_open_closed :
    canonicalize (rawWord3 rawClosed rawOpen rawClosed) = .full := by
  native_decide

theorem canonicalize_closed_closed_open :
    canonicalize (rawWord3 rawClosed rawClosed rawOpen) = .full := by
  native_decide

theorem canonicalize_full_2_2 :
    canonicalize
      (rawWord4 rawOpen rawOpen rawClosed rawClosed) = .full := by
  native_decide

theorem complete_lattice_14 :
    canonicalize rawOpen = .open ∧
    canonicalize rawClosed = .closed ∧
    canonicalize (rawWord2 rawOpen rawClosed) = .full ∧
    canonicalize (rawWord2 rawClosed rawOpen) = .full ∧
    canonicalize (rawWord2 rawOpen rawOpen) = .open ∧
    canonicalize (rawWord2 rawClosed rawClosed) = .closed ∧
    canonicalize (rawWord3 rawOpen rawOpen rawOpen) = .open ∧
    canonicalize (rawWord3 rawClosed rawClosed rawClosed) = .closed ∧
    canonicalize (rawWord3 rawOpen rawOpen rawClosed) = .full ∧
    canonicalize (rawWord3 rawOpen rawClosed rawOpen) = .full ∧
    canonicalize (rawWord3 rawClosed rawOpen rawOpen) = .full ∧
    canonicalize (rawWord3 rawOpen rawClosed rawClosed) = .full ∧
    canonicalize (rawWord3 rawClosed rawOpen rawClosed) = .full ∧
    canonicalize (rawWord3 rawClosed rawClosed rawOpen) = .full := by
  native_decide

abbrev RPAFull : Prop := DUAL_ENDPOINT_STATE

theorem full_is_dual_endpoint_state :
    RPAFull ↔ DUAL_ENDPOINT_STATE := Iff.rfl

theorem full_is_math :
    RPAFull ↔ RPAMath := Iff.rfl

theorem full_is_final_root :
    RPAFull ↔ RPAFinalRoot := Iff.rfl

theorem full_is_global_external_certificate :
    RPAFull ↔ RPAGlobalExternalCertificate := Iff.rfl

theorem full_raw_2_2_is_global_external :
    canonicalize
        (rawWord4 rawOpen rawOpen rawClosed rawClosed) = .full ∧
      (RPAFull ↔ RPAGlobalExternalCertificate) := by
  exact ⟨canonicalize_full_2_2, full_is_global_external_certificate⟩

theorem full_chain_exact :
    RPAFull ↔
      (DUAL_ENDPOINT_STATE ∧
       RPAMath ∧
       RPAFinalRoot ∧
       RPAGlobalExternalCertificate) := by
  constructor
  · intro h
    exact ⟨h, h, h, h⟩
  · rintro ⟨h, _, _, _⟩
    exact h

end MCore
