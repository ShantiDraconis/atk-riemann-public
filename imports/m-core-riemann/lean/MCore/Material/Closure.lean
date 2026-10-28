import MCore
namespace MCore.Material
structure RHClosure (DN : Nat → Real) where
  K0 : Real
  K0_nonneg : 0 ≤ K0
  log_pos : ∀ N : Nat, 0 < Real.log (N + 2)
  bound : ∀ N : Nat, DN N ≤ K0 / Real.log (N + 2)

def ConcreteUniformLogDNBound (DN : Nat → Real) : Prop := Nonempty (RHClosure DN)

theorem closure_produces_bound {DN : Nat → Real} (h : RHClosure DN) :
    ConcreteUniformLogDNBound DN := ⟨h⟩
end MCore.Material
