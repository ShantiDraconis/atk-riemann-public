namespace MCore
inductive BoundaryPhase where | regular | preBoundary | boundary | crossing | postBoundary deriving DecidableEq, Repr
inductive BoundaryResult where | uniqueExtension | pathDependent | blowup | oscillatory | removable | nonremovable | discreteJump | noNaturalLimit | open deriving DecidableEq, Repr
structure BoundaryProtocol (Object Value : Type) where
  observable : Object → Value
  atBoundary : Object → Prop
  admissiblePath : (Nat → Object) → Prop
end MCore
