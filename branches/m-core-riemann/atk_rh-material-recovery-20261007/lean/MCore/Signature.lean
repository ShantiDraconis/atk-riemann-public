namespace MCore
inductive SignatureStatus where | candidate | definitionInterface | provedProperty | refutedProperty | openBridge deriving DecidableEq, Repr
structure CriticalSignature (Object Value : Type) where
  observable : Object → Value
  target : Value → Prop
  status : SignatureStatus := .candidate
structure SignatureAdapter (A B VA VB : Type) where
  source : CriticalSignature A VA
  targetSig : CriticalSignature B VB
  mapObject : A → B
  relation : VA → VB → Prop
end MCore
