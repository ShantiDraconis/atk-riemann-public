import MCore.RH.Experimental.GeometryAnsatz

namespace MCore.RH.Experimental

/-- Invariants used to compare candidate structures without assuming relevance to RH. -/
structure GeometryInvariants where
  parameterRank : ℕ
  hasReflectionSymmetry : Bool
  hasRotationSymmetry : Bool
  hasPeriodicDirection : Bool
  coneCount : ℕ

structure ClassifiedGeometry where
  descriptor : GeometryDescriptor
  invariants : GeometryInvariants
  ansatz : GeometryAnsatz

def squareClass : ClassifiedGeometry :=
  ⟨squareDescriptor, ⟨2, true, false, false, 0⟩, PairParamAnsatz⟩

def cubeClass : ClassifiedGeometry :=
  ⟨cubeDescriptor, ⟨3, true, false, false, 0⟩, PairParamAnsatz⟩

def sphereClass : ClassifiedGeometry :=
  ⟨sphereDescriptor, ⟨1, true, true, false, 0⟩, ScalarParamAnsatz⟩

def cylinderClass : ClassifiedGeometry :=
  ⟨cylinderDescriptor, ⟨2, true, true, true, 0⟩, PairParamAnsatz⟩

def coneClass : ClassifiedGeometry :=
  ⟨coneDescriptor, ⟨2, false, true, false, 1⟩, PairParamAnsatz⟩

def doubleConeClass : ClassifiedGeometry :=
  ⟨doubleConeDescriptor, ⟨2, true, true, false, 2⟩, PairParamAnsatz⟩

def tripleConeClass : ClassifiedGeometry :=
  ⟨tripleConeDescriptor, ⟨3, false, true, false, 3⟩, PairParamAnsatz⟩

def torusClass : ClassifiedGeometry :=
  ⟨torusDescriptor, ⟨2, true, true, true, 0⟩, PairParamAnsatz⟩

/-- Unknown geometries can enter the same search if they supply actual invariants and an ansatz. -/
def customGeometry
    (label : String) (dimension : ℕ)
    (inv : GeometryInvariants) (ansatz : GeometryAnsatz) : ClassifiedGeometry :=
  ⟨⟨label, dimension⟩, inv, ansatz⟩

end MCore.RH.Experimental
