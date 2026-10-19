import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDoubleSymmetricPilotInstalledJoint
import SymmetricSubgroupAsymptotics.Row113DoubleSymmetricOriginalJointData
import SymmetricSubgroupAsymptotics.Row147DoubleSymmetricOriginalJointData
import SymmetricSubgroupAsymptotics.Row226DoubleSymmetricOriginalJointData

/-! Three original order-48 pair-top clients retain their physical
kernels, original abelian axes, and original natural-two bounds. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveDoubleSymmetricFollowupInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 3 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨112, fun _ _ => Row113DoubleSymmetricOriginalJointData.flexibleData, by decide +kernel⟩,
    ⟨146, fun _ _ => Row147DoubleSymmetricOriginalJointData.flexibleData, by decide +kernel⟩,
    ⟨225, fun _ _ => Row226DoubleSymmetricOriginalJointData.flexibleData, by decide +kernel⟩]
def additionalIndices : Finset (Fin 301) := Finset.univ.image fun k : Fin 3 => (entry k).index
theorem additionalIndices_card : additionalIndices.card = 3 := by decide +kernel
theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveDoubleSymmetricPilotInstalledJoint.installedIndices := by
  decide +kernel

def additionalPackage
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (j : Fin 301) (hj : j ∈ additionalIndices) : Data (catalogue.row j).finite := by
  apply Classical.choice
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
  exact ⟨(entry k).package socle primitiveCatalogue⟩
theorem additional_branch (j : Fin 301) (hj : j ∈ additionalIndices) :
    (catalogue.row j).branch = .joint := by
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
  exact (entry k).branch

def installedIndices : Finset (Fin 301) :=
  DegreeTwoTwelveDoubleSymmetricPilotInstalledJoint.installedIndices ∪ additionalIndices
theorem installedIndices_card : installedIndices.card = 257 := by decide +kernel
def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices
theorem remainingIndices_card : remainingIndices.card = 26 := by decide +kernel

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite
namespace RemainingData
def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveDoubleSymmetricPilotInstalledJoint.RemainingData where
  row j hold hbranch := by
    by_cases hadd : j ∈ additionalIndices
    · exact additionalPackage socle primitiveCatalogue j hadd
    · exact D.row j (by simpa only [installedIndices, Finset.mem_union,
        not_or] using And.intro hold hadd) hbranch
def resolution (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  (D.previous socle primitiveCatalogue).resolution socle primitiveCatalogue hZmud lit
end RemainingData
end DegreeTwoTwelveDoubleSymmetricFollowupInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
