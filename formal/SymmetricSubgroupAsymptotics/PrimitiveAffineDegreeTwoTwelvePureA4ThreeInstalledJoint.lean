import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow203FullWreathInstalledJoint
import SymmetricSubgroupAsymptotics.Row126TernaryWreathOriginalJointData
import SymmetricSubgroupAsymptotics.Row160QuarterTurnOriginalJointData
import SymmetricSubgroupAsymptotics.Row161TwoAxisOriginalJointData

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePureA4ThreeInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 3 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨125, fun _ _ => Row126TernaryWreathOriginalJointData.flexibleData, by decide +kernel⟩,
    ⟨159, fun _ _ => Row160QuarterTurnOriginalJointData.flexibleData, by decide +kernel⟩,
    ⟨160, fun _ _ => Row161TwoAxisOriginalJointData.flexibleData, by decide +kernel⟩]
def additionalIndices : Finset (Fin 301) := Finset.univ.image fun k : Fin 3 => (entry k).index
theorem additionalIndices_card : additionalIndices.card = 3 := by decide +kernel
theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveRow203FullWreathInstalledJoint.installedIndices := by
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
  DegreeTwoTwelveRow203FullWreathInstalledJoint.installedIndices ∪ additionalIndices
theorem installedIndices_card : installedIndices.card = 266 := by decide +kernel
def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices
theorem remainingIndices_card : remainingIndices.card = 17 := by decide +kernel

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite
namespace RemainingData
def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveRow203FullWreathInstalledJoint.RemainingData where
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
end DegreeTwoTwelvePureA4ThreeInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
