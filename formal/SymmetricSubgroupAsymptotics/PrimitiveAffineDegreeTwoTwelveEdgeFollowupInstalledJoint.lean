import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow57EdgeInstalledJoint
import SymmetricSubgroupAsymptotics.Row88EdgePairOriginalJointData
import SymmetricSubgroupAsymptotics.Row92EdgePairOriginalJointData
import SymmetricSubgroupAsymptotics.Row93EdgePairOriginalJointData
import SymmetricSubgroupAsymptotics.Row144EdgePairOriginalJointData
import SymmetricSubgroupAsymptotics.Row188EdgePairOriginalJointData

/-! Five original actions reuse the physical edge-A4 source theorem
with their retained original natural-two bounds. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveEdgeFollowupInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 5 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨87, fun _ _ => Row88EdgePairOriginalJointData.flexibleData, by decide +kernel⟩,
    ⟨91, fun _ _ => Row92EdgePairOriginalJointData.flexibleData, by decide +kernel⟩,
    ⟨92, fun _ _ => Row93EdgePairOriginalJointData.flexibleData, by decide +kernel⟩,
    ⟨143, fun _ _ => Row144EdgePairOriginalJointData.flexibleData, by decide +kernel⟩,
    ⟨187, fun _ _ => Row188EdgePairOriginalJointData.flexibleData, by decide +kernel⟩]
def additionalIndices : Finset (Fin 301) := Finset.univ.image fun k : Fin 5 => (entry k).index
theorem additionalIndices_card : additionalIndices.card = 5 := by decide +kernel
theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveRow57EdgeInstalledJoint.installedIndices := by
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
  DegreeTwoTwelveRow57EdgeInstalledJoint.installedIndices ∪ additionalIndices
theorem installedIndices_card : installedIndices.card = 249 := by decide +kernel
def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices
theorem remainingIndices_card : remainingIndices.card = 34 := by decide +kernel

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite
namespace RemainingData
def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveRow57EdgeInstalledJoint.RemainingData where
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
end DegreeTwoTwelveEdgeFollowupInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
