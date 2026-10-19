import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow200InstalledJoint
import SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData

/-! Two original six-pair actions at the (3,1) profile, using the universal
transitive-six top theorem and their checked original natural-one bounds. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveJoinedHalfCycleInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 2 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨207, JoinedHalfCycleSixPairOriginalJointData.row208Data, by decide +kernel⟩,
    ⟨259, JoinedHalfCycleSixPairOriginalJointData.row260Data, by decide +kernel⟩]
def additionalIndices : Finset (Fin 301) := Finset.univ.image fun k : Fin 2 => (entry k).index
theorem additionalIndices_card : additionalIndices.card = 2 := by decide +kernel
theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveRow200InstalledJoint.installedIndices := by
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
  DegreeTwoTwelveRow200InstalledJoint.installedIndices ∪ additionalIndices
theorem installedIndices_card : installedIndices.card = 235 := by decide +kernel
def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices
theorem remainingIndices_card : remainingIndices.card = 48 := by decide +kernel

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite
namespace RemainingData
def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveRow200InstalledJoint.RemainingData where
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
end DegreeTwoTwelveJoinedHalfCycleInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
