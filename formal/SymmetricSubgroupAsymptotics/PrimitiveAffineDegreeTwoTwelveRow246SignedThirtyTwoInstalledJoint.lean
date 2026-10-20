import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow103DoubleSymmetricInstalledJoint
import SymmetricSubgroupAsymptotics.Row246OriginalJointData

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow246SignedThirtyTwoInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 1 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨245, fun _ _ => Row246OriginalJointData.flexibleData, by decide +kernel⟩]
def additionalIndices : Finset (Fin 301) := Finset.univ.image fun k : Fin 1 => (entry k).index
theorem additionalIndices_card : additionalIndices.card = 1 := by decide +kernel
theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.installedIndices := by
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
  DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.installedIndices ∪ additionalIndices
theorem installedIndices_card : installedIndices.card = 271 := by
  rw [installedIndices,Finset.card_union_of_disjoint additionalIndices_disjoint_previous.symm,
    DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.installedIndices_card,additionalIndices_card]
def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices
set_option maxRecDepth 4096 in
theorem additionalIndices_subset_previous_remaining :
    additionalIndices ⊆ DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.remainingIndices := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,additional_branch j hj,?_⟩
  intro hold
  exact Finset.disjoint_left.mp additionalIndices_disjoint_previous hj hold

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem remainingIndices_eq : remainingIndices =
    DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.remainingIndices \ additionalIndices := by
  ext j
  simp only [remainingIndices,DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.remainingIndices,
    installedIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
    Finset.mem_sdiff,not_or]
  tauto

theorem remainingIndices_card : remainingIndices.card = 12 := by
  rw [remainingIndices_eq,Finset.card_sdiff_of_subset additionalIndices_subset_previous_remaining,
    DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.remainingIndices_card,additionalIndices_card]

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite
namespace RemainingData
def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveRow103DoubleSymmetricInstalledJoint.RemainingData where
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
end DegreeTwoTwelveRow246SignedThirtyTwoInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
