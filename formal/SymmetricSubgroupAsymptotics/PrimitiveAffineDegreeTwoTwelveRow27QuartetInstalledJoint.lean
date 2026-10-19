import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow62CyclicFourInstalledJoint
import SymmetricSubgroupAsymptotics.Row27OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRemainingEightExclusion

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow27QuartetInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 1 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨26, fun _ _ => Row27OriginalJointData.flexibleData, by decide +kernel⟩]
def additionalIndices : Finset (Fin 301) := Finset.univ.image fun k : Fin 1 => (entry k).index
theorem additionalIndices_eq_singleton : additionalIndices = {26} := by decide +kernel
theorem additionalIndices_card : additionalIndices.card = 1 := by
  rw [additionalIndices_eq_singleton, Finset.card_singleton]
theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveRow62CyclicFourInstalledJoint.installedIndices := by
  rw [additionalIndices_eq_singleton]
  apply Finset.disjoint_singleton_left.mpr
  have h275 : (26 : Fin 301) ∉ DegreeTwoTwelveRow181GraphInstalledJoint.installedIndices :=
    DegreeTwoTwelveRemainingEightExclusion.not_mem_installed_of_mem 26 (by decide +kernel)
  have h276 : (26 : Fin 301) ∉ DegreeTwoTwelveRow61CutSpaceInstalledJoint.installedIndices := by
    rw [DegreeTwoTwelveRow61CutSpaceInstalledJoint.installedIndices,Finset.mem_union,not_or]
    exact ⟨h275,by decide +kernel⟩
  have h277 : (26 : Fin 301) ∉ DegreeTwoTwelveRow22DirectedEdgeInstalledJoint.installedIndices := by
    rw [DegreeTwoTwelveRow22DirectedEdgeInstalledJoint.installedIndices,Finset.mem_union,not_or]
    exact ⟨h276,by decide +kernel⟩
  have h278 : (26 : Fin 301) ∉ DegreeTwoTwelveRow49DoubleSymmetricInstalledJoint.installedIndices := by
    rw [DegreeTwoTwelveRow49DoubleSymmetricInstalledJoint.installedIndices,Finset.mem_union,not_or]
    exact ⟨h277,by decide +kernel⟩
  have h279 : (26 : Fin 301) ∉ DegreeTwoTwelveRow272PrimitiveElevenInstalledJoint.installedIndices := by
    rw [DegreeTwoTwelveRow272PrimitiveElevenInstalledJoint.installedIndices,Finset.mem_union,not_or]
    exact ⟨h278,by decide +kernel⟩
  have h280 : (26 : Fin 301) ∉ DegreeTwoTwelveRow187CyclicPairInstalledJoint.installedIndices := by
    rw [DegreeTwoTwelveRow187CyclicPairInstalledJoint.installedIndices,Finset.mem_union,not_or]
    exact ⟨h279,by decide +kernel⟩
  rw [DegreeTwoTwelveRow62CyclicFourInstalledJoint.installedIndices,Finset.mem_union,not_or]
  exact ⟨h280,by decide +kernel⟩

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
  DegreeTwoTwelveRow62CyclicFourInstalledJoint.installedIndices ∪ additionalIndices
theorem installedIndices_card : installedIndices.card = 282 := by
  rw [installedIndices,Finset.card_union_of_disjoint additionalIndices_disjoint_previous.symm,
    DegreeTwoTwelveRow62CyclicFourInstalledJoint.installedIndices_card,additionalIndices_card]
def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices
set_option maxRecDepth 4096 in
theorem additionalIndices_subset_previous_remaining :
    additionalIndices ⊆ DegreeTwoTwelveRow62CyclicFourInstalledJoint.remainingIndices := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,additional_branch j hj,?_⟩
  intro hold
  exact Finset.disjoint_left.mp additionalIndices_disjoint_previous hj hold

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem remainingIndices_eq : remainingIndices =
    DegreeTwoTwelveRow62CyclicFourInstalledJoint.remainingIndices \ additionalIndices := by
  ext j
  simp only [remainingIndices,DegreeTwoTwelveRow62CyclicFourInstalledJoint.remainingIndices,
    installedIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
    Finset.mem_sdiff,not_or]
  tauto

theorem remainingIndices_card : remainingIndices.card = 1 := by
  rw [remainingIndices_eq,Finset.card_sdiff_of_subset additionalIndices_subset_previous_remaining,
    DegreeTwoTwelveRow62CyclicFourInstalledJoint.remainingIndices_card,additionalIndices_card]

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite
namespace RemainingData
def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveRow62CyclicFourInstalledJoint.RemainingData where
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
end DegreeTwoTwelveRow27QuartetInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
