import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveEdgeFollowupInstalledJoint
import SymmetricSubgroupAsymptotics.DihedralFourOriginalJointData

/-! Four original dihedral pair actions retain their physical kernels,
actual abelian axes, and checked original natural-two bounds. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveDihedralFourInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 4 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨107, fun _ _ => DihedralFourOriginalJointData.row108Data, by decide +kernel⟩,
    ⟨108, fun _ _ => DihedralFourOriginalJointData.row109Data, by decide +kernel⟩,
    ⟨153, fun _ _ => DihedralFourOriginalJointData.row154Data, by decide +kernel⟩,
    ⟨154, fun _ _ => DihedralFourOriginalJointData.row155Data, by decide +kernel⟩]
def additionalIndices : Finset (Fin 301) := Finset.univ.image fun k : Fin 4 => (entry k).index
theorem additionalIndices_card : additionalIndices.card = 4 := by decide +kernel
theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveEdgeFollowupInstalledJoint.installedIndices := by
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
  DegreeTwoTwelveEdgeFollowupInstalledJoint.installedIndices ∪ additionalIndices
theorem installedIndices_card : installedIndices.card = 253 := by decide +kernel
def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices
theorem remainingIndices_card : remainingIndices.card = 30 := by decide +kernel

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite
namespace RemainingData
def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveEdgeFollowupInstalledJoint.RemainingData where
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
end DegreeTwoTwelveDihedralFourInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
