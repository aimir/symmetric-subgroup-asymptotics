import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow269InstalledJoint
import SymmetricSubgroupAsymptotics.Row278OriginalJointData
import SymmetricSubgroupAsymptotics.Row279OriginalJointData
import SymmetricSubgroupAsymptotics.Row288OriginalJointData
import SymmetricSubgroupAsymptotics.Row296OriginalJointData
import SymmetricSubgroupAsymptotics.Row297OriginalJointData
import SymmetricSubgroupAsymptotics.Row298OriginalJointData
import SymmetricSubgroupAsymptotics.Row299OriginalJointData

/-! Seven original two-six-block actions at the existing profile (3,1).
Actual component witnesses and every original normal denominator are
retained by each package; no historical profile equality is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 7 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨277, Row278OriginalBlockFrame.flexibleData, by decide +kernel⟩,
    ⟨278, Row279OriginalBlockFrame.flexibleData, by decide +kernel⟩,
    ⟨287, Row288OriginalBlockFrame.flexibleData, by decide +kernel⟩,
    ⟨295, Row296OriginalBlockFrame.flexibleData, by decide +kernel⟩,
    ⟨296, Row297OriginalBlockFrame.flexibleData, by decide +kernel⟩,
    ⟨297, Row298OriginalBlockFrame.flexibleData, by decide +kernel⟩,
    ⟨298, Row299OriginalBlockFrame.flexibleData, by decide +kernel⟩]
def additionalIndices : Finset (Fin 301) := Finset.univ.image fun k : Fin 7 => (entry k).index
theorem additionalIndices_card : additionalIndices.card = 7 := by decide +kernel
theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveRow269InstalledJoint.installedIndices := by
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
  DegreeTwoTwelveRow269InstalledJoint.installedIndices ∪ additionalIndices
theorem installedIndices_card : installedIndices.card = 228 := by decide +kernel
def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices
theorem remainingIndices_card : remainingIndices.card = 55 := by decide +kernel

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite
namespace RemainingData
def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveRow269InstalledJoint.RemainingData where
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
end DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
