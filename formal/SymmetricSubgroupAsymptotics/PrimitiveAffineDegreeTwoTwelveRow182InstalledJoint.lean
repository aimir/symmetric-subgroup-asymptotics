import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryInstalledJoint
import SymmetricSubgroupAsymptotics.Row182OriginalJointData

/-! A selected original row182 extension of the joint catalogue installer.
The checked (2,1) package keeps its literal twelve-point action and original
normal denominators. This extension adds no new published premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow182InstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ⟨181, Row182OriginalBlockKernel.flexibleData, by decide +kernel⟩

def additionalIndices : Finset (Fin 301) := {entry.index}

theorem additionalIndices_card : additionalIndices.card = 1 := by decide +kernel

theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveTernaryInstalledJoint.installedIndices := by
  decide +kernel

def additionalPackage
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (j : Fin 301) (hj : j ∈ additionalIndices) : Data (catalogue.row j).finite := by
  have he : j = entry.index := Finset.mem_singleton.mp hj
  subst j
  exact entry.package socle primitiveCatalogue

theorem additional_branch (j : Fin 301) (hj : j ∈ additionalIndices) :
    (catalogue.row j).branch = .joint := by
  have he : j = entry.index := Finset.mem_singleton.mp hj
  subst j
  exact entry.branch

def installedIndices : Finset (Fin 301) :=
  DegreeTwoTwelveTernaryInstalledJoint.installedIndices ∪ additionalIndices

theorem installedIndices_card : installedIndices.card = 220 := by decide +kernel

def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices

theorem remainingIndices_card : remainingIndices.card = 63 := by decide +kernel

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite

namespace RemainingData

def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveTernaryInstalledJoint.RemainingData where
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
end DegreeTwoTwelveRow182InstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
