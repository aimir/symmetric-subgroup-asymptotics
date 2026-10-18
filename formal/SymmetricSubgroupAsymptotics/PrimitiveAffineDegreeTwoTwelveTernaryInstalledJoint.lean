import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveStructuralInstalledJoint
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow40TernaryPilot

/-! One complete original joint package from an actual signed ternary lift.
The pure C4 × C2 complement is proved with actual words and a point gauge.
The existing numerical menu admits the proved capacities (2,2); historical
profiles and all original normal denominators remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveTernaryInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 1 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨39, fun _ _ => TwelvePointRemainingStructuralRow40TernaryPilot.dataAtTwo,
    by decide +kernel⟩]

def additionalIndices : Finset (Fin 301) :=
  Finset.univ.image fun k : Fin 1 => (entry k).index

theorem additionalIndices_card : additionalIndices.card = 1 := by decide +kernel

theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveStructuralInstalledJoint.installedIndices := by
  decide +kernel

def additionalPackage
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (j : Fin 301) (hj : j ∈ additionalIndices) : Data (catalogue.row j).finite := by
  apply Classical.choice
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨(entry k).package socle primitiveCatalogue⟩

theorem additional_branch (j : Fin 301) (hj : j ∈ additionalIndices) :
    (catalogue.row j).branch = .joint := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
  exact (entry k).branch

def installedIndices : Finset (Fin 301) :=
  DegreeTwoTwelveStructuralInstalledJoint.installedIndices ∪ additionalIndices

theorem installedIndices_card : installedIndices.card = 215 := by decide +kernel

def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices

theorem remainingIndices_card : remainingIndices.card = 68 := by decide +kernel

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite

namespace RemainingData

def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveStructuralInstalledJoint.RemainingData where
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
end DegreeTwoTwelveTernaryInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
