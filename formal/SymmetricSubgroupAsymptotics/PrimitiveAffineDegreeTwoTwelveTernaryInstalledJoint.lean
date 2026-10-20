import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveStructuralInstalledJoint
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow40TernaryPilot
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow47TernaryPilot
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow171TernaryPilot
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow172TernaryPilot
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow174TernaryPilot

/-! Five complete original joint packages from actual signed ternary lifts.
The pure C4 × C2, quaternion and dihedral complements are proved with actual
words and a point gauge.
The existing numerical menu admits the proved capacities (2,2); historical
profiles and all original normal denominators remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveTernaryInstalledJoint
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def entry : Fin 5 → DegreeTwoTwelveStructuralInstalledJoint.Entry :=
  ![⟨39, fun _ _ => TwelvePointRemainingStructuralRow40TernaryPilot.dataAtTwo,
    by decide +kernel⟩,
    ⟨46, fun _ _ => TwelvePointRemainingStructuralRow47TernaryPilot.dataAtTwo,
    by decide +kernel⟩,
    ⟨170, fun _ _ => TwelvePointRemainingStructuralRow171TernaryPilot.dataAtTwo,
    by decide +kernel⟩,
    ⟨171, fun _ _ => TwelvePointRemainingStructuralRow172TernaryPilot.dataAtTwo,
    by decide +kernel⟩,
    ⟨173, fun _ _ => TwelvePointRemainingStructuralRow174TernaryPilot.dataAtTwo,
    by decide +kernel⟩]

def additionalIndices : Finset (Fin 301) :=
  Finset.univ.image fun k : Fin 5 => (entry k).index

theorem additionalIndices_card : additionalIndices.card = 5 := by decide +kernel

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

theorem installedIndices_card : installedIndices.card = 219 := by decide +kernel

def remainingIndices : Finset (Fin 301) :=
  Finset.univ.filter fun j => (catalogue.row j).branch = .joint ∧ j ∉ installedIndices

theorem remainingIndices_card : remainingIndices.card = 64 := by decide +kernel

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
