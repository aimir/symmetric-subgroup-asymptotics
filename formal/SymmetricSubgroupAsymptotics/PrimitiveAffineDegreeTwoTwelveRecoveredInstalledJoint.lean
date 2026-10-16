import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAlternateInstalledJoint
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages

/-! Additional original-action packages recovered by shared structural
proofs. The dependent entry table keeps each literal action paired with
its own proved capacities. Its residual assembler requests only actions
outside the union with the previously installed catalogue. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRecoveredInstalledJoint

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

structure Entry : Type 1 where
  index : Fin 301
  package : Data (catalogue.row index).finite
  branch : (catalogue.row index).branch = .joint

def entry : Fin 13 → Entry :=
  ![⟨200, DegreeTwoTwelveTwoTernaryMatrixFinitePackages.row201At3Data, by decide +kernel⟩,
    ⟨236, DegreeTwoTwelveTwoTernaryMatrixFinitePackages.row237At3Data, by decide +kernel⟩,
    ⟨237, DegreeTwoTwelveTwoTernaryMatrixFinitePackages.row238At3Data, by decide +kernel⟩,
    ⟨264, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row265AtThree, by decide +kernel⟩,
    ⟨272, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row273AtThree, by decide +kernel⟩,
    ⟨274, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row275AtThree, by decide +kernel⟩,
    ⟨275, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row276AtThree, by decide +kernel⟩,
    ⟨282, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row283AtThree, by decide +kernel⟩,
    ⟨283, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row284AtThree, by decide +kernel⟩,
    ⟨289, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row290AtThree, by decide +kernel⟩,
    ⟨290, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row291AtThree, by decide +kernel⟩,
    ⟨291, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.row292AtThree, by decide +kernel⟩,
    ⟨293, PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages.row294AtThree, by decide +kernel⟩]

def additionalIndices : Finset (Fin 301) :=
  Finset.univ.image fun k : Fin 13 ↦ (entry k).index

theorem additionalIndices_card : additionalIndices.card = 13 := by decide +kernel

theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveAlternateInstalledJoint.installedIndices := by
  decide +kernel

noncomputable def additionalPackage (j : Fin 301) (hj : j ∈ additionalIndices) :
    Data (catalogue.row j).finite := by
  apply Classical.choice
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨(entry k).package⟩

theorem additional_branch (j : Fin 301) (hj : j ∈ additionalIndices) :
    (catalogue.row j).branch = .joint := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
  exact (entry k).branch

def installedIndices : Finset (Fin 301) :=
  DegreeTwoTwelveAlternateInstalledJoint.installedIndices ∪ additionalIndices

theorem installedIndices_card : installedIndices.card = 138 := by decide +kernel

/-- The remaining project-owned original-action obligations. -/
structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite

namespace RemainingData

noncomputable def previous (D : RemainingData) :
    DegreeTwoTwelveAlternateInstalledJoint.RemainingData where
  row j hold hbranch := by
    by_cases hadd : j ∈ additionalIndices
    · exact additionalPackage j hadd
    · exact D.row j (by simpa only [installedIndices, Finset.mem_union,
        not_or] using And.intro hold hadd) hbranch

noncomputable def resolution (D : RemainingData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  D.previous.resolution hZmud lit

noncomputable def source (D : RemainingData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPairTable : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (publishedSix : PublishedDegreeTwoSixPairCatalogueLocator sixPairTable)
    (eightPairTable : DegreeTwoEightPairFiniteCatalogue)
    (publishedEight : PublishedDegreeTwoEightPairCatalogueLocator eightPairTable)
    (publishedTwelve : DegreeTwoConcreteResidualAssembly.PublishedTwelveCatalogueLocator)
    (publishedSixteen : DegreeTwoConcreteResidualAssembly.PublishedSixteenCatalogueLocator)
    (sixteen : DegreeTwoSixteenInstalledSocles.RemainingData) :
    PrimitiveAffineResidualDegreeSource 2 :=
  D.previous.source hZmud lit publishedThree publishedFour sixPairTable publishedSix
    eightPairTable publishedEight publishedTwelve publishedSixteen sixteen

end RemainingData
end DegreeTwoTwelveRecoveredInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
