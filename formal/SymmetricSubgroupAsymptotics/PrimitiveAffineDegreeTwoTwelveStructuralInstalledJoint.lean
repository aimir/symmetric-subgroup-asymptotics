import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRecoveredInstalledJoint
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePilot
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow207FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAxesFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveFinalPublishedFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicQuartetFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow166OddSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicSquareSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricEdgeSignSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricOrderedPairSocles

/-! Shared original-action structural packages. The primitive-six entries
use exactly the socle and bounded primitive catalogue inputs already present
at the final published boundary. No new classification or capacity premise
is introduced. Entries retain the original action and both proved capacities. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveStructuralInstalledJoint

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

structure Entry : Type 1 where
  index : Fin 301
  package : PublishedPrimitiveSocleDichotomyInput →
    PublishedBoundedPrimitiveCatalogueCorrespondence → Data (catalogue.row index).finite
  branch : (catalogue.row index).branch = .joint

def entry : Fin 44 → Entry :=
  ![⟨126, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages.row127AtThree, by decide +kernel⟩,
    ⟨127, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages.row128AtThree, by decide +kernel⟩,
    ⟨128, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages.row129AtThree, by decide +kernel⟩,
    ⟨164, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages.row165AtThree, by decide +kernel⟩,
    ⟨203, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages.row204AtThree, by decide +kernel⟩,
    ⟨204, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages.row205AtThree, by decide +kernel⟩,
    ⟨205, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages.row206AtThree, by decide +kernel⟩,
    ⟨238, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages.row239AtThree, by decide +kernel⟩,
    ⟨250, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePilot.row251AtThree, by decide +kernel⟩,
    ⟨251, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePackages.row252AtThree, by decide +kernel⟩,
    ⟨252, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePackages.row253AtThree, by decide +kernel⟩,
    ⟨253, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePackages.row254AtThree, by decide +kernel⟩,
    ⟨267, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePackages.row268AtThree, by decide +kernel⟩,
    ⟨206, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveRow207FinitePackage.row207AtThree, by decide +kernel⟩,
    ⟨158, fun _ _ ↦ DegreeTwoTwelveTernaryAxesFinitePackages.row159At3Data, by decide +kernel⟩,
    ⟨195, fun _ _ ↦ DegreeTwoTwelveTernaryAxesFinitePackages.row196At3Data, by decide +kernel⟩,
    ⟨196, fun _ _ ↦ DegreeTwoTwelveTernaryAxesFinitePackages.row197At3Data, by decide +kernel⟩,
    ⟨239, fun _ _ ↦ DegreeTwoTwelveTernaryAxesFinitePackages.row240At3Data, by decide +kernel⟩,
    ⟨32, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row33At2Data, by decide +kernel⟩,
    ⟨74, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row75At2Data, by decide +kernel⟩,
    ⟨75, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row76At2Data, by decide +kernel⟩,
    ⟨122, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row123At2Data, by decide +kernel⟩,
    ⟨123, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row124At2Data, by decide +kernel⟩,
    ⟨179, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row180At2Data, by decide +kernel⟩,
    ⟨182, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row183At2Data, by decide +kernel⟩,
    ⟨229, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row230At2Data, by decide +kernel⟩,
    ⟨254, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row255At2Data, by decide +kernel⟩,
    ⟨255, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row256At2Data, by decide +kernel⟩,
    ⟨256, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row257At2Data, by decide +kernel⟩,
    ⟨269, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row270At2Data, by decide +kernel⟩,
    ⟨276, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row277At2Data, by decide +kernel⟩,
    ⟨285, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row286At2Data, by decide +kernel⟩,
    ⟨286, DegreeTwoTwelvePrimitiveFinalPublishedFinitePackages.row287At2Data, by decide +kernel⟩,
    ⟨5, fun _ _ ↦ DegreeTwoTwelveCubicQuartetFinitePackages.row6AtTwoData, by decide +kernel⟩,
    ⟨6, fun _ _ ↦ DegreeTwoTwelveCubicQuartetFinitePackages.row7AtTwoData, by decide +kernel⟩,
    ⟨24, fun _ _ ↦ DegreeTwoTwelveCubicQuartetFinitePackages.row25AtTwoData, by decide +kernel⟩,
    ⟨25, fun _ _ ↦ DegreeTwoTwelveCubicQuartetFinitePackages.row26AtTwoData, by decide +kernel⟩,
    ⟨55, fun _ _ ↦ DegreeTwoTwelveCubicQuartetFinitePackages.row56AtTwoData, by decide +kernel⟩,
    ⟨89, fun _ _ ↦ DegreeTwoTwelveCubicQuartetFinitePackages.row90AtTwoData, by decide +kernel⟩,
    ⟨165, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveRow166OddSocles.data, by decide +kernel⟩,
    ⟨84, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveCubicSquareSocles.Row85.data, by decide +kernel⟩,
    ⟨163, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveCubicSquareSocles.Row164.data, by decide +kernel⟩,
    ⟨8, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveSymmetricEdgeSignSocles.data, by decide +kernel⟩,
    ⟨7, fun _ _ ↦ PrimitiveAffineDegreeTwoTwelveSymmetricOrderedPairSocles.data, by decide +kernel⟩]

def additionalIndices : Finset (Fin 301) :=
  Finset.univ.image fun k : Fin 44 ↦ (entry k).index

theorem additionalIndices_card : additionalIndices.card = 44 := by decide +kernel

theorem additionalIndices_disjoint_previous :
    Disjoint additionalIndices DegreeTwoTwelveRecoveredInstalledJoint.installedIndices := by
  decide +kernel

noncomputable def additionalPackage
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
  DegreeTwoTwelveRecoveredInstalledJoint.installedIndices ∪ additionalIndices

theorem installedIndices_card : installedIndices.card = 192 := by decide +kernel

/-- Only original joint actions outside the proved union remain project work. -/
structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite

namespace RemainingData

noncomputable def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveRecoveredInstalledJoint.RemainingData where
  row j hold hbranch := by
    by_cases hadd : j ∈ additionalIndices
    · exact additionalPackage socle primitiveCatalogue j hadd
    · exact D.row j (by simpa only [installedIndices, Finset.mem_union,
        not_or] using And.intro hold hadd) hbranch

noncomputable def resolution (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  (D.previous socle primitiveCatalogue).resolution hZmud lit

noncomputable def source (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
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
  (D.previous socle primitiveCatalogue).source hZmud lit publishedThree publishedFour
    sixPairTable publishedSix eightPairTable publishedEight publishedTwelve publishedSixteen sixteen

end RemainingData
end DegreeTwoTwelveStructuralInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
