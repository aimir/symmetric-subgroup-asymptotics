import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairImageFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveParityCoupledSignAlternate
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFlexibleResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedAlternateProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixPairAlternateProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLargeSignAlternateProfiles

/-! Install thirty-two admissible alternate profiles on their original
catalogue actions. No historical capacity is asserted for these rows.
The remaining finite obligations and the published classification inputs
stay explicit; this file does not assert completion of the catalogue. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveAlternateInstalledJoint

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

/-- Zero-based indices of the thirty-two original actions resolved here. -/
def alternateIndices : Finset (Fin 301) :=
  {34, 35, 45, 57, 79, 81, 83, 104, 172, 208, 211, 215, 246, 248, 261, 262, 279, 280, 284, 59, 68, 106, 144, 281, 51, 52, 147, 149, 150, 220, 222, 224}

theorem alternateIndices_card : alternateIndices.card = 32 := by decide +kernel

theorem alternateIndices_disjoint_exact :
    Disjoint alternateIndices DegreeTwoTwelveFlexibleInstalledJoint.exactIndices := by
  decide +kernel

noncomputable def alternatePackage (j : Fin 301) (hj : j ∈ alternateIndices) :
    Data (catalogue.row j).finite := by
  apply Classical.choice
  simp only [alternateIndices, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row35AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row36AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row46AtTwo
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSixPairAlternateProfiles.row58AtTwo
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row80AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row82AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row84AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSixPairAlternateProfiles.row105AtTwo
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row173AtTwo
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row209AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row212AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row216AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row247AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row249AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row262AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSignedAlternateProfiles.row263AtThree
  · refine ⟨?_⟩
    exact DegreeTwoTwelveLargeSignAlternateProfiles.row280AtTwo
  · refine ⟨?_⟩
    exact DegreeTwoTwelveLargeSignAlternateProfiles.row281AtTwo
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSixPairAlternateProfiles.row285AtTwo

  · refine ⟨?_⟩
    exact DegreeTwoTwelvePairImageFinitePackages.row60At2Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelvePairImageFinitePackages.row69At2Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelvePairImageFinitePackages.row107At2Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelvePairImageFinitePackages.row145At3Data
  · refine ⟨?_⟩
    exact PrimitiveAffineDegreeTwoTwelveParityCoupledSignAlternate.row282AtTwo

  · refine ⟨?_⟩
    exact DegreeTwoTwelveSecondPairChartFinitePackages.row52At3Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSecondPairChartFinitePackages.row53At3Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSecondPairChartFinitePackages.row148At3Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSecondPairChartFinitePackages.row150At3Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSecondPairChartFinitePackages.row151At3Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSecondPairChartFinitePackages.row221At3Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSecondPairChartFinitePackages.row223At3Data
  · refine ⟨?_⟩
    exact DegreeTwoTwelveSecondPairChartFinitePackages.row225At3Data

/-- Every selected alternate package lies in the actual joint branch. -/
theorem alternate_branch (j : Fin 301) (hj : j ∈ alternateIndices) :
    (catalogue.row j).branch = .joint := by
  have h : ∀ k ∈ alternateIndices, (catalogue.row k).branch = .joint := by
    decide +kernel
  exact h j hj

def installedIndices : Finset (Fin 301) :=
  DegreeTwoTwelveFlexibleInstalledJoint.exactIndices ∪ alternateIndices

theorem installedIndices_card : installedIndices.card = 125 := by decide +kernel

/-- Bounds are requested only for original joint actions outside both
the exact packages and the thirty-two alternate packages. -/
structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ installedIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite

namespace RemainingData

noncomputable def flexible (D : RemainingData) :
    DegreeTwoTwelveFlexibleInstalledJoint.RemainingData where
  row j hexact hbranch := by
    by_cases halt : j ∈ alternateIndices
    · exact alternatePackage j halt
    · exact D.row j (by simpa only [installedIndices, Finset.mem_union,
        not_or] using And.intro hexact halt) hbranch

noncomputable def resolution (D : RemainingData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  D.flexible.resolution hZmud lit

/-- The installed alternate packages enter the same original-action residual
source, reducing only its explicitly remaining finite obligations. -/
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
  DegreeTwoFlexibleResidualAssembly.source hZmud lit publishedThree publishedFour
    sixPairTable publishedSix eightPairTable publishedEight publishedTwelve publishedSixteen
    D.flexible sixteen

end RemainingData

end DegreeTwoTwelveAlternateInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end

