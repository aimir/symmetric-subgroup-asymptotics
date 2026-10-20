import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenPairFiniteCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopBinaryKernelRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryAffineWitnesses

/-!
# Concrete degree-two pair-top assembly

This file fixes the count-twelve and count-sixteen finite tables in the
degree-two residual source.  Count twelve is the literal 301-row table.
Count sixteen is the complete `24 + 29 + 15 + 20` finite table, with the two
natural alternating/symmetric tops retained as uniform theorem cases.

The final constructor below has no abstract count-twelve or count-sixteen
catalogue argument and no free row-resolution argument.  It exposes the
anchored relative labels and the natural `A_16`/`S_16` character alternative.
Catalogue locators remain separate and are explicitly named as published
classification hypotheses.  The eight four-ternary packages are constructed
internally from their checked literal top/core data and the uniform active
socle theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoConcreteResidualAssembly

abbrev TwelveCatalogue : DegreeTwoTwelvePairTopFiniteCatalogue :=
  DegreeTwoTwelvePairFiniteCatalogue.catalogue

abbrev SixteenCatalogue : DegreeTwoSixteenPairTopFiniteCatalogue :=
  DegreeTwoSixteenPairFiniteCatalogue.catalogue

/-- The published degree-twelve transitive-top locator, specialized to the
literal 301-row catalogue. -/
abbrev PublishedTwelveCatalogueLocator : Prop :=
  PublishedDegreeTwoTwelvePairTopCatalogueLocator TwelveCatalogue

/-- The published degree-sixteen primitive/block locator, specialized to the
complete `24 + 29 + 15 + 20` finite catalogue. -/
abbrev PublishedSixteenCatalogueLocator : Prop :=
  PublishedDegreeTwoSixteenPairTopCatalogueLocator SixteenCatalogue

/-- All non-classification semantic data still required on the two concrete
pair-top catalogues.  The eight four-ternary rows are already supplied by
their checked compression packages; the remaining types are attached to the
actual row and original pair action. -/
structure PairTopSemanticData : Type 1 where
  twelveRelative :
    ∀ (j : Fin 301) (p : PreE7PairActionClass 12)
      (realization : DegreeTwoPairTopRealization
        (TwelveCatalogue.row j).finite p),
      (TwelveCatalogue.row j).branch ≠ .ternary →
      DegreeTwoPairTopBinaryKernelRowData
        (TwelveCatalogue.row j).finite
        (TwelveCatalogue.row j).expectedProfiles p realization
  sixteenPaired8 :
    ∀ (j : Fin 24) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopTowerRealization
        (SixteenCatalogue.paired8 j) p),
      DegreeTwoPairTopTowerBinaryKernelRowData
        (SixteenCatalogue.paired8 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenZero16 :
    ∀ (j : Fin 29) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization
        (SixteenCatalogue.zero16 j) p),
      DegreeTwoPairTopBinaryKernelRowData
        (SixteenCatalogue.zero16 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenTwoAffine16 :
    ∀ (j : Fin 15) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization
        (SixteenCatalogue.twoAffine16 j) p),
      DegreeTwoPairTopBinaryKernelRowData
        (SixteenCatalogue.twoAffine16 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenPrimitive16 :
    ∀ (j : Fin 20) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization
        (SixteenCatalogue.primitive16 j) p),
      DegreeTwoPairTopBinaryKernelRowData
        (SixteenCatalogue.primitive16 j)
        degreeTwoSixteenPairProfiles p realization
  sixteenNatural :
    ∀ (kind : DegreeTwoSixteenNaturalTop)
      (p : PreE7PairActionClass 16)
      (realization : DegreeTwoSixteenNaturalTopRealization kind p),
      DegreeTwoSixteenNaturalSocleGeneratorData kind p realization

namespace PairTopSemanticData

/-- Resolve all 301 concrete count-twelve rows. -/
noncomputable def twelveResolution
    (D : PairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution TwelveCatalogue :=
  degreeTwoTwelveCatalogueResolution_of_relative_and_fourTernary
    hZmud lit
    (fun j p realization h ↦
      (D.twelveRelative j p realization h).twelveResolvedData lit)
    PrimitiveAffineDegreeTwoFourTernaryAffineWitnesses.compressionPackages

/-- Resolve the complete concrete count-sixteen table, including the
twenty-four paired-eight rows and all 64 literal degree-sixteen rows. -/
noncomputable def sixteenResolution
    (D : PairTopSemanticData)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairTopCatalogueResolution SixteenCatalogue :=
  degreeTwoSixteenResolution_of_binaryKernel_and_naturalSocle hZmud lit
    SixteenCatalogue
    D.sixteenPaired8 D.sixteenZero16 D.sixteenTwoAffine16
    D.sixteenPrimitive16 D.sixteenNatural

end PairTopSemanticData

/-- The complete degree-two residual source with both pair-top catalogues
fixed to their literal generated tables.  The hypotheses named `published*`
are catalogue/classification inputs.  `pairTopData`, the six-pair owner
table, and the 527-row eight-pair semantic table are independently checked
project data and are intentionally visible in the type. -/
noncomputable def source
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (publishedThree :
      PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPairTable : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (publishedSix : PublishedDegreeTwoSixPairCatalogueLocator sixPairTable)
    (eightPairTable : DegreeTwoEightPairFiniteCatalogue)
    (publishedEight :
      PublishedDegreeTwoEightPairCatalogueLocator eightPairTable)
    (publishedTwelve : PublishedTwelveCatalogueLocator)
    (publishedSixteen : PublishedSixteenCatalogueLocator)
    (pairTopData : PairTopSemanticData) :
    PrimitiveAffineResidualDegreeSource 2 :=
  degreeTwoResidualSource_of_finitePairTopCatalogues
    hZmud lit publishedThree publishedFour sixPairTable publishedSix
    eightPairTable publishedEight
    TwelveCatalogue publishedTwelve
      (pairTopData.twelveResolution hZmud lit)
    SixteenCatalogue publishedSixteen
      (pairTopData.sixteenResolution hZmud lit)

end DegreeTwoConcreteResidualAssembly
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
