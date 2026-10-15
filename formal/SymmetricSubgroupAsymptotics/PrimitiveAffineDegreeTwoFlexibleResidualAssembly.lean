import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleInstalledJoint

/-! Install alternate proved count-twelve profiles into the unchanged
original-action degree-two residual theorem. All existing exact one-frame,
paired-eight, natural-top and exceptional count-twelve resolutions are
retained. The outstanding finite data remains explicit. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoFlexibleResidualAssembly

abbrev SixteenCatalogue := DegreeTwoConcreteResidualAssembly.SixteenCatalogue

noncomputable def sixteenResolution
    (D : DegreeTwoSixteenInstalledSocles.RemainingData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoSixteenPairTopCatalogueResolution SixteenCatalogue where
  paired8 j p realization :=
    DegreeTwoPairedEightCompleteCatalogue.resolvedRow hZmud lit j realization
  zero16 j p realization :=
    D.finiteCatalogue.zero16ResolvedRow hZmud lit j realization
  twoAffine16 j p realization :=
    D.finiteCatalogue.twoAffine16ResolvedRow hZmud lit j realization
  primitive16 j p realization :=
    D.finiteCatalogue.primitive16ResolvedRow hZmud lit j realization
  natural kind p realization :=
    DegreeTwoSixteenNaturalFiniteRows.symbolicCatalogue.source hZmud lit kind p realization

/-- An alternate valid numerical profile changes no catalogue action,
quotient, realization or original weight in the residual source. -/
noncomputable def source
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
    (twelve : DegreeTwoTwelveFlexibleInstalledJoint.RemainingData)
    (sixteen : DegreeTwoSixteenInstalledSocles.RemainingData) :
    PrimitiveAffineResidualDegreeSource 2 :=
  degreeTwoResidualSource_of_finitePairTopCatalogues
    hZmud lit publishedThree publishedFour sixPairTable publishedSix
    eightPairTable publishedEight
    DegreeTwoConcreteResidualAssembly.TwelveCatalogue publishedTwelve
      (twelve.resolution hZmud lit)
    SixteenCatalogue publishedSixteen (sixteenResolution sixteen hZmud lit)

end DegreeTwoFlexibleResidualAssembly
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
