import SymmetricSubgroupAsymptotics.TwelveCatalogueOriginalGroupLocator
import SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneExtendedSource

/-! Exact original-source residual after all selected actual capacity-one
packages. The classifier is only a locator; unhandled row isomorphisms
continue to request the final source on the original representative. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveLocatorExtendedSixPairResidualAssembly
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev RemainingSource :=
  ∀ (p : PreE7PairActionClass 6) (j : Fin 301),
    j ∉ TwelveInstalledSocleOneExtendedSource.indices →
    (catalogue.row j).finite.top ≃* preE7PairAction 6 p →
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p)

def source
    (published : PublishedDegreeTwoTwelvePairTopCatalogueLocator catalogue)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hZmud : ZmudFaithfulCharacterTupleInput) (remaining : RemainingSource) :
    DegreeTwoSixPairRepresentativeSource := by
  intro p
  letI : MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12) :=
    preE7PairAction_pretransitive 6 p
  apply Classical.choice
  obtain ⟨j,hj⟩ := TwelveCatalogueOriginalGroupLocator.exists_top_equiv catalogue published
    (preE7PairAction 6 p) (preE7PairAction_not_isPGroup 6 p)
  let e := Classical.choice hj
  by_cases hs : j ∈ TwelveInstalledSocleOneExtendedSource.indices
  · exact ⟨TwelveInstalledSocleOneExtendedSource.source socle primitiveCatalogue hZmud j hs p e⟩
  · exact ⟨remaining p j hs e⟩

end SymmetricSubgroupAsymptotics.TwelveLocatorExtendedSixPairResidualAssembly
