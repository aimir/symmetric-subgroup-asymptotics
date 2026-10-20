import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveTwelveInstalledJoint
import SymmetricSubgroupAsymptotics.SixPairSourceOfTwelveFlexibleSocleOne

/-! A small pilot inspects actual installed package fields, with no normal
census or historical capacity lookup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePrimitiveInstalledSocleOnePilot
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePrimitiveTwelveInstalledJoint

theorem package_kappa
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (k : Fin 2) : ((entry k).package socle primitiveCatalogue).kappa=1 := by
  fin_cases k <;> rfl

def source
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (k : Fin 2) (p : PreE7PairActionClass 6)
    (e : (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row (entry k).index).finite.top ≃*
      preE7PairAction 6 p) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  SixPairSourceOfTwelveFlexibleSocleOne.source
    ((entry k).package socle primitiveCatalogue)
    (package_kappa socle primitiveCatalogue k) hZmud p e

end SymmetricSubgroupAsymptotics.TwelvePrimitiveInstalledSocleOnePilot
