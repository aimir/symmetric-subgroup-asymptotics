import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveStructuralInstalledJoint
import SymmetricSubgroupAsymptotics.SixPairSourceOfTwelveFlexibleSocleOne

/-! Three actual capacity-one packages in the structural installed batch:
the original row166 odd quotient and rows9/8 symmetric tops. No historical
capacity field is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveStructuralInstalledSocleOnePilot
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelveStructuralInstalledJoint

def selected : Fin 3 → Fin 66 := ![39,42,43]

theorem package_kappa
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (k : Fin 3) : ((entry (selected k)).package socle primitiveCatalogue).kappa=1 := by
  fin_cases k <;> rfl

def source
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (k : Fin 3) (p : PreE7PairActionClass 6)
    (e : (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row (entry (selected k)).index).finite.top ≃*
      preE7PairAction 6 p) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  SixPairSourceOfTwelveFlexibleSocleOne.source
    ((entry (selected k)).package socle primitiveCatalogue)
    (package_kappa socle primitiveCatalogue k) hZmud p e

end SymmetricSubgroupAsymptotics.TwelveStructuralInstalledSocleOnePilot
