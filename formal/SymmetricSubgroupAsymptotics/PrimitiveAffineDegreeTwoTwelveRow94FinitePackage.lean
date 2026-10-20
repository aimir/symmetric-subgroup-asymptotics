import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow94WreathModel
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow94NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! The exact row94 quotient-socle bound one and the previously checked
natural-module bound one form its original joint finite package. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow94FinitePackage

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def finiteData : DegreeTwoTwelveJointFiniteRowData row94Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRow94WreathModel.topSocle
  natural := DegreeTwoTwelveRow94NaturalFamily.row94Natural

def resolvedRow (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (93 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (93 : Fin 301)).finite
      (catalogue.row (93 : Fin 301)).expectedProfiles p := by
  let lift := finiteData.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveRow94FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
