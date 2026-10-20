import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! The complete original-quotient joint package for literal row 131. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow131FinitePackage

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

def finiteData : DegreeTwoTwelveJointFiniteRowData row131Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRow131AffineModel.topSocle
  natural := DegreeTwoTwelveRow131CyclicFamily.row131Natural

def resolvedRow (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (130 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (130 : Fin 301)).finite
      (catalogue.row (130 : Fin 301)).expectedProfiles p := by
  let lift := finiteData.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveRow131FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
