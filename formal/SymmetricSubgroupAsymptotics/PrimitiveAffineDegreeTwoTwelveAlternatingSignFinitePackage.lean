import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAlternatingSignSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Original even-sign alternating row271, with retained capacities (2,1). -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveAlternatingSignFinitePackage

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row271 : DegreeTwoTwelveJointFiniteRowData row271Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveAlternatingSignSocles.row271_family
  natural := PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily.row271Natural

def row271Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (270 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (270 : Fin 301)).finite
      (catalogue.row (270 : Fin 301)).expectedProfiles p := by
  let lift := row271.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveAlternatingSignFinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
