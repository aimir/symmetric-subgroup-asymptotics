import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullParitySignSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Original full-translation two-sign packages at capacities (2,1) and (3,1). -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveFullParitySignFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row211 : DegreeTwoTwelveJointFiniteRowData row211Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveFullParitySignSocles.row211_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row211Natural

def row248 : DegreeTwoTwelveJointFiniteRowData row248Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveFullParitySignSocles.row248_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row248Natural

def row211Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (210 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (210 : Fin 301)).finite
      (catalogue.row (210 : Fin 301)).expectedProfiles p := by
  let lift := row211.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row248Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (247 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (247 : Fin 301)).finite
      (catalogue.row (247 : Fin 301)).expectedProfiles p := by
  let lift := row248.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveFullParitySignFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
