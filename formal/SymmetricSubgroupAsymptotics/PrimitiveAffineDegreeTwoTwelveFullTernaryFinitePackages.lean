import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullTernarySocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Original full-ternary packages at retained capacities: row194 has
κ=2 and natural capacity1; row231 has κ=1 and natural capacity1. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveFullTernaryFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row194 : DegreeTwoTwelveJointFiniteRowData row194Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveFullTernarySocles.row194_family
  natural := PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row194Natural

def row231 : DegreeTwoTwelveJointFiniteRowData row231Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveFullTernarySocles.row231_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row231Natural

def row194Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (193 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (193 : Fin 301)).finite
      (catalogue.row (193 : Fin 301)).expectedProfiles p := by
  let lift := row194.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row231Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (230 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (230 : Fin 301)).finite
      (catalogue.row (230 : Fin 301)).expectedProfiles p := by
  let lift := row231.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveFullTernaryFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
