import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCocycleSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow4NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Three original cocycle packages. Row4 retains capacities (1,3),
and rows132/177 retain capacities (1,1). -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveCocycleFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row4 : DegreeTwoTwelveJointFiniteRowData row4Interface 1 3 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCocycleSocles.row4_family
  natural := PrimitiveAffineDegreeTwoTwelveRow4NaturalModule.natural

def row132 : DegreeTwoTwelveJointFiniteRowData row132Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCocycleSocles.row132_family
  natural := PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily.row132Natural

def row177 : DegreeTwoTwelveJointFiniteRowData row177Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveCocycleSocles.row177_family
  natural := DegreeTwoTwelveRow17NaturalFamily.row177Natural

def row4Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (3 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (3 : Fin 301)).finite
      (catalogue.row (3 : Fin 301)).expectedProfiles p := by
  let lift := row4.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row132Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (131 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (131 : Fin 301)).finite
      (catalogue.row (131 : Fin 301)).expectedProfiles p := by
  let lift := row132.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row177Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (176 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (176 : Fin 301)).finite
      (catalogue.row (176 : Fin 301)).expectedProfiles p := by
  let lift := row177.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveCocycleFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
