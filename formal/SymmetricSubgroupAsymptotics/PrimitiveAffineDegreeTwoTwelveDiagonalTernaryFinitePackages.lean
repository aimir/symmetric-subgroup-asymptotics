import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow20NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Five diagonal ternary packages at their original stored capacities. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveDiagonalTernaryFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row20 : DegreeTwoTwelveJointFiniteRowData row20Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles.row20_family
  natural := DegreeTwoTwelveRow20NaturalFamily.row20Natural

def row43 : DegreeTwoTwelveJointFiniteRowData row43Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles.row43_family
  natural := DegreeTwoTwelveRow20NaturalFamily.row43Natural

def row44 : DegreeTwoTwelveJointFiniteRowData row44Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles.row44_family
  natural := DegreeTwoTwelveRow20NaturalFamily.row44Natural

def row45 : DegreeTwoTwelveJointFiniteRowData row45Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles.row45_family
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row45Natural

def row83 : DegreeTwoTwelveJointFiniteRowData row83Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveDiagonalTernarySocles.row83_family
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row83Natural

def row20Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (19 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (19 : Fin 301)).finite
      (catalogue.row (19 : Fin 301)).expectedProfiles p := by
  let lift := row20.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row43Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (42 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (42 : Fin 301)).finite
      (catalogue.row (42 : Fin 301)).expectedProfiles p := by
  let lift := row43.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row44Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (43 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (43 : Fin 301)).finite
      (catalogue.row (43 : Fin 301)).expectedProfiles p := by
  let lift := row44.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row45Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (44 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (44 : Fin 301)).finite
      (catalogue.row (44 : Fin 301)).expectedProfiles p := by
  let lift := row45.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row83Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (82 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (82 : Fin 301)).finite
      (catalogue.row (82 : Fin 301)).expectedProfiles p := by
  let lift := row83.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveDiagonalTernaryFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
