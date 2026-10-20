import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveBinarySignSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Five original joint packages from the shared signed four-block
family. Their existing natural-module certificates are reused literally. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveBinarySignFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row245 : DegreeTwoTwelveJointFiniteRowData row245Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveBinarySignSocles.row245_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row245Natural

def row264 : DegreeTwoTwelveJointFiniteRowData row264Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveBinarySignSocles.row264_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row264Natural

def row267 : DegreeTwoTwelveJointFiniteRowData row267Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveBinarySignSocles.row267_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row267Natural

def row274 : DegreeTwoTwelveJointFiniteRowData row274Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveBinarySignSocles.row274_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row274Natural

def row289 : DegreeTwoTwelveJointFiniteRowData row289Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveBinarySignSocles.row289_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row289Natural

def row245Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (244 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (244 : Fin 301)).finite
      (catalogue.row (244 : Fin 301)).expectedProfiles p := by
  let lift := row245.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row264Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (263 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (263 : Fin 301)).finite
      (catalogue.row (263 : Fin 301)).expectedProfiles p := by
  let lift := row264.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row267Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (266 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (266 : Fin 301)).finite
      (catalogue.row (266 : Fin 301)).expectedProfiles p := by
  let lift := row267.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row274Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (273 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (273 : Fin 301)).finite
      (catalogue.row (273 : Fin 301)).expectedProfiles p := by
  let lift := row274.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row289Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (288 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (288 : Fin 301)).finite
      (catalogue.row (288 : Fin 301)).expectedProfiles p := by
  let lift := row289.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveBinarySignFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
