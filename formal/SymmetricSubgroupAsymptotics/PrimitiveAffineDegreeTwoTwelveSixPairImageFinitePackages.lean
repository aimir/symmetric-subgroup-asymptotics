import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixPairImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Four original complete joint packages from the physical pair kernel
chart and the retained C6/S6 image, with their existing natural bounds. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSixPairImageFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row87 : DegreeTwoTwelveJointFiniteRowData row87Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSixPairImageSocles.row87_family
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row87Natural

def row134 : DegreeTwoTwelveJointFiniteRowData row134Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSixPairImageSocles.row134_family
  natural := PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily.row134Natural

def row219 : DegreeTwoTwelveJointFiniteRowData row219Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSixPairImageSocles.row219_family
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row219Natural

def row293 : DegreeTwoTwelveJointFiniteRowData row293Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSixPairImageSocles.row293_family
  natural := PrimitiveAffineDegreeTwoTwelveEvenPairCycleNaturalFamily.row293Natural

def row87Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (86 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (86 : Fin 301)).finite
      (catalogue.row (86 : Fin 301)).expectedProfiles p := by
  let lift := row87.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row134Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (133 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (133 : Fin 301)).finite
      (catalogue.row (133 : Fin 301)).expectedProfiles p := by
  let lift := row134.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row219Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (218 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (218 : Fin 301)).finite
      (catalogue.row (218 : Fin 301)).expectedProfiles p := by
  let lift := row219.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row293Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (292 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (292 : Fin 301)).finite
      (catalogue.row (292 : Fin 301)).expectedProfiles p := by
  let lift := row293.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveSixPairImageFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
