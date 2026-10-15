import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveQuaternaryImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Complete original joint packages for rows29 and55 using their exact
quaternary image maps and the existing natural-module certificates.
Row31's socle family is exported separately; no natural bound is assumed. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveQuaternaryImageFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row29 : DegreeTwoTwelveJointFiniteRowData row29Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveQuaternaryImageSocles.row29TopSocle
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row29Natural

def row55 : DegreeTwoTwelveJointFiniteRowData row55Interface 1 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveQuaternaryImageSocles.row55TopSocle
  natural := DegreeTwoTwelveThreeBlockNaturalFamily.row55Natural

def row29Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (28 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (28 : Fin 301)).finite
      (catalogue.row (28 : Fin 301)).expectedProfiles p := by
  let lift := row29.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row55Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (54 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (54 : Fin 301)).finite
      (catalogue.row (54 : Fin 301)).expectedProfiles p := by
  let lift := row55.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveQuaternaryImageFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
