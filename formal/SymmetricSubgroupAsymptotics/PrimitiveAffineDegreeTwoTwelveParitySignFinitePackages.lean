import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveParitySignImages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow19CyclicFamily

/-! The exact stored joint packages for original rows 79, 81, and 125,
using the actual signed-block quotient-socle proofs and checked cycles. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveParitySignFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

def row79 : DegreeTwoTwelveJointFiniteRowData row79Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveParitySignImages.row79TopSocle
  natural := DegreeTwoTwelveRow19CyclicFamily.row79Natural

def row81 : DegreeTwoTwelveJointFiniteRowData row81Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveParitySignImages.row81TopSocle
  natural := DegreeTwoTwelveRow19CyclicFamily.row81Natural

def row125 : DegreeTwoTwelveJointFiniteRowData row125Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveParitySignImages.row125TopSocle
  natural := DegreeTwoTwelveRow19CyclicFamily.row125Natural

def row79Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (78 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (78 : Fin 301)).finite
      (catalogue.row (78 : Fin 301)).expectedProfiles p := by
  let lift := row79.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row81Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (80 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (80 : Fin 301)).finite
      (catalogue.row (80 : Fin 301)).expectedProfiles p := by
  let lift := row81.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row125Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (124 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (124 : Fin 301)).finite
      (catalogue.row (124 : Fin 301)).expectedProfiles p := by
  let lift := row125.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveParitySignFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
