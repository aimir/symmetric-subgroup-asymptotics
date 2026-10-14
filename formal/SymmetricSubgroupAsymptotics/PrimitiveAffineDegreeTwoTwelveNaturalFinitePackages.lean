import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveNaturalTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Complete original-quotient joint packages for the literal A12/S12 tops. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveNaturalFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

def row300 : DegreeTwoTwelveJointFiniteRowData row300Interface 1 1 where
  topSocle := DegreeTwoTwelveNaturalTops.row300Socle
  natural := DegreeTwoTwelveNaturalTops.row300Natural

def row301 : DegreeTwoTwelveJointFiniteRowData row301Interface 1 1 where
  topSocle := DegreeTwoTwelveNaturalTops.row301Socle
  natural := DegreeTwoTwelveNaturalTops.row301Natural

def row300Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (299 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (299 : Fin 301)).finite
      (catalogue.row (299 : Fin 301)).expectedProfiles p := by
  let lift := row300.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row301Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (300 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (300 : Fin 301)).finite
      (catalogue.row (300 : Fin 301)).expectedProfiles p := by
  let lift := row301.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveNaturalFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
