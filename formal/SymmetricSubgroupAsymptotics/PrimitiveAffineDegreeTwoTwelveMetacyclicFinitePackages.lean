import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicImages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow19CyclicFamily

/-! The exact stored (2,1) joint packages for original rows 38, 39, and 42. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveMetacyclicFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

def row38 : DegreeTwoTwelveJointFiniteRowData row38Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveMetacyclicImages.row38TopSocle
  natural := DegreeTwoTwelveRow19CyclicFamily.row38Natural

def row39 : DegreeTwoTwelveJointFiniteRowData row39Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveMetacyclicImages.row39TopSocle
  natural := DegreeTwoTwelveRow19CyclicFamily.row39Natural

def row42 : DegreeTwoTwelveJointFiniteRowData row42Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveMetacyclicImages.row42TopSocle
  natural := DegreeTwoTwelveRow19CyclicFamily.row42Natural

def row38Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (37 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (37 : Fin 301)).finite
      (catalogue.row (37 : Fin 301)).expectedProfiles p := by
  let lift := row38.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row39Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (38 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (38 : Fin 301)).finite
      (catalogue.row (38 : Fin 301)).expectedProfiles p := by
  let lift := row39.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row42Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (41 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (41 : Fin 301)).finite
      (catalogue.row (41 : Fin 301)).expectedProfiles p := by
  let lift := row42.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveMetacyclicFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
