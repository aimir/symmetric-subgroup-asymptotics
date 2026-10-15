import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRows234And258ScalarSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Exact full-scalar packages: original row234 retains (1,1), and
original row258 retains (2,1). No stored capacity is enlarged. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRows234And258FinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row234 : DegreeTwoTwelveJointFiniteRowData row234Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRows234And258ScalarSocles.row234_family
  natural := PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row234Natural

def row258 : DegreeTwoTwelveJointFiniteRowData row258Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRows234And258ScalarSocles.row258_family
  natural := DegreeTwoTwelveRow131CyclicFamily.row258Natural

def row234Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (233 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (233 : Fin 301)).finite
      (catalogue.row (233 : Fin 301)).expectedProfiles p := by
  let lift := row234.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row258Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (257 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (257 : Fin 301)).finite
      (catalogue.row (257 : Fin 301)).expectedProfiles p := by
  let lift := row258.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveRows234And258FinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
