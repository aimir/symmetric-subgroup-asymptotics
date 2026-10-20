import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow178AugmentationSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow72PolynomialFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Original joint packages at the retained one-position capacities for
the A4, S4, and sign-twisted S4 augmentation actions, rows133,175,178. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveAugmentationFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row133 : DegreeTwoTwelveJointFiniteRowData row133Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveAugmentationSocles.row133_family
  natural := PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row133Natural

def row175 : DegreeTwoTwelveJointFiniteRowData row175Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveAugmentationSocles.row175_family
  natural := DegreeTwoTwelveRow72PolynomialFamily.row175Natural

def row178 : DegreeTwoTwelveJointFiniteRowData row178Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRow178AugmentationSocles.family
  natural := DegreeTwoTwelveRow17NaturalFamily.row178Natural

def row133Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (132 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (132 : Fin 301)).finite
      (catalogue.row (132 : Fin 301)).expectedProfiles p := by
  let lift := row133.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row175Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (174 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (174 : Fin 301)).finite
      (catalogue.row (174 : Fin 301)).expectedProfiles p := by
  let lift := row175.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row178Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (177 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (177 : Fin 301)).finite
      (catalogue.row (177 : Fin 301)).expectedProfiles p := by
  let lift := row178.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveAugmentationFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
