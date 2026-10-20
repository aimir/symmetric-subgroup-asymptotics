import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedTernaryCentralFlipNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Six complete original joint packages from the arbitrary signed
affine-subgroup theorem and the retained block-cycle or central-flip natural modules. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSignedSubgroupFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row41 : DegreeTwoTwelveJointFiniteRowData row41Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles.row41_family
  natural := PrimitiveAffineDegreeTwoTwelvePairedTernaryCentralFlipNaturalFamily.row41Natural

def row78 : DegreeTwoTwelveJointFiniteRowData row78Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles.row78_family
  natural := PrimitiveAffineDegreeTwoTwelvePairedTernaryCentralFlipNaturalFamily.row78Natural

def row215 : DegreeTwoTwelveJointFiniteRowData row215Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles.row215_family
  natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row215Natural

def row243 : DegreeTwoTwelveJointFiniteRowData row243Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles.row243_family
  natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row243Natural

def row244 : DegreeTwoTwelveJointFiniteRowData row244Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles.row244_family
  natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row244Natural

def row266 : DegreeTwoTwelveJointFiniteRowData row266Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles.row266_family
  natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row266Natural

def row215Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (214 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (214 : Fin 301)).finite
      (catalogue.row (214 : Fin 301)).expectedProfiles p := by
  let lift := row215.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row243Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (242 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (242 : Fin 301)).finite
      (catalogue.row (242 : Fin 301)).expectedProfiles p := by
  let lift := row243.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row244Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (243 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (243 : Fin 301)).finite
      (catalogue.row (243 : Fin 301)).expectedProfiles p := by
  let lift := row244.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

def row266Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (265 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (265 : Fin 301)).finite
      (catalogue.row (265 : Fin 301)).expectedProfiles p := by
  let lift := row266.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveSignedSubgroupFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
