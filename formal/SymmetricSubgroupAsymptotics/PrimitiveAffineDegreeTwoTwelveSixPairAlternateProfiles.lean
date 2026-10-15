import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixPairAlternateSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Admissible alternate profiles for three original joint actions. Every
finite bound is on the original top and every endpoint uses its actual
proved comparator source, without identifying different profile sets. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSixPairAlternateProfiles

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows
open PrimitiveAffineDegreeTwoTwelveSixPairAlternateSocles

def row58AtTwo : DegreeTwoTwelveFlexibleProfiles.Data row58Interface where
  kappa := 2
  sectionCap := 2
  parameters := by decide +kernel
  finite := {
    topSocle := row58AtTwo_family
    natural := DegreeTwoTwelveSharedNaturalWitnesses.row58Natural }

def row105AtTwo : DegreeTwoTwelveFlexibleProfiles.Data row105Interface where
  kappa := 2
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row105AtTwo_family
    natural := DegreeTwoTwelveSharedNaturalWitnesses.row105Natural }

def row285AtTwo : DegreeTwoTwelveFlexibleProfiles.Data row285Interface where
  kappa := 2
  sectionCap := 2
  parameters := by decide +kernel
  finite := {
    topSocle := row285AtTwo_family
    natural := DegreeTwoTwelveSharedNaturalWitnesses.row285Natural }

def row58AtTwoResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (57 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (57 : Fin 301)).finite
      (catalogue.row (57 : Fin 301)).expectedProfiles p :=
  row58AtTwo.resolvedRow hZmud lit _ R

def row105AtTwoResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (104 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (104 : Fin 301)).finite
      (catalogue.row (104 : Fin 301)).expectedProfiles p :=
  row105AtTwo.resolvedRow hZmud lit _ R

def row285AtTwoResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (284 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (284 : Fin 301)).finite
      (catalogue.row (284 : Fin 301)).expectedProfiles p :=
  row285AtTwo.resolvedRow hZmud lit _ R

end DegreeTwoTwelveSixPairAlternateProfiles
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
