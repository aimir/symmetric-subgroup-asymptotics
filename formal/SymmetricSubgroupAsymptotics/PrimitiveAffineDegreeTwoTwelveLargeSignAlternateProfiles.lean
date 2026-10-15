import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLargeSignAlternateSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily

/-! Two complete alternate (2,1) profiles for the original A4/S4 signed
actions. Historical profile labels do not alter the proved source. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveLargeSignAlternateProfiles

open DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveLargeSignAlternateSocles

def row280AtTwo : DegreeTwoTwelveFlexibleProfiles.Data row280Interface where
  kappa := 2
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row280AtTwo_family
    natural := PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily.row280Natural }

def row281AtTwo : DegreeTwoTwelveFlexibleProfiles.Data row281Interface where
  kappa := 2
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row281AtTwo_family
    natural := DegreeTwoTwelveRow131CyclicFamily.row281Natural }

def row280AtTwoResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (279 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (279 : Fin 301)).finite
      (catalogue.row (279 : Fin 301)).expectedProfiles p :=
  row280AtTwo.resolvedRow hZmud lit _ R

def row281AtTwoResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (280 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (280 : Fin 301)).finite
      (catalogue.row (280 : Fin 301)).expectedProfiles p :=
  row281AtTwo.resolvedRow hZmud lit _ R

end DegreeTwoTwelveLargeSignAlternateProfiles
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
