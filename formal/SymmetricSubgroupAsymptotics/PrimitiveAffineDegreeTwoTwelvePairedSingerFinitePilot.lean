import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerPilot
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily

/-! Complete alternate (3,1) package for original paired-Singer row251. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePilot

open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row251AtThree : DegreeTwoTwelveFlexibleProfiles.Data row251Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.family
              natural := PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row251Natural }

def row251AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (250 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (250 : Fin 301)).finite
      (catalogue.row (250 : Fin 301)).expectedProfiles p :=
  row251AtThree.resolvedRow hZmud lit _ R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePilot

end
