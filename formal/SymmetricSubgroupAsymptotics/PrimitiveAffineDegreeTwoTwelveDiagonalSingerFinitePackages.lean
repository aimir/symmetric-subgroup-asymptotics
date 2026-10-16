import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalSingerSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow20NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Complete alternate (3,1) packages for eight diagonal-Singer clients. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue PrimitiveAffineDegreeTwoTwelveDiagonalSingerSocles

def row127AtThree : DegreeTwoTwelveFlexibleProfiles.Data row127Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row127_family
              natural := PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily.row127Natural }

def row127AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (126 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (126 : Fin 301)).finite
      (catalogue.row (126 : Fin 301)).expectedProfiles p :=
  row127AtThree.resolvedRow hZmud lit _ R

def row128AtThree : DegreeTwoTwelveFlexibleProfiles.Data row128Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row128_family
              natural := PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily.row128Natural }

def row128AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (127 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (127 : Fin 301)).finite
      (catalogue.row (127 : Fin 301)).expectedProfiles p :=
  row128AtThree.resolvedRow hZmud lit _ R

def row129AtThree : DegreeTwoTwelveFlexibleProfiles.Data row129Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row129_family
              natural := PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily.row129Natural }

def row129AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (128 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (128 : Fin 301)).finite
      (catalogue.row (128 : Fin 301)).expectedProfiles p :=
  row129AtThree.resolvedRow hZmud lit _ R

def row165AtThree : DegreeTwoTwelveFlexibleProfiles.Data row165Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row165_family
              natural := PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily.row165Natural }

def row165AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (164 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (164 : Fin 301)).finite
      (catalogue.row (164 : Fin 301)).expectedProfiles p :=
  row165AtThree.resolvedRow hZmud lit _ R

def row204AtThree : DegreeTwoTwelveFlexibleProfiles.Data row204Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row204_family
              natural := DegreeTwoTwelveRow20NaturalFamily.row204Natural }

def row204AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (203 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (203 : Fin 301)).finite
      (catalogue.row (203 : Fin 301)).expectedProfiles p :=
  row204AtThree.resolvedRow hZmud lit _ R

def row205AtThree : DegreeTwoTwelveFlexibleProfiles.Data row205Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row205_family
              natural := DegreeTwoTwelveRow20NaturalFamily.row205Natural }

def row205AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (204 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (204 : Fin 301)).finite
      (catalogue.row (204 : Fin 301)).expectedProfiles p :=
  row205AtThree.resolvedRow hZmud lit _ R

def row206AtThree : DegreeTwoTwelveFlexibleProfiles.Data row206Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row206_family
              natural := DegreeTwoTwelveRow20NaturalFamily.row206Natural }

def row206AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (205 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (205 : Fin 301)).finite
      (catalogue.row (205 : Fin 301)).expectedProfiles p :=
  row206AtThree.resolvedRow hZmud lit _ R

def row239AtThree : DegreeTwoTwelveFlexibleProfiles.Data row239Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row239_family
              natural := DegreeTwoTwelveRow20NaturalFamily.row239Natural }

def row239AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (238 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (238 : Fin 301)).finite
      (catalogue.row (238 : Fin 301)).expectedProfiles p :=
  row239AtThree.resolvedRow hZmud lit _ R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalSingerFinitePackages

end
