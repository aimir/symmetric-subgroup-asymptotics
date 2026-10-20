import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow265NaturalFamily

/-! Complete alternate (3,1) packages for the nine further three-quartet
rows. Row292 remains in the checked pilot module. All packages preserve
the original actions and use the committed natural-module bounds. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages

open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateSocles

def row265AtThree : DegreeTwoTwelveFlexibleProfiles.Data row265Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row265AtThree_family
              natural := DegreeTwoTwelveRow265NaturalFamily.row265Natural }
def row273AtThree : DegreeTwoTwelveFlexibleProfiles.Data row273Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row273AtThree_family
              natural := DegreeTwoTwelveRow265NaturalFamily.row273Natural }
def row275AtThree : DegreeTwoTwelveFlexibleProfiles.Data row275Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row275AtThree_family
              natural := DegreeTwoTwelveRow265NaturalFamily.row275Natural }
def row276AtThree : DegreeTwoTwelveFlexibleProfiles.Data row276Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row276AtThree_family
              natural := DegreeTwoTwelveRow265NaturalFamily.row276Natural }
def row283AtThree : DegreeTwoTwelveFlexibleProfiles.Data row283Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row283AtThree_family
              natural := DegreeTwoTwelveRow265NaturalFamily.row283Natural }
def row284AtThree : DegreeTwoTwelveFlexibleProfiles.Data row284Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row284AtThree_family
              natural := DegreeTwoTwelveRow265NaturalFamily.row284Natural }
def row290AtThree : DegreeTwoTwelveFlexibleProfiles.Data row290Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row290AtThree_family
              natural := DegreeTwoTwelveRow265NaturalFamily.row290Natural }
def row291AtThree : DegreeTwoTwelveFlexibleProfiles.Data row291Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row291AtThree_family
              natural := DegreeTwoTwelveRow265NaturalFamily.row291Natural }
def row294AtThree : DegreeTwoTwelveFlexibleProfiles.Data row294Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row294AtThree_family
              natural := DegreeTwoTwelveRow94NaturalFamily.row294Natural }

def row265AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (264 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (264 : Fin 301)).finite
      (catalogue.row (264 : Fin 301)).expectedProfiles p :=
  row265AtThree.resolvedRow hZmud lit _ R
def row273AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (272 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (272 : Fin 301)).finite
      (catalogue.row (272 : Fin 301)).expectedProfiles p :=
  row273AtThree.resolvedRow hZmud lit _ R
def row275AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (274 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (274 : Fin 301)).finite
      (catalogue.row (274 : Fin 301)).expectedProfiles p :=
  row275AtThree.resolvedRow hZmud lit _ R
def row276AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (275 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (275 : Fin 301)).finite
      (catalogue.row (275 : Fin 301)).expectedProfiles p :=
  row276AtThree.resolvedRow hZmud lit _ R
def row283AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (282 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (282 : Fin 301)).finite
      (catalogue.row (282 : Fin 301)).expectedProfiles p :=
  row283AtThree.resolvedRow hZmud lit _ R
def row284AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (283 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (283 : Fin 301)).finite
      (catalogue.row (283 : Fin 301)).expectedProfiles p :=
  row284AtThree.resolvedRow hZmud lit _ R
def row290AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (289 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (289 : Fin 301)).finite
      (catalogue.row (289 : Fin 301)).expectedProfiles p :=
  row290AtThree.resolvedRow hZmud lit _ R
def row291AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (290 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (290 : Fin 301)).finite
      (catalogue.row (290 : Fin 301)).expectedProfiles p :=
  row291AtThree.resolvedRow hZmud lit _ R
def row294AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (293 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (293 : Fin 301)).finite
      (catalogue.row (293 : Fin 301)).expectedProfiles p :=
  row294AtThree.resolvedRow hZmud lit _ R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateFinitePackages

end
