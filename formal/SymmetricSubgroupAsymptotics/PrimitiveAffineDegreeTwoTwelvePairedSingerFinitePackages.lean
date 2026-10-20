import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily

/-! Four further complete alternate (3,1) packages from exact paired-Singer words. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePackages
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue PrimitiveAffineDegreeTwoTwelvePairedSingerSocles

def row252AtThree : DegreeTwoTwelveFlexibleProfiles.Data row252Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row252AtThree_family
              natural := PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row252Natural }

def row252AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (251 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (251 : Fin 301)).finite
      (catalogue.row (251 : Fin 301)).expectedProfiles p :=
  row252AtThree.resolvedRow hZmud lit _ R

def row253AtThree : DegreeTwoTwelveFlexibleProfiles.Data row253Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row253AtThree_family
              natural := PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row253Natural }

def row253AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (252 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (252 : Fin 301)).finite
      (catalogue.row (252 : Fin 301)).expectedProfiles p :=
  row253AtThree.resolvedRow hZmud lit _ R

def row254AtThree : DegreeTwoTwelveFlexibleProfiles.Data row254Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row254AtThree_family
              natural := PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row254Natural }

def row254AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (253 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (253 : Fin 301)).finite
      (catalogue.row (253 : Fin 301)).expectedProfiles p :=
  row254AtThree.resolvedRow hZmud lit _ R

def row268AtThree : DegreeTwoTwelveFlexibleProfiles.Data row268Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := row268AtThree_family
              natural := PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row268Natural }

def row268AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (267 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (267 : Fin 301)).finite
      (catalogue.row (267 : Fin 301)).expectedProfiles p :=
  row268AtThree.resolvedRow hZmud lit _ R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerFinitePackages

end
