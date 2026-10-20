import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow207Socles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Original row207 alternate (3,1) package from its actual dihedral18 image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow207FinitePackage
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row207AtThree : DegreeTwoTwelveFlexibleProfiles.Data row207Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := { topSocle := PrimitiveAffineDegreeTwoTwelveRow207Socles.family
              natural := PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row207Natural }

def row207AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (206 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (206 : Fin 301)).finite
      (catalogue.row (206 : Fin 301)).expectedProfiles p :=
  row207AtThree.resolvedRow hZmud lit _ R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow207FinitePackage

end
