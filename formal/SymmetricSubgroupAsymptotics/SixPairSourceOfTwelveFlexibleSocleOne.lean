import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.SixPairSourceOfTwelveSocleOneProfile

/-! Reuse the ACTUAL capacity of a checked flexible package. The equality
below concerns the proved package field, never the historical row label. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairSourceOfTwelveFlexibleSocleOne
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelveFlexibleProfiles
variable {D : DegreeTwoPairTopFiniteInterface 12}

/-- Transport only the capacity index of the already proved normal family. -/
def family (F : Data D) (h : F.kappa=1) :
    D.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  h ▸ F.finite.topSocle

/-- The natural-module capacity is irrelevant for the six-pair source. -/
def source (F : Data D) (h : F.kappa=1)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (p : PreE7PairActionClass 6) (e : D.top ≃* preE7PairAction 6 p) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  SixPairSourceOfTwelveSocleOneProfile.source D (family F h)
    p e (Classical.choice p.2) hZmud

end SymmetricSubgroupAsymptotics.SixPairSourceOfTwelveFlexibleSocleOne
