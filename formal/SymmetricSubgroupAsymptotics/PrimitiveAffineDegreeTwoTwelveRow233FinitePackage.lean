import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow233ScalarSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! The original row233 package retains κ2 and natural capacity1. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow233FinitePackage

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def finitePackage : DegreeTwoTwelveJointFiniteRowData row233Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRow233ScalarSocles.family
  natural := DegreeTwoTwelveRow17NaturalFamily.row233Natural

def resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (232 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (232 : Fin 301)).finite
      (catalogue.row (232 : Fin 301)).expectedProfiles p := by
  let lift := finitePackage.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveRow233FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
