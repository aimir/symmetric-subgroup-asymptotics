import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow176AugmentationSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! The original row176 package retains its one-character socle bound
and its one-generator natural-module bound. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow176FinitePackage

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def finitePackage : DegreeTwoTwelveJointFiniteRowData row176Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRow176AugmentationSocles.family
  natural := PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row176Natural

def resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (175 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (175 : Fin 301)).finite
      (catalogue.row (175 : Fin 301)).expectedProfiles p := by
  let lift := finitePackage.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveRow176FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
