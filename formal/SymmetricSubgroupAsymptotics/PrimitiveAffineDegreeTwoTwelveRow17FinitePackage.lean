import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRows17And19ImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! The complete original-quotient row-17 package. The original top's
socle bound comes from its exact affine image; its natural module is
uniformly cyclic by the literal matrix units and algebra projector. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow17FinitePackage

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

def finiteData : DegreeTwoTwelveJointFiniteRowData row17Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRows17And19ImageSocles.row17TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

def resolvedRow (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (16 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (16 : Fin 301)).finite
      (catalogue.row (16 : Fin 301)).expectedProfiles p := by
  let lift := finiteData.liftConclusion hZmud lit (by decide +kernel) R
  exact .relative lift rfl (degreeTwoTwelvePairRelativeNumerics lift.lift)

end DegreeTwoTwelveRow17FinitePackage
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
