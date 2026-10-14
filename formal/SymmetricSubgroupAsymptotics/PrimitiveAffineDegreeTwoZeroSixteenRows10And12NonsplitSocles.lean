import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRows10And12BlockImages
import SymmetricSubgroupAsymptotics.BinaryFourNonsplitNormalGenerators

/-! Quotient-socle bounds for the original zero16 rows10 and12,
transported through the checked literal generator maps. The normal
subgroup in every conclusion is the original quotient kernel. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRows10And12NonsplitSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourFullBlockCoordinates PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts

abbrev Top10 := DegreeTwoZeroSixteenInterfaces.row10.top
abbrev Top12 := DegreeTwoZeroSixteenInterfaces.row12.top

theorem row10_socle_of_surjective {Q : Type} [Group Q]
    (pi : Top10 →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  row10Model_socle_of_surjective (pi.comp row10Map) (hpi.comp row10Map_surjective)

theorem row12_socle_of_surjective {Q : Type} [Group Q]
    (pi : Top12 →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  row12Model_socle_of_surjective (pi.comp row12Map) (hpi.comp row12Map_surjective)

theorem row10_quotientSocle (N : Subgroup Top10) [N.Normal] :
    SocleNormalGeneratorBound (Top10 ⧸ N) 2 :=
  row10_socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem row12_quotientSocle (N : Subgroup Top12) [N.Normal] :
    SocleNormalGeneratorBound (Top12 ⧸ N) 2 :=
  row12_socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def row10Socle : DegreeTwoZeroSixteenInterfaces.row10.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by
    letI := N.2
    exact row10_quotientSocle N.1)

def row12Socle : DegreeTwoZeroSixteenInterfaces.row12.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by
    letI := N.2
    exact row12_quotientSocle N.1)

end PrimitiveAffineDegreeTwoZeroSixteenRows10And12NonsplitSocles
end SymmetricSubgroupAsymptotics

end
