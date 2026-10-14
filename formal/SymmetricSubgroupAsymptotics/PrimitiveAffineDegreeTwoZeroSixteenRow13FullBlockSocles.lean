import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow13BlockImage
import SymmetricSubgroupAsymptotics.BinaryFourFullBlockNormalGenerators

/-! Original zero16 row13 quotient socles, transported through the exact
full-block generator map and retaining every original normal kernel. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow13FullBlockSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourFullBlockCoordinates PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts

abbrev Top := DegreeTwoZeroSixteenInterfaces.row13.top

theorem socle_of_surjective {Q : Type} [Group Q]
    (pi : Top →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  fullBlockModel_socle_of_surjective (pi.comp row13Map) (hpi.comp row13Map_surjective)

theorem quotientSocle (N : Subgroup Top) [N.Normal] :
    SocleNormalGeneratorBound (Top ⧸ N) 2 :=
  socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def family : DegreeTwoZeroSixteenInterfaces.row13.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocle N.1)

end PrimitiveAffineDegreeTwoZeroSixteenRow13FullBlockSocles
end SymmetricSubgroupAsymptotics

end
