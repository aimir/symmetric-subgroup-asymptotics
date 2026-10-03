import SymmetricSubgroupAsymptotics.PrimitiveAffinePublishedSmallStructuralInput
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCoefficient
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly

/-!
# Assemble the primitive-affine consumer

The primitive branch is the exhaustive consumer already obtained from the
published finite affine inputs and the generic infinite-degree estimates.
The imprimitive branch is supplied by the group-native component source on
the literal minimal block system and the actual wreath transfer.

The component-source package remains separate from the published finite
input.  Its generic branch is a project estimate on the actual block system;
its exceptional branch is an already integrated ambient owner.  Constructing
this dichotomy is the remaining affine-capacity obligation.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open PrimitiveAffineImprimitiveBlockTransfer

/-- **Complete primitive-affine consumer assembly.**

The primitive field uses the exhaustive primitive owner after instantiating
its finite package from the four published structural inputs.  The
imprimitive field applies the actual block-system transfer to the literal
component source. -/
noncomputable def preE7PrimitiveAffineConsumerData
    (published : PublishedPrimitiveAffineFiniteLiterature)
    (hcomp : PrimitiveCompositionLengthInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (components : PreE7PrimitiveAffineImprimitiveComponentSourceData
      hTraceyHalf hTraceyLog hTraceyPerm) :
    PreE7PrimitiveAffineConsumerData where
  primitive := by
    intro w U hw hprimitive P
    exact .inl
      ((publishedPrimitiveAffineFiniteInput published).primitiveOwner
        hcomp hgen hKP U hw hprimitive P)
  imprimitive := by
    intro w U hw basePoint block P
    exact match components.source w U hw basePoint block P with
      | .inl source => imprimitiveAffineComponentTransfer
          hTraceyHalf hTraceyLog hTraceyPerm hSimpleGen block P source
      | .inr ambient => ambient

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
