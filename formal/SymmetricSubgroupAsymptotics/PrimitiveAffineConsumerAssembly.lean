import SymmetricSubgroupAsymptotics.PrimitiveAffinePublishedSmallStructuralInput
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentTransfer
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly

/-!
# Assemble the primitive-affine consumer

The primitive branch is the exhaustive consumer already obtained from the
published finite affine inputs and the generic infinite-degree estimates.
The imprimitive branch is supplied by the group-native component source on
the literal minimal block system and the actual wreath transfer.

Keeping the component-source package separate from the published finite
input records the theorem boundary faithfully.  It is a project estimate on
the actual block system, whereas the primitive finite package consists only
of the cited catalogue and linear-group facts.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open PrimitiveAffineImprimitiveBlockTransfer

/-- Component-native estimates for every affine primitive component that can
occur in the selected original minimal block system.  The source is attached
to the literal component and block map; no `PreE7NonPairActionClass` is
manufactured for the component. -/
structure PreE7PrimitiveAffineImprimitiveComponentSourceData : Type 1 where
  source : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    (P : PrimitiveAffineProfile block.Component block.Fibre) →
    ComponentSource block P

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
    (components : PreE7PrimitiveAffineImprimitiveComponentSourceData) :
    PreE7PrimitiveAffineConsumerData where
  primitive := by
    intro w U hw hprimitive P
    exact .inl
      ((publishedPrimitiveAffineFiniteInput published).primitiveOwner
        hcomp hgen hKP U hw hprimitive P)
  imprimitive := by
    intro w U hw basePoint block P
    exact imprimitiveAffineComponentTransfer block P
      (components.source w U hw basePoint block P)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
