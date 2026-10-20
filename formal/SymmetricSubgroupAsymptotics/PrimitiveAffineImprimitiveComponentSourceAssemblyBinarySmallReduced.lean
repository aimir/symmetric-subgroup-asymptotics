import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentSourceAssembly
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCapacityExhaustionBinarySmallReduced

/-! Isolated binary-small consumer route. Original datatypes, interfaces,
and finite certificate declarations are imported unchanged. Only the
changed consumer declarations and their private helper closure are copied. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffineImprimitiveBlockTransfer

namespace BinarySmallReduced

namespace PreE7PrimitiveAffineExceptionalCellConsumerData

end PreE7PrimitiveAffineExceptionalCellConsumerData

noncomputable def preE7PrimitiveAffineImprimitiveComponentSourceData
    (D : BinaryAffineSmallCatalogueData)
    (hcomp : PrimitiveCompositionLengthInput)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (exceptional : PreE7PrimitiveAffineExceptionalCellConsumerData) :
    PreE7PrimitiveAffineImprimitiveComponentSourceData
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm where
  source := by
    intro w U hw basePoint block P
    exact match _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.capacityExhaustion
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P D hcomp with
      | .inl source => .inl source
      | .inr h => exceptional.consume hTraceyHalf hTraceyLog hTraceyRefined
          hTraceyPerm U hw basePoint block P h.down

end BinarySmallReduced

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

