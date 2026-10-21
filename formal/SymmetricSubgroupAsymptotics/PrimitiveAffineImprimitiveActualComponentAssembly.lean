import SymmetricSubgroupAsymptotics.PrimitiveAffineActualCapacityExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveAffineExceptionalActualAssembly

/-! Assemble actual component sources, intercepting every degree16 component
before the old finite composition package can be requested. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ActualAffineSources

def preE7PrimitiveAffineImprimitiveActualComponentSourceData
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
    by_cases hr16 : Nat.card block.Fibre = 16
    · letI actualComponentAssembly_nontrivial : Nontrivial block.Fibre :=
        Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
      exact .inr (sixteenGenericTranslationSource block P hTraceyPerm hr16)
    · exact match ComponentSource.capacityExhaustionAwaySixteen
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P hr16 hcomp with
        | .inl source => .inl source
        | .inr h => exceptional.consume hTraceyHalf hTraceyLog hTraceyRefined
            hTraceyPerm U hw basePoint block P h.down

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ActualAffineSources
