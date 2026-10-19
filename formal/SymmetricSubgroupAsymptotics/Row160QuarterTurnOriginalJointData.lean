import SymmetricSubgroupAsymptotics.QuarterTurnPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.PureA4FourOriginalPairFrames
import SymmetricSubgroupAsymptotics.Row160OriginalAbelianAxes
import SymmetricSubgroupAsymptotics.QuarterTurnTwoOriginalJointData
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row160QuarterTurnOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPointTernaryQuarterTurnNormalGenerators (Model literalAction)
open QuarterTurnTwoOriginalJointData (rotation reflection mover)
def shift : Equiv.Perm (Fin 6) where
  toFun := ![3,0,5,2,1,4]
  invFun := ![1,4,3,0,5,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def points : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr shift (Equiv.refl (ZMod 2))).trans PureA4FourOriginalPairFrames.points

def codes : Fin 4 → Model := ![1,rotation,reflection,mover]
def tops : Fin 4 → Equiv.Perm (Fin 6) := fun i => literalAction (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row160Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row160Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row160Generators tops preserves
private theorem range_le : frame.top.range≤literalAction.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    BinaryPairFrame.ofGenerators_top_range points row160Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨codes i,rfl⟩
private theorem mover_mem : literalAction mover∈frame.top.range := by
  refine ⟨closureGenerators row160Generators 3,?_⟩
  exact BinaryPairFrame.ofGenerators_top_generator points row160Generators tops preserves 3
private theorem pair_uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) frame.top.range (Fin 6)) 1 := by
  apply BinaryTwoTernaryPairOperator.uniform_subgroup 0 frame.top.range
    (frame.top.rangeRestrict (closureGenerators row160Generators 1))
    (frame.top.rangeRestrict (closureGenerators row160Generators 3))
  · exact (BinaryPairFrame.ofGenerators_top_generator points row160Generators tops preserves 1).trans
      (by decide +kernel)
  · exact (BinaryPairFrame.ofGenerators_top_generator points row160Generators tops preserves 3).trans
      (by decide +kernel)
private theorem natural_two : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row160Interface.top (Fin 12)) 2 :=
  frame.permutationFunctionRepresentation_uniform_of_coordinateTop 1 pair_uniform

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row160Interface :=
  .ofExact (QuarterTurnPairFrameOriginalJointData.jointData row160Interface frame range_le
    mover mover_mem rfl pair_uniform Row160OriginalAbelianAxes.noTernary natural_two)
    (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row160QuarterTurnOriginalJointData
