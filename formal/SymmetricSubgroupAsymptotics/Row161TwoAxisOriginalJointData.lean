import SymmetricSubgroupAsymptotics.TwoAxisPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.Row161OriginalAbelianAxes
import SymmetricSubgroupAsymptotics.PureA4FourOriginalPairFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row161TwoAxisOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPointTernaryAxesNormalGenerators (Model literalAction translation)
def shift : Equiv.Perm (Fin 6) where
  toFun := ![2,1,4,3,0,5]
  invFun := ![4,1,0,3,2,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr shift (Equiv.refl (ZMod 2))).trans PureA4FourOriginalPairFrames.points
def codes : Fin 4 → Model :=
  ![1,(translation,translation^2),TwoAxisSixActualUpper.inversionLift,TwoAxisSixActualUpper.swapLift]
def tops : Fin 4 → Equiv.Perm (Fin 6) := fun i => literalAction (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves pointChart (row161Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row161Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row161Generators tops preserves
private theorem range_le : frame.top.range≤literalAction.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    BinaryPairFrame.ofGenerators_top_range pointChart row161Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨codes i,rfl⟩
private theorem inversion_mem : literalAction TwoAxisSixActualUpper.inversionLift∈frame.top.range := by
  refine ⟨closureGenerators row161Generators 2,?_⟩
  exact BinaryPairFrame.ofGenerators_top_generator pointChart row161Generators tops preserves 2
private theorem swap_mem : literalAction TwoAxisSixActualUpper.swapLift∈frame.top.range := by
  refine ⟨closureGenerators row161Generators 3,?_⟩
  exact BinaryPairFrame.ofGenerators_top_generator pointChart row161Generators tops preserves 3
private def cycle : frame.top.range := frame.top.rangeRestrict
  (closureGenerators row161Generators 1 * closureGenerators row161Generators 3)
private theorem cycle_val : (cycle : Equiv.Perm (Fin 6))=tops 1*tops 3 := by
  change frame.top (closureGenerators row161Generators 1 * closureGenerators row161Generators 3)=_
  rw [map_mul]
  exact congrArg₂ (fun a b : Equiv.Perm (Fin 6) => a*b)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row161Generators tops preserves 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row161Generators tops preserves 3)
private def pairWitness : LiteralCyclicOrbitWitness frame.top.range 1 where
  element := cycle
  representative := ![0]
  orbitIndex := fun _ => 0
  exponent := ![0,3,2,5,4,1]
  point_eq := by
    intro x
    change ((cycle : Equiv.Perm (Fin 6)) ^ (![0,3,2,5,4,1] x : Fin 6).val) 0=x
    rw [cycle_val]
    revert x
    decide +kernel
private theorem pair_uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) frame.top.range (Fin 6)) 1 :=
  pairWitness.uniform (ZMod 2)
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row161Interface :=
  .ofExact (TwoAxisPairFrameOriginalJointData.jointData row161Interface frame range_le
    inversion_mem swap_mem pair_uniform Row161OriginalAbelianAxes.cover
    Row161OriginalAbelianAxes.cover_surjective Row161OriginalAbelianAxes.noTernary
    PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily.row161Natural) (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row161TwoAxisOriginalJointData
