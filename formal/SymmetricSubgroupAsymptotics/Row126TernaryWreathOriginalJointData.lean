import SymmetricSubgroupAsymptotics.TernaryPairWreathPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.PureA4FourOriginalPairFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row126TernaryWreathOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open TernaryPairWreathSixImage (Model action rotation swap)
abbrev points := PureA4FourOriginalPairFrames.points

def codes : Fin 3 → Model := ![1,rotation,swap]
def tops : Fin 3 → Equiv.Perm (Fin 6) := fun i => action (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row126Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row126Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row126Generators tops preserves

theorem image : frame.top.range=action.range := by
  apply (BinaryPairFrame.ofGenerators_top_range points row126Generators tops preserves).trans
  apply TernaryPairWreathSixImage.generated_range codes
  · exact Subgroup.subset_closure ⟨1,rfl⟩
  · exact Subgroup.subset_closure ⟨2,rfl⟩

private def cycle : frame.top.range := frame.top.rangeRestrict
  (closureGenerators row126Generators 1 * closureGenerators row126Generators 2)
private theorem cycle_val : (cycle : Equiv.Perm (Fin 6))=tops 1*tops 2 := by
  change frame.top (closureGenerators row126Generators 1 * closureGenerators row126Generators 2)=_
  rw [map_mul]
  exact congrArg₂ (fun a b : Equiv.Perm (Fin 6) => a*b)
    (BinaryPairFrame.ofGenerators_top_generator points row126Generators tops preserves 1)
    (BinaryPairFrame.ofGenerators_top_generator points row126Generators tops preserves 2)
private def pairWitness : LiteralCyclicOrbitWitness frame.top.range 1 where
  element := cycle
  representative := ![0]
  orbitIndex := fun _ => 0
  exponent := ![0,5,2,1,4,3]
  point_eq := by
    intro x
    change ((cycle : Equiv.Perm (Fin 6)) ^ (![0,5,2,1,4,3] x : Fin 6).val) 0=x
    rw [cycle_val]
    revert x
    decide +kernel

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row126Interface :=
  .ofExact (TernaryPairWreathPairFrameOriginalJointData.jointData row126Interface frame image
    (pairWitness.uniform (ZMod 2))
    PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily.row126Natural) (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row126TernaryWreathOriginalJointData
