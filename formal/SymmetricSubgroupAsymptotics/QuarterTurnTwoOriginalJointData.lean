import SymmetricSubgroupAsymptotics.QuarterTurnPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.QuarterTurnTwoOriginalNoTernary
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuarterTurnTwoOriginalJointData
open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPointTernaryQuarterTurnNormalGenerators (Model gen literalAction)
abbrev pointChart := PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pointChart

def rotation : Model := ⟨Multiplicative.ofAdd (![1,0] : Fin 2 → ZMod 3),1⟩
def reflection : Model := ⟨Multiplicative.ofAdd (![0,2] : Fin 2 → ZMod 3),Multiplicative.ofAdd 2⟩
def mover : Model := ⟨Multiplicative.ofAdd (![2,1] : Fin 2 → ZMod 3),gen⟩

namespace Row162
def codes : Fin 5 → Model := ![1,1,rotation,reflection,mover]
def tops : Fin 5 → Equiv.Perm (Fin 6) := fun i => literalAction (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves pointChart (row162Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row162Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row162Generators tops preserves
private theorem range_le : frame.top.range≤literalAction.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    BinaryPairFrame.ofGenerators_top_range pointChart row162Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨codes i,rfl⟩
private theorem mover_mem : literalAction mover∈frame.top.range := by
  refine ⟨closureGenerators row162Generators 4,?_⟩
  exact BinaryPairFrame.ofGenerators_top_generator pointChart row162Generators tops preserves 4
private theorem pair_uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) frame.top.range (Fin 6)) 1 :=
  PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pair_uniform 0
    row162Generators tops 2 4 preserves (by decide +kernel) (by decide +kernel)
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row162Interface :=
  .ofExact (QuarterTurnPairFrameOriginalJointData.jointData row162Interface frame range_le
    mover mover_mem rfl pair_uniform QuarterTurnTwoOriginalNoTernary.row162
    PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.row162Natural) (by decide +kernel)
end Row162

namespace Row199
def codes : Fin 4 → Model := ![1,rotation,reflection,mover]
def tops : Fin 4 → Equiv.Perm (Fin 6) := fun i => literalAction (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves pointChart (row199Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row199Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row199Generators tops preserves
private theorem range_le : frame.top.range≤literalAction.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    BinaryPairFrame.ofGenerators_top_range pointChart row199Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨codes i,rfl⟩
private theorem mover_mem : literalAction mover∈frame.top.range := by
  refine ⟨closureGenerators row199Generators 3,?_⟩
  exact BinaryPairFrame.ofGenerators_top_generator pointChart row199Generators tops preserves 3
private theorem pair_uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) frame.top.range (Fin 6)) 1 :=
  PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pair_uniform 0
    row199Generators tops 1 3 preserves (by decide +kernel) (by decide +kernel)
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row199Interface :=
  .ofExact (QuarterTurnPairFrameOriginalJointData.jointData row199Interface frame range_le
    mover mover_mem rfl pair_uniform QuarterTurnTwoOriginalNoTernary.row199
    PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.row199Natural) (by decide +kernel)
end Row199
end SymmetricSubgroupAsymptotics.QuarterTurnTwoOriginalJointData
