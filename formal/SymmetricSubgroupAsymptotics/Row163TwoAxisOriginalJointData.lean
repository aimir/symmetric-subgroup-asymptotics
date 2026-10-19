import SymmetricSubgroupAsymptotics.TwoAxisPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.Row163OriginalAbelianAxes
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row163TwoAxisOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPointTernaryAxesNormalGenerators (Model literalAction translation)
abbrev pointChart := PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pointChart
def codes : Fin 5 → Model :=
  ![1,1,(translation,translation),TwoAxisSixActualUpper.inversionLift,TwoAxisSixActualUpper.swapLift]
def tops : Fin 5 → Equiv.Perm (Fin 6) := fun i => literalAction (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves pointChart (row163Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row163Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row163Generators tops preserves
private theorem range_le : frame.top.range≤literalAction.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    BinaryPairFrame.ofGenerators_top_range pointChart row163Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨codes i,rfl⟩
private theorem inversion_mem : literalAction TwoAxisSixActualUpper.inversionLift∈frame.top.range := by
  refine ⟨closureGenerators row163Generators 3,?_⟩
  exact BinaryPairFrame.ofGenerators_top_generator pointChart row163Generators tops preserves 3
private theorem swap_mem : literalAction TwoAxisSixActualUpper.swapLift∈frame.top.range := by
  refine ⟨closureGenerators row163Generators 4,?_⟩
  exact BinaryPairFrame.ofGenerators_top_generator pointChart row163Generators tops preserves 4
private theorem pair_uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) frame.top.range (Fin 6)) 1 :=
  PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pair_uniform 1
    row163Generators tops 2 4 preserves (by decide +kernel) (by decide +kernel)
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row163Interface :=
  .ofExact (TwoAxisPairFrameOriginalJointData.jointData row163Interface frame range_le
    inversion_mem swap_mem pair_uniform Row163OriginalAbelianAxes.cover
    Row163OriginalAbelianAxes.cover_surjective Row163OriginalAbelianAxes.noTernary
    PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.row163Natural) (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row163TwoAxisOriginalJointData
