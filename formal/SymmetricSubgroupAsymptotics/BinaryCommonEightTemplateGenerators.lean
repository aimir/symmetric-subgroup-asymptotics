import SymmetricSubgroupAsymptotics.BinaryPairCommonShearOriginalGenerators
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

/-! Three literal critical kernel templates supply the common shear
operators on the original source. The axis is the whole actual outer
kernel, and no replacement normal subgroup or action is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem regular46_constant_mem : (fun _ : Fin 8 => (1 : ZMod 2)) ∈
    BinaryRegularEightSquareCarry.K46 := by
  simp only [BinaryRegularEightSquareCarry.K46,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel

private theorem heisenberg14_constant_mem : (fun _ : Fin 8 => (1 : ZMod 2)) ∈
    BinaryHeisenbergEightSquareCarry.K14 := by
  simp only [BinaryHeisenbergEightSquareCarry.K14,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel

private theorem regular23_constant_mem : (fun _ : Fin 8 => (1 : ZMod 2)) ∈
    (BinaryRegularEightNaturalRegistry.charts 23).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

namespace BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem uniform_generatedBy_six_of_regular_zero_kernel
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace = BinaryRegularEightSquareCarry.K46)
    (hW : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
        (BinaryRegular46GraphHeadRigidity.stateChart 0).space) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 6 := by
  apply F.uniform_generatedBy_six_of_original_common_shears E hzero
  · intro j
    rw [hH]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · rw [hK]
    exact regular46_constant_mem
  · intro b hb
    have hm := E.regular_zero_originalPointMonomial_mem
      (F.axisNaturalSubrepresentation F.top.ker) hW b hb
    change E.originalPointMonomial b ∈ F.ambientAxis F.top.ker at hm
    exact F.ambientAxis_le_kernelSpace F.top.ker hm

theorem uniform_generatedBy_six_of_heisenberg_zero_kernel
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace = BinaryHeisenbergEightSquareCarry.K14)
    (hW : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
        (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 6 := by
  apply F.uniform_generatedBy_six_of_original_common_shears E hzero
  · intro j
    rw [BinaryCommonEightShearCoordinates.regular_generators_are_heisenberg j, hH]
    exact Subgroup.subset_closure ⟨j.castSucc.castSucc, rfl⟩
  · rw [hK]
    exact heisenberg14_constant_mem
  · intro b hb
    have hm := E.heisenberg_zero_originalPointMonomial_mem
      (F.axisNaturalSubrepresentation F.top.ker) hW b hb
    change E.originalPointMonomial b ∈ F.ambientAxis F.top.ker at hm
    exact F.ambientAxis_le_kernelSpace F.top.ker hm

theorem uniform_generatedBy_six_of_elementary_zero_kernel
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (hW : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 6 := by
  apply F.uniform_generatedBy_six_of_original_common_shears E hzero
  · intro j
    rw [hH]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · rw [hK]
    exact regular23_constant_mem
  · intro b hb
    have hm := E.elementary_zero_originalPointMonomial_mem
      (F.axisNaturalSubrepresentation F.top.ker) hW b hb
    change E.originalPointMonomial b ∈ F.ambientAxis F.top.ker at hm
    exact F.ambientAxis_le_kernelSpace F.top.ker hm

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
