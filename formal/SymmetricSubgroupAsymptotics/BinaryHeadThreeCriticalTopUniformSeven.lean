import SymmetricSubgroupAsymptotics.BinaryPairAxisHeadThreeExtraUniformSeven
import SymmetricSubgroupAsymptotics.BinaryCommonEightExtraShearOriginalRow

/-! Both remaining rank-six inner templates supply the additional genuine
top shear. A head-three whole outer kernel then has original module width
seven, with no invariant-module census or pure outer-lift assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem headThree_regular46_constant_mem : (fun _ : Fin 8 => (1 : ZMod 2)) ∈
    BinaryRegularEightSquareCarry.K46 := by
  simp only [BinaryRegularEightSquareCarry.K46,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel

private theorem headThree_heisenberg14_constant_mem : (fun _ : Fin 8 => (1 : ZMod 2)) ∈
    BinaryHeisenbergEightSquareCarry.K14 := by
  simp only [BinaryHeisenbergEightSquareCarry.K14,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel

namespace BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem uniform_generatedBy_seven_of_head_three_original_extra_shear
    (hzero : F.top.range = E.splitAffineAction)
    (hreg : ∀ j : Fin 3, BinaryMenuCayley8T3.generators j ∈ E.top.range)
    (hconst : (fun _ : Fin 8 => (1 : ZMod 2)) ∈ E.kernelSpace)
    (hextra : ∃ u : U, ∀ j,
      (F.top u)⁻¹ (E.commonBooleanPointLabels.symm j) = E.commonBooleanPointLabels.symm
        (BinaryCommonEightExtraShearLeading.booleanPermutation.symm j))
    (hhead : 3 ≤ Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2)))) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  let e := E.commonBooleanPointLabels
  apply F.uniform_generatedBy_seven_of_axis_head_three_extra e _ hextra hhead
  intro i
  let t := E.commonTranslationRow hzero hreg hconst i
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective t
  have heq : F.top u = t.val := congrArg Subtype.val hu
  have hf (x : Fin 16) : e (F.top u x) = flipIndex i (e x) := by
    rw [heq]
    exact E.commonTranslationRow_pointLabels hzero hreg hconst i x
  refine ⟨u, ?_⟩
  intro j
  apply (F.top u).injective
  simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  apply e.injective
  rw [hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply, flipIndex_involutive]

theorem uniform_generatedBy_seven_of_head_three_regular46
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace = BinaryRegularEightSquareCarry.K46)
    (hhead : 3 ≤ Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2)))) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  apply F.uniform_generatedBy_seven_of_head_three_original_extra_shear E hzero _ _
    (F.exists_lift_commonExtraShearRow_regular E hzero hK) hhead
  · intro j
    rw [hH]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · rw [hK]
    exact headThree_regular46_constant_mem

theorem uniform_generatedBy_seven_of_head_three_heisenberg14
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : E.kernelSpace = BinaryHeisenbergEightSquareCarry.K14)
    (hhead : 3 ≤ Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2)))) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  apply F.uniform_generatedBy_seven_of_head_three_original_extra_shear E hzero _ _
    (F.exists_lift_commonExtraShearRow_heisenberg E hzero hK) hhead
  · intro j
    rw [BinaryCommonEightShearCoordinates.regular_generators_are_heisenberg j, hH]
    exact Subgroup.subset_closure ⟨j.castSucc.castSucc, rfl⟩
  · rw [hK]
    exact headThree_heisenberg14_constant_mem

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
