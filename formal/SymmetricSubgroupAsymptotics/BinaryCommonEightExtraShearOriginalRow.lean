import SymmetricSubgroupAsymptotics.BinaryCommonEightExtraShearLeading
import SymmetricSubgroupAsymptotics.BinaryCommonEightOriginalTranslations
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

/-! The extra shear is an actual element of either original inner model,
and its lift through the actual outer top homomorphism is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem regular46_extra_bits_mem : binaryVectorOfMask 8 120 ∈
    BinaryRegularEightSquareCarry.K46 := by
  simp only [BinaryRegularEightSquareCarry.K46,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel

private theorem heisenberg14_extra_bits_mem : binaryVectorOfMask 8 120 ∈
    BinaryHeisenbergEightSquareCarry.K14 := by
  simp only [BinaryHeisenbergEightSquareCarry.K14,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel

namespace BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

def commonExtraShearRow (hzero : F.top.range = E.splitAffineAction)
    (hbits : binaryVectorOfMask 8 120 ∈ E.kernelSpace) : F.top.range :=
  E.originalZeroRow hzero 1 (binaryVectorOfMask 8 120) hbits

theorem commonExtraShearRow_pointLabels
    (hzero : F.top.range = E.splitAffineAction)
    (hbits : binaryVectorOfMask 8 120 ∈ E.kernelSpace) (x : Fin 16) :
    E.commonBooleanPointLabels (F.commonExtraShearRow E hzero hbits • x) =
      BinaryCommonEightExtraShearLeading.booleanPermutation (E.commonBooleanPointLabels x) := by
  change BinaryCommonEightShearCoordinates.pointLabels.symm
    (E.canonicalPointLabels (E.affinePermutation 1 (binaryVectorOfMask 8 120) x)) =
      BinaryCommonEightShearCoordinates.pointLabels.symm
        (BinaryCommonEightExtraShearLeading.originalPermutation
          (BinaryCommonEightShearCoordinates.pointLabels
            (BinaryCommonEightShearCoordinates.pointLabels.symm (E.canonicalPointLabels x))))
  rw [Equiv.apply_symm_apply]
  exact congrArg BinaryCommonEightShearCoordinates.pointLabels.symm
    (E.canonicalPointLabels_affinePermutation 1 (binaryVectorOfMask 8 120) x)

theorem exists_lift_commonExtraShearRow
    (hzero : F.top.range = E.splitAffineAction)
    (hbits : binaryVectorOfMask 8 120 ∈ E.kernelSpace) :
    ∃ u : U, ∀ j,
      (F.top u)⁻¹ (E.commonBooleanPointLabels.symm j) =
        E.commonBooleanPointLabels.symm
          (BinaryCommonEightExtraShearLeading.booleanPermutation.symm j) := by
  let t := F.commonExtraShearRow E hzero hbits
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective t
  have heq : F.top u = t.val := congrArg Subtype.val hu
  have hf (x : Fin 16) : E.commonBooleanPointLabels (F.top u x) =
      BinaryCommonEightExtraShearLeading.booleanPermutation (E.commonBooleanPointLabels x) := by
    rw [heq]
    exact F.commonExtraShearRow_pointLabels E hzero hbits x
  refine ⟨u, ?_⟩
  intro j
  apply (F.top u).injective
  simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  apply E.commonBooleanPointLabels.injective
  rw [hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (BinaryCommonEightExtraShearLeading.booleanPermutation.apply_symm_apply j).symm

theorem exists_lift_commonExtraShearRow_regular
    (hzero : F.top.range = E.splitAffineAction)
    (hK : E.kernelSpace = BinaryRegularEightSquareCarry.K46) :
    ∃ u : U, ∀ j,
      (F.top u)⁻¹ (E.commonBooleanPointLabels.symm j) =
        E.commonBooleanPointLabels.symm
          (BinaryCommonEightExtraShearLeading.booleanPermutation.symm j) := by
  apply F.exists_lift_commonExtraShearRow E hzero
  rw [hK]
  exact regular46_extra_bits_mem

theorem exists_lift_commonExtraShearRow_heisenberg
    (hzero : F.top.range = E.splitAffineAction)
    (hK : E.kernelSpace = BinaryHeisenbergEightSquareCarry.K14) :
    ∃ u : U, ∀ j,
      (F.top u)⁻¹ (E.commonBooleanPointLabels.symm j) =
        E.commonBooleanPointLabels.symm
          (BinaryCommonEightExtraShearLeading.booleanPermutation.symm j) := by
  apply F.exists_lift_commonExtraShearRow E hzero
  rw [hK]
  exact heisenberg14_extra_bits_mem

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
