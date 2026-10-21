import SymmetricSubgroupAsymptotics.BinaryRegular45TwelveAnnihilator
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateQuotientAnnihilator
import SymmetricSubgroupAsymptotics.BinaryAffineDoubleCommutatorZeroLift
import SymmetricSubgroupAsymptotics.BinaryPairKernelCommutatorBits
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

/-! A particular ORIGINAL inner double commutator has constant bits and
zero outer affine class. The inner top lifts retain arbitrary offsets;
only the actual kernel and selected top images are used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped commutatorElement Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular45TwelveZeroFlip
local instance regular45TwelveZeroFlipPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private theorem mask_three_mem : binaryVectorOfMask 8 3∈BinaryRegularEightNaturalRegistry.chart45.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem selected_double_constant :
    (binaryPermutationRepresentation 8) (BinaryMenuCayley8T3.generators 2)
      ((binaryPermutationRepresentation 8) (BinaryMenuCayley8T3.generators 1)
        (binaryVectorOfMask 8 3)-binaryVectorOfMask 8 3)-
      ((binaryPermutationRepresentation 8) (BinaryMenuCayley8T3.generators 1)
        (binaryVectorOfMask 8 3)-binaryVectorOfMask 8 3)=
      (fun _ : Fin 8 => (1 : ZMod 2)) := by decide +kernel

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : SymmetricSubgroupAsymptotics.BinaryPairFrame U (Fin 16))
    (E : SymmetricSubgroupAsymptotics.BinaryPairFrame F.top.range (Fin 8))
include F E

theorem exists_actual_zero_constant_flip
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hJ : E.kernelSpace=BinaryRegularEightNaturalRegistry.chart45.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      BinarySplitRegular46FullConstantStabilizer.state.space) :
    ∃ z : E.top.ker,E.bits z=(fun _ : Fin 8 => (1 : ZMod 2)) ∧
      (z : F.top.range)∈Subgroup.center F.top.range ∧ F.affineClass (z : F.top.range)=0 := by
  let tg : E.top.range := ⟨BinaryMenuCayley8T3.generators 2,by
    rw [hH];exact Subgroup.subset_closure ⟨2,rfl⟩⟩
  let th : E.top.range := ⟨BinaryMenuCayley8T3.generators 1,by
    rw [hH];exact Subgroup.subset_closure ⟨1,rfl⟩⟩
  let g := E.affineTopLift tg
  let h := E.affineTopLift th
  have hg : E.top g=BinaryMenuCayley8T3.generators 2 :=
    congrArg Subtype.val (E.affineTopLift_top tg)
  have hh : E.top h=BinaryMenuCayley8T3.generators 1 :=
    congrArg Subtype.val (E.affineTopLift_top th)
  have hm : binaryVectorOfMask 8 3∈E.kernelSpace := by rw [hJ];exact mask_three_mem
  obtain ⟨j,hj⟩ := E.kernelSpaceHom_bijective.2 (Multiplicative.ofAdd ⟨binaryVectorOfMask 8 3,hm⟩)
  have hjbits : E.bits j=binaryVectorOfMask 8 3 :=
    congrArg (fun a : Multiplicative E.kernelSpace => a.toAdd.val) hj
  let z := E.kernelCommutator g (E.kernelCommutator h j)
  have hword : (z : F.top.range)=⁅g,⁅h,(j : F.top.range)⁆⁆ := by
    change ((E.kernelCommutator g (E.kernelCommutator h j) : E.top.ker) : F.top.range)=_
    rw [E.kernelCommutator_coe,E.kernelCommutator_coe]
  have hzbits : E.bits z=(fun _ : Fin 8 => (1 : ZMod 2)) := by
    rw [E.kernelCommutator_bits,E.kernelCommutator_bits,hjbits]
    change (binaryPermutationRepresentation 8) (E.top g)
      ((binaryPermutationRepresentation 8) (E.top h) (binaryVectorOfMask 8 3)-binaryVectorOfMask 8 3)-
      ((binaryPermutationRepresentation 8) (E.top h) (binaryVectorOfMask 8 3)-binaryVectorOfMask 8 3)=_
    rw [hg,hh]
    exact selected_double_constant
  have hjact : F.affineQuotientRepresentation (j : F.top.range)=1 :=
    F.affineQuotient_eq_one_of_original_coordinate_displacement E
      BinaryRegular45TwelveAnnihilator.K hS (j : F.top.range)
      (BinaryRegular45TwelveAnnihilator.kernel_displacement_mem_K E (j : F.top.range) j.property)
  have hAnn := F.affineQuotient_double_annihilator_of_original_coordinate E
    BinaryRegular45TwelveAnnihilator.K hS g h
    (BinaryRegular45TwelveAnnihilator.double_displacement_mem_K E g h hg hh)
  have hzclass : F.affineClass (z : F.top.range)=0 := by
    rw [hword]
    exact BinaryAffineDoubleCommutatorZeroLift.cocycle_double_commutator_eq_zero
      F.affineQuotientRepresentation F.affineClass F.affineClass_mul g h (j : F.top.range) hjact hAnn
  exact ⟨z,hzbits,E.kernel_mem_center_of_bits_one z hzbits,hzclass⟩
end BinaryPairFrame
end SymmetricSubgroupAsymptotics.BinaryRegular45TwelveZeroFlip
