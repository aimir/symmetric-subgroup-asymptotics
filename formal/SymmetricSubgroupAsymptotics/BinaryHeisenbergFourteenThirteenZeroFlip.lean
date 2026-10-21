import SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenQuotientKernelInclusion
import SymmetricSubgroupAsymptotics.BinaryPairPairSumQuotientKernels
import SymmetricSubgroupAsymptotics.BinaryPairKernelCommutatorBits
import SymmetricSubgroupAsymptotics.BinaryAffineCommutatorKernelZeroLift

/-! One actual inner commutator gives a zero-class constant flip in the
original outer extension. Both inner and outer lift offsets are arbitrary;
the only linear premise is the SAME outer pair-sum preimage kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenThirteenZeroFlip
local instance heisenbergFourteenThirteenZeroFlipPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private theorem selected_mem : binaryVectorOfMask 8 135∈BinaryRegularEightNaturalRegistry.chart40.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem selected_commuting :
    (binaryPermutationRepresentation 8) (BinaryMenuCayley8T22.generators 1)
      (binaryVectorOfMask 8 135)-binaryVectorOfMask 8 135=0 := by decide +kernel
private theorem selected_constant :
    (binaryPermutationRepresentation 8) (BinaryMenuCayley8T22.generators 2)
      (binaryVectorOfMask 8 135)-binaryVectorOfMask 8 135=
        (fun _ : Fin 8 => (1 : ZMod 2)) := by decide +kernel

private theorem exists_selected_actual_rows {H : Subgroup (Equiv.Perm (Fin 16))}
    (E : SymmetricSubgroupAsymptotics.BinaryPairFrame H (Fin 8))
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hJ : E.kernelSpace=BinaryRegularEightNaturalRegistry.chart40.space) :
    ∃ (g h : H) (j : E.top.ker),
      E.top g=BinaryMenuCayley8T22.generators 2 ∧
      E.top h=BinaryMenuCayley8T22.generators 1 ∧
      E.bits j=binaryVectorOfMask 8 135 ∧ Commute h (j : H) := by
  let tg : E.top.range := ⟨BinaryMenuCayley8T22.generators 2,by
    rw [hH];exact Subgroup.subset_closure ⟨2,rfl⟩⟩
  let th : E.top.range := ⟨BinaryMenuCayley8T22.generators 1,by
    rw [hH];exact Subgroup.subset_closure ⟨1,rfl⟩⟩
  let g := E.affineTopLift tg
  let h := E.affineTopLift th
  have hg : E.top g=BinaryMenuCayley8T22.generators 2 :=
    congrArg Subtype.val (E.affineTopLift_top tg)
  have hh : E.top h=BinaryMenuCayley8T22.generators 1 :=
    congrArg Subtype.val (E.affineTopLift_top th)
  have hm : binaryVectorOfMask 8 135∈E.kernelSpace := by rw [hJ];exact selected_mem
  obtain ⟨j,hj⟩ := E.kernelSpaceHom_bijective.2 (Multiplicative.ofAdd ⟨binaryVectorOfMask 8 135,hm⟩)
  have hjbits : E.bits j=binaryVectorOfMask 8 135 :=
    congrArg (fun a : Multiplicative E.kernelSpace => a.toAdd.val) hj
  have hjcomm : E.kernelCommutator h j=1 := by
    apply E.bitsHom_injective
    rw [map_one]
    change Multiplicative.ofAdd (E.bits (E.kernelCommutator h j))=1
    have hb : E.bits (E.kernelCommutator h j)=0 := by
      rw [E.kernelCommutator_bits,hjbits]
      change (binaryPermutationRepresentation 8) (E.top h) (binaryVectorOfMask 8 135)-_=0
      rw [hh]
      exact selected_commuting
    rw [hb]
    rfl
  have hhj : Commute h (j : H) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←E.kernelCommutator_coe]
    exact congrArg (fun k : E.top.ker => (k : H)) hjcomm
  exact ⟨g,h,j,hg,hh,hjbits,hhj⟩

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : SymmetricSubgroupAsymptotics.BinaryPairFrame U (Fin 16))
    (E : SymmetricSubgroupAsymptotics.BinaryPairFrame F.top.range (Fin 8))
include F E

theorem exists_actual_zero_constant_flip
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hJ : E.kernelSpace=BinaryRegularEightNaturalRegistry.chart40.space)
    (hK : F.kernelSpace=BinaryRegularEightNaturalRegistry.chart33.space.comap E.pairSum) :
    ∃ z : E.top.ker,E.bits z=(fun _ : Fin 8 => (1 : ZMod 2)) ∧
      (z : F.top.range)∈Subgroup.center F.top.range ∧ F.affineClass (z : F.top.range)=0 := by
  obtain ⟨g,h,j,hg,hh,hjbits,hhj⟩ := exists_selected_actual_rows E hH hJ
  let z := E.kernelCommutator g j
  have hzbits : E.bits z=(fun _ : Fin 8 => (1 : ZMod 2)) := by
    rw [E.kernelCommutator_bits,hjbits]
    change (binaryPermutationRepresentation 8) (E.top g) (binaryVectorOfMask 8 135)-_= _
    rw [hg]
    exact selected_constant
  have hjact : F.affineQuotientRepresentation (j : F.top.range)=1 :=
    F.affineQuotient_eq_one_of_pairSum_preimage_kernel (w := 8) E BinaryRegularEightNaturalRegistry.chart33.space hK (j : F.top.range) j.property
  have hker := F.affineQuotient_kernel_inclusion_of_pairSum_preimage (w := 8) E BinaryRegularEightNaturalRegistry.chart33.space hK g h (by
    intro v hv
    change (binaryPermutationRepresentation 8) (E.top h) v-v∈_ at hv
    change (binaryPermutationRepresentation 8) (E.top g) v-v∈_
    rw [hh] at hv
    rw [hg]
    exact BinaryHeisenbergFourteenQuotientKernelInclusion.difference_kernel_inclusion v hv)
  have hzclass : F.affineClass (z : F.top.range)=0 := by
    change F.affineClass ((E.kernelCommutator g j : E.top.ker) : F.top.range)=0
    rw [E.kernelCommutator_coe]
    exact F.affineClass_commutator_eq_zero_of_kernel_inclusion g h (j : F.top.range) hjact hhj hker
  exact ⟨z,hzbits,E.kernel_mem_center_of_bits_one z hzbits,hzclass⟩
end BinaryPairFrame
end SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenThirteenZeroFlip
