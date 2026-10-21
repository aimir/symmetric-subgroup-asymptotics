import SymmetricSubgroupAsymptotics.BinaryPairLargeKernelCenter
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSevenPlanes
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalPointCoordinates

/-! The original centre's kernel bits map to the literal constant line
under the same canonical coordinates. Large-kernel faithfulness also
puts the full original centre in that kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance canonicalCenterLineFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private theorem canonical_constant_one_eq_line :
    binaryEightCanonicalLayerChange (fun _ : Fin 16 => (1 : ZMod 2))=
      BinaryRegularFullConstantSevenPlanes.line.inclusion (fun _ : Fin 1 => 1) := by decide +kernel
namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]
include F E

theorem original_center_axis_le_canonical_line :
    (F.ambientAxis (Subgroup.center U)).map E.originalCoordinateEquiv.toLinearMap≤
      BinaryRegularFullConstantSevenPlanes.line.space := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  rintro v ⟨a,ha,rfl⟩
  obtain ⟨k,hk,rfl⟩ := (F.mem_ambientAxis (Subgroup.center U) a).mp ha
  change E.originalCoordinateEquiv (F.bits k)∈BinaryRegularFullConstantSevenPlanes.line.space
  rw [E.originalCoordinateEquiv_canonicalPointLabels]
  let c := F.bits k 0
  have he : (fun j => F.bits k (E.canonicalPointLabels.symm j))=
      c • (fun _ : Fin 16 => (1 : ZMod 2)) := by
    funext j
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using
      F.central_kernel_bits_constant k hk (E.canonicalPointLabels.symm j) (0 : Fin 16)
  rw [he,map_smul,canonical_constant_one_eq_line]
  exact BinaryRegularFullConstantSevenPlanes.line.space.smul_mem c ⟨_,rfl⟩

theorem original_center_le_kernel_of_fullconstant_space
    (hU : IsPGroup 2 U)
    (hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=
      BinaryRegularFullConstantPlaneOne.K.space) :
    Subgroup.center U≤F.top.ker := by
  have hd := E.originalCoordinateEquiv.finrank_map_eq F.kernelSpace
  rw [hspace,BinaryRegularFullConstantPlaneOne.K.finrank] at hd
  apply F.original_center_le_kernel_of_half_lt hU (0 : Fin 16)
  omega
end BinaryPairFrame
end SymmetricSubgroupAsymptotics
