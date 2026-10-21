import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups

/-! Actual kernel commutators retain their original ambient word and
literal bits. In particular a constant-bit actual kernel element is
central without any split-model or lift-offset premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)} (E : BinaryPairFrame U (Fin w))
include E

def kernelCommutator (g : U) (k : E.top.ker) : E.top.ker := MulAut.conjNormal g k*k⁻¹

theorem kernelCommutator_coe (g : U) (k : E.top.ker) :
    ((E.kernelCommutator g k : E.top.ker) : U)=⁅g,(k : U)⁆ := rfl

theorem kernelCommutator_bits (g : U) (k : E.top.ker) :
    E.bits (E.kernelCommutator g k)=
      E.coordinateTopAction (E.top.rangeRestrict g) (E.bits k)-E.bits k := by
  letI : IsMulCommutative E.top.ker := ⟨⟨fun a b => E.bitsHom_injective (by
    rw [map_mul,map_mul,mul_comm])⟩⟩
  change E.bits (MulAut.conjNormal g k*k⁻¹)=_
  rw [mul_comm' (MulAut.conjNormal g k) k⁻¹]
  exact E.bits_commutator g k

theorem kernel_mem_center_of_bits_one (k : E.top.ker)
    (hk : E.bits k=(fun _ : Fin w => (1 : ZMod 2))) : (k : U)∈Subgroup.center U := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hbits : E.bits (MulAut.conjNormal g k)=E.bits k := by
    rw [←E.coordinateTopAction_bits,hk]
    rfl
  have he : MulAut.conjNormal g k=k := E.bitsHom_injective (congrArg Multiplicative.ofAdd hbits)
  have hm := congrArg (fun z : E.top.ker => (z : U)) he
  change g*(k : U)*g⁻¹=(k : U) at hm
  have hh := congrArg (fun z : U => z*g) hm
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
end SymmetricSubgroupAsymptotics.BinaryPairFrame
