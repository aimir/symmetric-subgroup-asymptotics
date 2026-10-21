import SymmetricSubgroupAsymptotics.BinaryAffineDoubleCommutatorZeroLift

/-! A commuting actual inner row forces its retained cocycle value into
one difference kernel. Inclusion in another selected difference kernel
then proves one actual commutator's zero offset class. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryAffineCommutatorKernelZeroLift
variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (rho : Representation (ZMod 2) G V)

theorem cocycle_commutator_eq_zero_of_kernel_inclusion (c : G → V)
    (hmul : ∀ g h,c (g*h)=rho g (c h)+c g)
    (g h j : G) (hj : rho j=1) (hhj : Commute h j)
    (hker : ∀ v : V,rho h v-v=0 → rho g v-v=0) : c ⁅g,j⁆=0 := by
  have hone : c 1=0 := by
    have hh : c 1=c 1+c 1 := by simpa only [one_mul,map_one,Module.End.one_apply] using hmul 1 1
    have hh' : c 1+0=c 1+c 1 := by simpa only [add_zero] using hh
    exact (add_left_cancel hh').symm
  have hhzero : rho h (c j)-c j=0 := by
    have hc := BinaryAffineDoubleCommutatorZeroLift.cocycle_commutator_eq_difference rho c hmul h j hj
    have he : ⁅h,j⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr hhj.eq
    rw [he,hone] at hc
    exact hc.symm
  rw [BinaryAffineDoubleCommutatorZeroLift.cocycle_commutator_eq_difference rho c hmul g j hj]
  exact hker (c j) hhzero
end SymmetricSubgroupAsymptotics.BinaryAffineCommutatorKernelZeroLift

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
include F

theorem affineClass_commutator_eq_zero_of_kernel_inclusion
    (g h j : F.top.range) (hj : F.affineQuotientRepresentation j=1) (hhj : Commute h j)
    (hker : ∀ v : (I → ZMod 2) ⧸ F.kernelSpace,
      F.affineQuotientRepresentation h v-v=0 → F.affineQuotientRepresentation g v-v=0) :
    F.affineClass ⁅g,j⁆=0 :=
  BinaryAffineCommutatorKernelZeroLift.cocycle_commutator_eq_zero_of_kernel_inclusion
    F.affineQuotientRepresentation F.affineClass F.affineClass_mul g h j hj hhj hker
end SymmetricSubgroupAsymptotics.BinaryPairFrame
