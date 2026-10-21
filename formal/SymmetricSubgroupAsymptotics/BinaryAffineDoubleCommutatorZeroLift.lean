import SymmetricSubgroupAsymptotics.BinaryPairAffineCoboundary

/-! A local annihilator of one cocycle restriction supplies an actual
zero-offset double-commutator lift. No whole extension is split, and no
normal-subgroup catalogue or full cocycle table is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryAffineDoubleCommutatorZeroLift
variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (rho : Representation (ZMod 2) G V)

private theorem action_commutator_eq_one (g j : G) (hj : rho j=1) :
    rho ⁅g,j⁆=1 := by
  change ⁅g,j⁆∈rho.ker
  rw [commutatorElement_def]
  exact rho.ker.mul_mem
    (Subgroup.Normal.conj_mem (inferInstance : rho.ker.Normal) j hj g)
    (rho.ker.inv_mem hj)

/-- The restriction need only be trivial at the ONE right-hand element. -/
theorem cocycle_commutator_eq_difference (c : G → V)
    (hmul : ∀ g h,c (g*h)=rho g (c h)+c g)
    (g j : G) (hj : rho j=1) : c ⁅g,j⁆=rho g (c j)-c j := by
  let r := ⁅g,j⁆
  have hr : rho r=1 := action_commutator_eq_one rho g j hj
  have hrj : rho (r*j)=1 := by rw [map_mul,hr,hj,mul_one]
  have hproduct : g*j=(r*j)*g := by
    dsimp only [r]
    simp only [commutatorElement_def]
    group
  have hc := congrArg c hproduct
  rw [hmul g j,hmul (r*j) g,hmul r j,hrj,hr] at hc
  simp only [Module.End.one_apply] at hc
  have hc' : rho g (c j)=c j+c r := by
    apply add_left_cancel (a := c g)
    calc
      c g+rho g (c j)=rho g (c j)+c g := add_comm _ _
      _=c g+(c j+c r) := hc
  exact (eq_sub_iff_add_eq).mpr ((add_comm (c r) (c j)).trans hc'.symm)

/-- One selected double-difference annihilator kills the exact retained
cocycle at the corresponding actual double commutator. -/
theorem cocycle_double_commutator_eq_zero (c : G → V)
    (hmul : ∀ g h,c (g*h)=rho g (c h)+c g)
    (g h j : G) (hj : rho j=1)
    (hAnn : ∀ v : V,rho g (rho h v-v)-(rho h v-v)=0) :
    c ⁅g,⁅h,j⁆⁆=0 := by
  rw [cocycle_commutator_eq_difference rho c hmul g ⁅h,j⁆
    (action_commutator_eq_one rho h j hj),
    cocycle_commutator_eq_difference rho c hmul h j hj]
  exact hAnn (c j)
end SymmetricSubgroupAsymptotics.BinaryAffineDoubleCommutatorZeroLift

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
include F

/-- All original offsets remain; only this particular class is proved zero. -/
theorem affinePermutation_zero_mem_of_double_commutator_annihilator
    (g h j : F.top.range) (hj : F.affineQuotientRepresentation j=1)
    (hAnn : ∀ v : (I → ZMod 2) ⧸ F.kernelSpace,
      F.affineQuotientRepresentation g (F.affineQuotientRepresentation h v-v)-
        (F.affineQuotientRepresentation h v-v)=0) :
    F.affinePermutation (⁅g,⁅h,j⁆⁆ : F.top.range).val 0∈U := by
  have hc := BinaryAffineDoubleCommutatorZeroLift.cocycle_double_commutator_eq_zero
    F.affineQuotientRepresentation F.affineClass F.affineClass_mul g h j hj hAnn
  obtain ⟨u,hu,hzero⟩ := (F.affine_graph_fibre ⁅g,⁅h,j⁆⁆ 0).mpr (by rw [map_zero,hc])
  have hp : F.top u=(⁅g,⁅h,j⁆⁆ : F.top.range).val := congrArg Subtype.val hu
  have he := F.affinePermutation_original u
  rw [hp,hzero] at he
  exact he.symm ▸ u.property
end SymmetricSubgroupAsymptotics.BinaryPairFrame
