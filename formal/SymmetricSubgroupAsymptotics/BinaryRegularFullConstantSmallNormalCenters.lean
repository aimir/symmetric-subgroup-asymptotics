import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantNormalFourCover
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneFamilyCapacity

/-! The seven-plane geometry bounds the actual normal quotients of
orders two/four. These are the only small-derived-denominator obligations
in the generic512-derived packet; the original outer action is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
private theorem fullconstant_small_line_basis : ∀ j : Fin 1,
    BinaryRegularFullConstantSevenPlanes.line.inclusion (Pi.single j 1)∈
      BinaryRegularFullConstantPlaneOne.plane.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]
include F E

theorem fullconstant_normal_two_quotient_center_card_le_eight
    (hU : IsPGroup 2 U)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      BinaryRegularFullConstantPlaneOne.K.space)
    (L : Subgroup U) [L.Normal] (hcard : Nat.card L=2) :
    Nat.card (Subgroup.center (U ⧸ L))≤8 := by
  have hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=
      BinaryRegularFullConstantPlaneOne.K.space := by
    change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
    simpa only [F.original_ambientAxis_kernel] using hS
  have hZK := F.original_center_le_kernel_of_fullconstant_space E hU hspace
  have hLZ := NormalOrderTwo.le_center L hcard
  have hLK : L≤F.top.ker := hLZ.trans hZK
  have hA : (F.ambientAxis L).map E.originalCoordinateEquiv.toLinearMap≤
      BinaryRegularFullConstantPlaneOne.plane.space := by
    apply le_trans ?_ (BinaryRegularFullConstantSevenPlanes.line.le_of_basis_mem _ fullconstant_small_line_basis)
    apply le_trans ?_ (F.original_center_axis_le_canonical_line E)
    rintro v ⟨a,ha,rfl⟩
    obtain ⟨k,hk,rfl⟩ := (F.mem_ambientAxis L a).mp ha
    exact ⟨_,(F.mem_ambientAxis (Subgroup.center U) _).mpr ⟨k,hLZ hk,rfl⟩,rfl⟩
  have hp := BinaryRegularFullConstantPlaneOneActual.BinaryPairFrame.original_normal_quotient_center_capacity_le
    F E hzero hH hK hS L hLK hA
  rw [hcard] at hp
  omega

theorem fullconstant_normal_four_quotient_center_card_le_thirty_two
    (hU : IsPGroup 2 U)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      BinaryRegularFullConstantPlaneOne.K.space)
    (L : Subgroup U) [L.Normal] (hcard : Nat.card L=4) :
    Nat.card (Subgroup.center (U ⧸ L))≤32 := by
  have hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=
      BinaryRegularFullConstantPlaneOne.K.space := by
    change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
    simpa only [F.original_ambientAxis_kernel] using hS
  obtain ⟨hLK,i,hi⟩ := F.fullconstant_normal_four_original_coordinate_cover E hU hzero hH hK hspace L hcard
  have hp := BinaryRegularFullConstantSelectedCapacity.BinaryPairFrame.original_normal_quotient_center_capacity_le_selected
    F E hzero hH hK hS (BinaryRegularFullConstantSevenPlanes.plane i).space L hLK hi
  have hb := hp.trans (BinaryRegularFullConstantPlaneFamilyCapacity.selected_joint_capacity_le i)
  rw [hcard] at hb
  omega
end BinaryPairFrame
end SymmetricSubgroupAsymptotics
