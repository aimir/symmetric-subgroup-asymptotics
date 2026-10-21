import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalCenterLine

/-! Cardinalities of the original zero-top-image normal are preserved
by both actual bits and the same reversible original-coordinate map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
include F E

theorem original_coordinate_axis_card_of_le_kernel
    (N : Subgroup U) (hN : N≤F.top.ker) :
    Nat.card ((F.ambientAxis N).map E.originalCoordinateEquiv.toLinearMap)=Nat.card N := by
  have hm := Nat.card_congr (E.originalCoordinateEquiv.submoduleMap (F.ambientAxis N)).toEquiv
  calc
    _ = Nat.card (F.ambientAxis N) := hm.symm
    _ = Nat.card (F.top.ker⊓N : Subgroup U) := F.axis_card_eq_kernel_intersection N
    _ = Nat.card N := by rw [inf_eq_right.mpr hN]

theorem original_fullconstant_center_card_le_two
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=
      BinaryRegularFullConstantPlaneOne.K.space) :
    Nat.card (Subgroup.center U)≤2 := by
  have hN := F.original_center_le_kernel_of_fullconstant_space E hU hspace
  have ha := F.original_center_axis_le_canonical_line E
  have hc := Nat.card_le_card_of_injective (Submodule.inclusion ha)
    (Submodule.inclusion_injective ha)
  rw [F.original_coordinate_axis_card_of_le_kernel E (Subgroup.center U) hN,
    BinaryRegularFullConstantSevenPlanes.line.card] at hc
  exact hc
end SymmetricSubgroupAsymptotics.BinaryPairFrame
