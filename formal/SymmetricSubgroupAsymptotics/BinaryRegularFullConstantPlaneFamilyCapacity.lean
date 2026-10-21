import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantSelectedCapacity
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneCode2
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneCode3
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneCode4
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneCode5
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneCode6
import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneCode7

/-! The seven literal planes all have the independently checked selected
joint capacity at most128. Six new sparse scalar certificates supplement
the original PASS plane-one pilot; actions/candidates reuse its constants. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneFamilyCapacity
open BinaryRegularFullConstantSelectedCapacity
private theorem zero_le_one : (BinaryRegularFullConstantSevenPlanes.plane 0).space≤
    BinaryRegularFullConstantPlaneOne.plane.space := by
  apply (BinaryRegularFullConstantSevenPlanes.plane 0).le_of_basis_mem
  intro j
  have hh : ∀ j : Fin 2,(BinaryRegularFullConstantSevenPlanes.plane 0).inclusion (Pi.single j 1)∈
      BinaryRegularFullConstantPlaneOne.plane.space := by
    simp only [BinaryCoordinateSpace.mem_iff]
    decide +kernel
  exact hh j
private theorem one_le_zero : BinaryRegularFullConstantPlaneOne.plane.space≤
    (BinaryRegularFullConstantSevenPlanes.plane 0).space := by
  apply BinaryRegularFullConstantPlaneOne.plane.le_of_basis_mem
  intro j
  have hh : ∀ j : Fin 2,BinaryRegularFullConstantPlaneOne.plane.inclusion (Pi.single j 1)∈
      (BinaryRegularFullConstantSevenPlanes.plane 0).space := by
    simp only [BinaryCoordinateSpace.mem_iff]
    decide +kernel
  exact hh j
private theorem plane_zero_eq : (BinaryRegularFullConstantSevenPlanes.plane 0).space=
    BinaryRegularFullConstantPlaneOne.plane.space := le_antisymm zero_le_one one_le_zero

theorem selected_joint_capacity_le (i : Fin 7) :
    Nat.card (binaryCoordinateFixedDisplacements K BinaryRegularFullConstantPlaneOne.action
      (BinaryRegularFullConstantSevenPlanes.plane i).space)*
      Nat.card (Allowed (BinaryRegularFullConstantSevenPlanes.plane i).space)≤128 := by
  fin_cases i
  · change Nat.card (binaryCoordinateFixedDisplacements K BinaryRegularFullConstantPlaneOne.action
        (BinaryRegularFullConstantSevenPlanes.plane 0).space)*
        Nat.card (Allowed (BinaryRegularFullConstantSevenPlanes.plane 0).space)≤128
    rw [plane_zero_eq]
    exact (Nat.mul_le_mul BinaryRegularFullConstantPlaneOne.fixed_card_le
      BinaryRegularFullConstantPlaneOne.allowed_card_le).trans (by decide)
  · have hh := Nat.mul_le_mul BinaryRegularFullConstantPlaneCode2.fixed_card_le
      BinaryRegularFullConstantPlaneCode2.allowed_card_le
    have hb := hh.trans (by decide : _≤128)
    simpa only [BinaryRegularFullConstantPlaneCode2.plane,
      BinaryRegularFullConstantPlaneCode2.action,BinaryRegularFullConstantPlaneCode2.candidateAction] using hb
  · have hh := Nat.mul_le_mul BinaryRegularFullConstantPlaneCode3.fixed_card_le
      BinaryRegularFullConstantPlaneCode3.allowed_card_le
    have hb := hh.trans (by decide : _≤128)
    simpa only [BinaryRegularFullConstantPlaneCode3.plane,
      BinaryRegularFullConstantPlaneCode3.action,BinaryRegularFullConstantPlaneCode3.candidateAction] using hb
  · have hh := Nat.mul_le_mul BinaryRegularFullConstantPlaneCode4.fixed_card_le
      BinaryRegularFullConstantPlaneCode4.allowed_card_le
    have hb := hh.trans (by decide : _≤128)
    simpa only [BinaryRegularFullConstantPlaneCode4.plane,
      BinaryRegularFullConstantPlaneCode4.action,BinaryRegularFullConstantPlaneCode4.candidateAction] using hb
  · have hh := Nat.mul_le_mul BinaryRegularFullConstantPlaneCode5.fixed_card_le
      BinaryRegularFullConstantPlaneCode5.allowed_card_le
    have hb := hh.trans (by decide : _≤128)
    simpa only [BinaryRegularFullConstantPlaneCode5.plane,
      BinaryRegularFullConstantPlaneCode5.action,BinaryRegularFullConstantPlaneCode5.candidateAction] using hb
  · have hh := Nat.mul_le_mul BinaryRegularFullConstantPlaneCode6.fixed_card_le
      BinaryRegularFullConstantPlaneCode6.allowed_card_le
    have hb := hh.trans (by decide : _≤128)
    simpa only [BinaryRegularFullConstantPlaneCode6.plane,
      BinaryRegularFullConstantPlaneCode6.action,BinaryRegularFullConstantPlaneCode6.candidateAction] using hb
  · have hh := Nat.mul_le_mul BinaryRegularFullConstantPlaneCode7.fixed_card_le
      BinaryRegularFullConstantPlaneCode7.allowed_card_le
    have hb := hh.trans (by decide : _≤128)
    simpa only [BinaryRegularFullConstantPlaneCode7.plane,
      BinaryRegularFullConstantPlaneCode7.action,BinaryRegularFullConstantPlaneCode7.candidateAction] using hb
end SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneFamilyCapacity
