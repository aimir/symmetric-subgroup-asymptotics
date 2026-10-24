import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeLowering
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeRaising

/-! A first non-defining source root identity at the next height.
The two original paths E1(v9) and E0(v8) agree because they have the
same positive H1 weight and the same F1 lowering. This demonstrates
the sparse source-height comparison without any matrix pullback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalFirstLoweringComparison
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreRootLoweringComparison
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightThreeImages
open CFSGFFourOriginalHeightThreeLowering CFSGFFourOriginalHeightThreeRaising
local notation "A" => CartanMatrix.F₄

theorem path_twelve (neg:Bool) :
    (rootVectors neg 12).val=⁅rootVector A neg 0,(rootVectors neg 8).val⁆ := by
  change dividedPower A neg 0 1 (rootVectors neg 8).val=_
  simp [dividedPower]

private theorem weight_nine (neg:Bool) :
    ⁅coroot A neg 1,(rootVectors neg 9).val⁆=(-1:ℚ) • (rootVectors neg 9).val := by
  have hc:simpleWeight (1:Fin 4) (9:Fin 24)= -1:=by decide +kernel
  simpa only [hc,Int.cast_neg,Int.cast_one] using rootVectors_weight neg 1 9

theorem opposite_one_twelve (neg:Bool) :
    ⁅oppositeVector A neg 1,(rootVectors neg 12).val⁆=(rootVectors neg 9).val := by
  have h5:=raising_five neg 0
  change ⁅rootVector A neg 0,(rootVectors neg 5).val⁆= -(rootVectors neg 9).val at h5
  rw [path_twelve,leibniz_lie,opposite_distinct A neg 1 0 (by decide),
    zero_lie,zero_add,lower_eight,lie_neg,h5,neg_neg]

theorem raising_one_nine (neg:Bool) :
    ⁅rootVector A neg 1,(rootVectors neg 9).val⁆=(rootVectors neg 12).val := by
  have he:⁅coroot A neg 1,rootVector A neg 1⁆=(2:ℚ) • rootVector A neg 1:=
    coroot_root A neg 1 1
  have hv:⁅coroot A neg 1,⁅rootVector A neg 1,(rootVectors neg 9).val⁆⁆=
      (1:ℚ) • ⁅rootVector A neg 1,(rootVectors neg 9).val⁆ := by
    rw [leibniz_lie,he,weight_nine,smul_lie,lie_smul]
    module
  have hw:⁅coroot A neg 1,(rootVectors neg 12).val⁆=
      (1:ℚ) • (rootVectors neg 12).val := by
    have hc:simpleWeight (1:Fin 4) (12:Fin 24)=1:=by decide +kernel
    simpa only [hc,Int.cast_one] using rootVectors_weight neg 1 12
  have h9:=opposite_nine neg 1
  change ⁅oppositeVector A neg 1,(rootVectors neg 9).val⁆=0 at h9
  have hl:=opposite_raising A neg 1 1 (rootVectors neg 9).val (-1) (weight_nine neg)
  rw [if_pos rfl,h9,lie_zero,add_zero,neg_one_smul,neg_neg] at hl
  exact eq_of_positive_weight_of_opposite_eq A neg 1 (by decide) _ _ 1 (by norm_num)
    hv hw (hl.trans (opposite_one_twelve neg).symm)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalFirstLoweringComparison
