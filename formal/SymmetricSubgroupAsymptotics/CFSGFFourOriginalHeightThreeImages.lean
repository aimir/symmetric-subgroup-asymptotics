import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightTwoImage
import SymmetricSubgroupAsymptotics.CFSGSerreImageNegativeWeightRaising
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleLowering

/-! Nonvanishing of the next three SAME original source images.
Single raising steps use negative Cartan weight. The double middle
step uses its already proved original lowering with coefficient one.
These are local rational-image statements, not an integral basis or
faithfulness theorem for the complete source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeImages
open CFSG.Models.Chevalley CFSGFFourSerreMatrices CFSGNormTwoRootPairing
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightTwoSpan
open CFSGFFourOriginalHeightTwoImage CFSGSerreSignedRootWeights
open CFSGFFourOriginalMiddleSerreStrings CFSGFFourOriginalMiddleLowering
open CFSGSerreImageNegativeWeightRaising
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.F₄

theorem path_seven (neg:Bool) :
    (rootVectors neg 7).val=⁅rootVector A neg 3,(rootVectors neg 5).val⁆ := by
  change dividedPower A neg 3 1 (dividedPower A neg 2 1 (rootVector A neg 1))=_
  simp only [dividedPower,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,pow_one,
    LinearMap.restrictScalars_apply,LieAlgebra.ad_apply]
  rw [path_five]

theorem path_nine (neg:Bool) :
    (rootVectors neg 9).val=⁅rootVector A neg 2,(rootVectors neg 6).val⁆ := by
  change dividedPower A neg 2 1 (dividedPower A neg 1 1 (rootVector A neg 0))=_
  simp only [dividedPower,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,pow_one,
    LinearMap.restrictScalars_apply,LieAlgebra.ad_apply]
  rw [path_six]

theorem lower_eight (neg:Bool) :
    ⁅oppositeVector A neg 1,(rootVectors neg 8).val⁆= -(rootVectors neg 5).val := by
  change ⁅oppositeVector A neg 1,stringVector neg 2⁆= -(rootVectors neg 5).val
  rw [opposite_short_string_two,string_one,path_five]
  exact (lie_skew (rootVector A neg 1) (rootVector A neg 2)).symm

theorem image_seven_ne_zero : rationalRepresentation ((rootVectors false 7).val)≠0 := by
  have hv:rationalRepresentation ((rootVectors false 5).val)≠0:=initial_image_ne_zero 5
  have hc:simpleWeight (3:Fin 4) (5:Fin 24)= -1:=by decide +kernel
  have hw:⁅coroot A false 3,(rootVectors false 5).val⁆=
      (-1:ℚ) • (rootVectors false 5).val := by
    simpa only [hc,Int.cast_neg,Int.cast_one] using rootVectors_weight false 3 5
  rw [path_seven]
  exact image_bracket_ne_zero_of_negative_weight A rationalRepresentation false 3
    (by decide) _ (-1) (by norm_num) hw hv

theorem image_eight_ne_zero : rationalRepresentation ((rootVectors false 8).val)≠0 := by
  intro hz
  have h:=congrArg rationalRepresentation (lower_eight false)
  rw [LieHom.map_lie,hz,lie_zero,map_neg] at h
  have hv:rationalRepresentation ((rootVectors false 5).val)≠0:=initial_image_ne_zero 5
  exact hv (neg_eq_zero.mp h.symm)

theorem image_nine_ne_zero : rationalRepresentation ((rootVectors false 9).val)≠0 := by
  have hv:rationalRepresentation ((rootVectors false 6).val)≠0:=initial_image_ne_zero 6
  have hc:simpleWeight (2:Fin 4) (6:Fin 24)= -1:=by decide +kernel
  have hw:⁅coroot A false 2,(rootVectors false 6).val⁆=
      (-1:ℚ) • (rootVectors false 6).val := by
    simpa only [hc,Int.cast_neg,Int.cast_one] using rootVectors_weight false 2 6
  rw [path_nine]
  exact image_bracket_ne_zero_of_negative_weight A rationalRepresentation false 2
    (by decide) _ (-1) (by norm_num) hw hv

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeImages
