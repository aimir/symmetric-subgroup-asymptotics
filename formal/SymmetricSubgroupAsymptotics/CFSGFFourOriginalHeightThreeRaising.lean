import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeImages
import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation

/-! The twelve simple raising operations on the three original
height-two vectors. Their images are integral combinations of the
three selected height-three paths. These are source Serre/Jacobi
identities and do not follow from matrix-image faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeRaising
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreCrossNodeCommutation
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightTwoSpan
open CFSGFFourOriginalHeightThreeImages CFSGFFourOriginalMiddleSerreStrings
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

private theorem serre_two (neg:Bool) (i j:Fin 4) (ha:A i j= -1) :
    ⁅rootVector A neg i,⁅rootVector A neg i,rootVector A neg j⁆⁆=0 := by
  cases neg
  · have h:=generator_adE A i j
    rw [ha] at h
    change (LieAlgebra.ad ℚ L (generator A (.E i))^2) (generator A (.E j))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,
      Module.End.one_apply,rootVector,Bool.false_eq_true,if_false] using h
  · have h:=generator_adF A i j
    rw [ha] at h
    change (LieAlgebra.ad ℚ L (generator A (.F i))^2) (generator A (.F j))=0 at h
    simpa only [pow_succ',Module.End.mul_apply,LieAlgebra.ad_apply,pow_zero,
      Module.End.one_apply,rootVector,if_true] using h

theorem raising_four (neg:Bool) (i:Fin 4) :
    ⁅rootVector A neg i,(rootVectors neg 4).val⁆=
      (![0,-(rootVectors neg 7).val,0,0]:Fin 4→L) i := by
  have h03:=rootVector_lie_zero_of_cartan_zero A neg 0 3 (by decide)
  have h02:=rootVector_lie_zero_of_cartan_zero A neg 0 2 (by decide)
  have h13:=rootVector_lie_zero_of_cartan_zero A neg 1 3 (by decide)
  fin_cases i
  · change ⁅rootVector A neg 0,(rootVectors neg 4).val⁆=0
    rw [path_four,leibniz_lie,h03,h02,zero_lie,lie_zero,add_zero]
  · change ⁅rootVector A neg 1,(rootVectors neg 4).val⁆= -(rootVectors neg 7).val
    rw [path_four,leibniz_lie,h13,zero_lie,zero_add,
      ←lie_skew (rootVector A neg 1) (rootVector A neg 2),lie_neg,
      ←path_five,←path_seven]
  · change ⁅rootVector A neg 2,(rootVectors neg 4).val⁆=0
    rw [path_four,←lie_skew (rootVector A neg 3) (rootVector A neg 2),lie_neg,
      serre_two neg 2 3 (by decide),neg_zero]
  · change ⁅rootVector A neg 3,(rootVectors neg 4).val⁆=0
    rw [path_four,serre_two neg 3 2 (by decide)]

theorem raising_five (neg:Bool) (i:Fin 4) :
    ⁅rootVector A neg i,(rootVectors neg 5).val⁆=
      (![-(rootVectors neg 9).val,(-2:ℚ) • (rootVectors neg 8).val,
        0,(rootVectors neg 7).val]:Fin 4→L) i := by
  have h02:=rootVector_lie_zero_of_cartan_zero A neg 0 2 (by decide)
  fin_cases i
  · change ⁅rootVector A neg 0,(rootVectors neg 5).val⁆= -(rootVectors neg 9).val
    rw [path_five,leibniz_lie,h02,zero_lie,zero_add,
      ←lie_skew (rootVector A neg 0) (rootVector A neg 1),lie_neg,
      ←path_six,←path_nine]
  · change ⁅rootVector A neg 1,(rootVectors neg 5).val⁆=
      (-2:ℚ) • (rootVectors neg 8).val
    rw [path_five,←lie_skew (rootVector A neg 2) (rootVector A neg 1),lie_neg]
    have h:=short_string_one neg
    rw [string_one] at h
    change ⁅rootVector A neg 1,⁅rootVector A neg 1,rootVector A neg 2⁆⁆=
      (2:ℚ) • (rootVectors neg 8).val at h
    rw [h]
    module
  · change ⁅rootVector A neg 2,(rootVectors neg 5).val⁆=0
    rw [path_five,serre_two neg 2 1 (by decide)]
  · change ⁅rootVector A neg 3,(rootVectors neg 5).val⁆=(rootVectors neg 7).val
    exact (path_seven neg).symm

theorem raising_six (neg:Bool) (i:Fin 4) :
    ⁅rootVector A neg i,(rootVectors neg 6).val⁆=
      (![0,0,(rootVectors neg 9).val,0]:Fin 4→L) i := by
  have h31:=rootVector_lie_zero_of_cartan_zero A neg 3 1 (by decide)
  have h30:=rootVector_lie_zero_of_cartan_zero A neg 3 0 (by decide)
  fin_cases i
  · change ⁅rootVector A neg 0,(rootVectors neg 6).val⁆=0
    rw [path_six,←lie_skew (rootVector A neg 1) (rootVector A neg 0),lie_neg,
      serre_two neg 0 1 (by decide),neg_zero]
  · change ⁅rootVector A neg 1,(rootVectors neg 6).val⁆=0
    rw [path_six,serre_two neg 1 0 (by decide)]
  · change ⁅rootVector A neg 2,(rootVectors neg 6).val⁆=(rootVectors neg 9).val
    exact (path_nine neg).symm
  · change ⁅rootVector A neg 3,(rootVectors neg 6).val⁆=0
    rw [path_six,leibniz_lie,h31,h30,zero_lie,lie_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeRaising
