import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFirstLoweringComparison
import SymmetricSubgroupAsymptotics.CFSGRationalLieDoubleDerivation
import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation

/-! All simple raises on the three original height-three paths, with
integer coefficients in the displayed height-four paths. The one
non-defining path equality is supplied by positive-weight lowering
comparison; the non-root diamond vanishes by double derivation in the
original rational source. No matrix identity is pulled back. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFourRaising
open CFSG.Models.Chevalley CFSGSerreCrossNodeCommutation CFSGRationalLieDoubleDerivation
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightTwoSpan
open CFSGFFourOriginalHeightThreeImages CFSGFFourOriginalHeightThreeRaising
open CFSGFFourOriginalMiddleSerreStrings CFSGFFourOriginalFirstLoweringComparison
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

theorem path_ten (neg:Bool) :
    (rootVectors neg 10).val=⁅rootVector A neg 3,(rootVectors neg 8).val⁆ := by
  change dividedPower A neg 3 1 (rootVectors neg 8).val=_
  simp [dividedPower]

theorem path_eleven (neg:Bool) :
    (rootVectors neg 11).val=⁅rootVector A neg 3,(rootVectors neg 9).val⁆ := by
  change dividedPower A neg 3 1 (rootVectors neg 9).val=_
  simp [dividedPower]

private theorem twice_two_one (neg:Bool) :
    ⁅rootVector A neg 2,⁅rootVector A neg 2,rootVector A neg 1⁆⁆=0 := by
  have h:=raising_five neg 2
  change ⁅rootVector A neg 2,(rootVectors neg 5).val⁆=0 at h
  rw [path_five] at h
  exact h

private theorem twice_two_three (neg:Bool) :
    ⁅rootVector A neg 2,⁅rootVector A neg 2,rootVector A neg 3⁆⁆=0 := by
  have h:=raising_four neg 2
  change ⁅rootVector A neg 2,(rootVectors neg 4).val⁆=0 at h
  rw [path_four,←lie_skew (rootVector A neg 3) (rootVector A neg 2),lie_neg] at h
  exact neg_eq_zero.mp h

private theorem twice_three_two (neg:Bool) :
    ⁅rootVector A neg 3,⁅rootVector A neg 3,rootVector A neg 2⁆⁆=0 := by
  have h:=raising_four neg 3
  change ⁅rootVector A neg 3,(rootVectors neg 4).val⁆=0 at h
  rw [path_four] at h
  exact h

theorem raising_seven (neg:Bool) (i:Fin 4) :
    ⁅rootVector A neg i,(rootVectors neg 7).val⁆=
      (![-(rootVectors neg 11).val,(-2:ℚ) • (rootVectors neg 10).val,0,0]:Fin 4→L) i := by
  have h03:=rootVector_lie_zero_of_cartan_zero A neg 0 3 (by decide)
  have h13:=rootVector_lie_zero_of_cartan_zero A neg 1 3 (by decide)
  have h31:=rootVector_lie_zero_of_cartan_zero A neg 3 1 (by decide)
  fin_cases i
  · change ⁅rootVector A neg 0,(rootVectors neg 7).val⁆= -(rootVectors neg 11).val
    have h5:⁅rootVector A neg 0,(rootVectors neg 5).val⁆= -(rootVectors neg 9).val:=
      raising_five neg 0
    rw [path_seven,leibniz_lie,h03,zero_lie,zero_add,h5,lie_neg,←path_eleven]
  · change ⁅rootVector A neg 1,(rootVectors neg 7).val⁆=(-2:ℚ) • (rootVectors neg 10).val
    have h5:⁅rootVector A neg 1,(rootVectors neg 5).val⁆=(-2:ℚ) • (rootVectors neg 8).val:=
      raising_five neg 1
    rw [path_seven,leibniz_lie,h13,zero_lie,zero_add,h5,lie_smul,←path_ten]
  · change ⁅rootVector A neg 2,(rootVectors neg 7).val⁆=0
    rw [path_seven,path_five,leibniz_lie,twice_two_one,lie_zero,add_zero]
    exact raised_commute_of_two_strings (rootVector A neg 2) (rootVector A neg 3)
      (rootVector A neg 1) h31 (twice_two_three neg) (twice_two_one neg)
  · change ⁅rootVector A neg 3,(rootVectors neg 7).val⁆=0
    rw [path_seven,path_five]
    have h:=lie_twice_bracket (rootVector A neg 3) (rootVector A neg 2) (rootVector A neg 1)
    simpa only [twice_three_two,h31,zero_lie,lie_zero,smul_zero,add_zero,zero_add] using h

theorem raising_eight (neg:Bool) (i:Fin 4) :
    ⁅rootVector A neg i,(rootVectors neg 8).val⁆=
      (![(rootVectors neg 12).val,0,0,(rootVectors neg 10).val]:Fin 4→L) i := by
  fin_cases i
  · change ⁅rootVector A neg 0,(rootVectors neg 8).val⁆=(rootVectors neg 12).val
    exact (path_twelve neg).symm
  · change ⁅shortVector neg,stringVector neg 2⁆=0
    exact short_string_two neg
  · change ⁅longVector neg,stringVector neg 2⁆=0
    exact long_string_two neg
  · change ⁅rootVector A neg 3,(rootVectors neg 8).val⁆=(rootVectors neg 10).val
    exact (path_ten neg).symm

theorem raising_nine (neg:Bool) (i:Fin 4) :
    ⁅rootVector A neg i,(rootVectors neg 9).val⁆=
      (![0,(rootVectors neg 12).val,0,(rootVectors neg 11).val]:Fin 4→L) i := by
  have h02:=rootVector_lie_zero_of_cartan_zero A neg 0 2 (by decide)
  have h20:=rootVector_lie_zero_of_cartan_zero A neg 2 0 (by decide)
  fin_cases i
  · change ⁅rootVector A neg 0,(rootVectors neg 9).val⁆=0
    have h6:⁅rootVector A neg 0,(rootVectors neg 6).val⁆=0:=raising_six neg 0
    rw [path_nine,leibniz_lie,h02,h6,zero_lie,lie_zero,add_zero]
  · change ⁅rootVector A neg 1,(rootVectors neg 9).val⁆=(rootVectors neg 12).val
    exact raising_one_nine neg
  · change ⁅rootVector A neg 2,(rootVectors neg 9).val⁆=0
    rw [path_nine,path_six]
    have h:=lie_twice_bracket (rootVector A neg 2) (rootVector A neg 1) (rootVector A neg 0)
    simpa only [twice_two_one,h20,zero_lie,lie_zero,smul_zero,add_zero,zero_add] using h
  · change ⁅rootVector A neg 3,(rootVectors neg 9).val⁆=(rootVectors neg 11).val
    exact (path_eleven neg).symm

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFourRaising
