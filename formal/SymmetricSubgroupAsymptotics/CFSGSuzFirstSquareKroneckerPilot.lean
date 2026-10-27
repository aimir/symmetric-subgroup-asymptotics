import SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareKroneckerCaches

/-! ONE whole product: the actual first Suz matrix squared.
Each selected row checks64 scalar packed multiplications. No other power is emitted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareKroneckerPilot
open MatrixKroneckerProductReflection
open CFSGSuzFirstSquareKroneckerCaches
open CFSG.Models.MatrixGroups.Suz

private theorem check_row_00 : ∀ j : Fin 64,
    (((aRowCode 0*aColumnCode j)/512^63)%512)%3=iDigit 0 j%3 := by
  decide +kernel

private theorem check_row_01 : ∀ j : Fin 64,
    (((aRowCode 1*aColumnCode j)/512^63)%512)%3=iDigit 1 j%3 := by
  decide +kernel

private theorem check_row_02 : ∀ j : Fin 64,
    (((aRowCode 2*aColumnCode j)/512^63)%512)%3=iDigit 2 j%3 := by
  decide +kernel

private theorem check_row_03 : ∀ j : Fin 64,
    (((aRowCode 3*aColumnCode j)/512^63)%512)%3=iDigit 3 j%3 := by
  decide +kernel

private theorem check_row_04 : ∀ j : Fin 64,
    (((aRowCode 4*aColumnCode j)/512^63)%512)%3=iDigit 4 j%3 := by
  decide +kernel

private theorem check_row_05 : ∀ j : Fin 64,
    (((aRowCode 5*aColumnCode j)/512^63)%512)%3=iDigit 5 j%3 := by
  decide +kernel

private theorem check_row_06 : ∀ j : Fin 64,
    (((aRowCode 6*aColumnCode j)/512^63)%512)%3=iDigit 6 j%3 := by
  decide +kernel

private theorem check_row_07 : ∀ j : Fin 64,
    (((aRowCode 7*aColumnCode j)/512^63)%512)%3=iDigit 7 j%3 := by
  decide +kernel

private theorem check_row_08 : ∀ j : Fin 64,
    (((aRowCode 8*aColumnCode j)/512^63)%512)%3=iDigit 8 j%3 := by
  decide +kernel

private theorem check_row_09 : ∀ j : Fin 64,
    (((aRowCode 9*aColumnCode j)/512^63)%512)%3=iDigit 9 j%3 := by
  decide +kernel

private theorem check_row_10 : ∀ j : Fin 64,
    (((aRowCode 10*aColumnCode j)/512^63)%512)%3=iDigit 10 j%3 := by
  decide +kernel

private theorem check_row_11 : ∀ j : Fin 64,
    (((aRowCode 11*aColumnCode j)/512^63)%512)%3=iDigit 11 j%3 := by
  decide +kernel

private theorem check_row_12 : ∀ j : Fin 64,
    (((aRowCode 12*aColumnCode j)/512^63)%512)%3=iDigit 12 j%3 := by
  decide +kernel

private theorem check_row_13 : ∀ j : Fin 64,
    (((aRowCode 13*aColumnCode j)/512^63)%512)%3=iDigit 13 j%3 := by
  decide +kernel

private theorem check_row_14 : ∀ j : Fin 64,
    (((aRowCode 14*aColumnCode j)/512^63)%512)%3=iDigit 14 j%3 := by
  decide +kernel

private theorem check_row_15 : ∀ j : Fin 64,
    (((aRowCode 15*aColumnCode j)/512^63)%512)%3=iDigit 15 j%3 := by
  decide +kernel

private theorem check_row_16 : ∀ j : Fin 64,
    (((aRowCode 16*aColumnCode j)/512^63)%512)%3=iDigit 16 j%3 := by
  decide +kernel

private theorem check_row_17 : ∀ j : Fin 64,
    (((aRowCode 17*aColumnCode j)/512^63)%512)%3=iDigit 17 j%3 := by
  decide +kernel

private theorem check_row_18 : ∀ j : Fin 64,
    (((aRowCode 18*aColumnCode j)/512^63)%512)%3=iDigit 18 j%3 := by
  decide +kernel

private theorem check_row_19 : ∀ j : Fin 64,
    (((aRowCode 19*aColumnCode j)/512^63)%512)%3=iDigit 19 j%3 := by
  decide +kernel

private theorem check_row_20 : ∀ j : Fin 64,
    (((aRowCode 20*aColumnCode j)/512^63)%512)%3=iDigit 20 j%3 := by
  decide +kernel

private theorem check_row_21 : ∀ j : Fin 64,
    (((aRowCode 21*aColumnCode j)/512^63)%512)%3=iDigit 21 j%3 := by
  decide +kernel

private theorem check_row_22 : ∀ j : Fin 64,
    (((aRowCode 22*aColumnCode j)/512^63)%512)%3=iDigit 22 j%3 := by
  decide +kernel

private theorem check_row_23 : ∀ j : Fin 64,
    (((aRowCode 23*aColumnCode j)/512^63)%512)%3=iDigit 23 j%3 := by
  decide +kernel

private theorem check_row_24 : ∀ j : Fin 64,
    (((aRowCode 24*aColumnCode j)/512^63)%512)%3=iDigit 24 j%3 := by
  decide +kernel

private theorem check_row_25 : ∀ j : Fin 64,
    (((aRowCode 25*aColumnCode j)/512^63)%512)%3=iDigit 25 j%3 := by
  decide +kernel

private theorem check_row_26 : ∀ j : Fin 64,
    (((aRowCode 26*aColumnCode j)/512^63)%512)%3=iDigit 26 j%3 := by
  decide +kernel

private theorem check_row_27 : ∀ j : Fin 64,
    (((aRowCode 27*aColumnCode j)/512^63)%512)%3=iDigit 27 j%3 := by
  decide +kernel

private theorem check_row_28 : ∀ j : Fin 64,
    (((aRowCode 28*aColumnCode j)/512^63)%512)%3=iDigit 28 j%3 := by
  decide +kernel

private theorem check_row_29 : ∀ j : Fin 64,
    (((aRowCode 29*aColumnCode j)/512^63)%512)%3=iDigit 29 j%3 := by
  decide +kernel

private theorem check_row_30 : ∀ j : Fin 64,
    (((aRowCode 30*aColumnCode j)/512^63)%512)%3=iDigit 30 j%3 := by
  decide +kernel

private theorem check_row_31 : ∀ j : Fin 64,
    (((aRowCode 31*aColumnCode j)/512^63)%512)%3=iDigit 31 j%3 := by
  decide +kernel

private theorem check_row_32 : ∀ j : Fin 64,
    (((aRowCode 32*aColumnCode j)/512^63)%512)%3=iDigit 32 j%3 := by
  decide +kernel

private theorem check_row_33 : ∀ j : Fin 64,
    (((aRowCode 33*aColumnCode j)/512^63)%512)%3=iDigit 33 j%3 := by
  decide +kernel

private theorem check_row_34 : ∀ j : Fin 64,
    (((aRowCode 34*aColumnCode j)/512^63)%512)%3=iDigit 34 j%3 := by
  decide +kernel

private theorem check_row_35 : ∀ j : Fin 64,
    (((aRowCode 35*aColumnCode j)/512^63)%512)%3=iDigit 35 j%3 := by
  decide +kernel

private theorem check_row_36 : ∀ j : Fin 64,
    (((aRowCode 36*aColumnCode j)/512^63)%512)%3=iDigit 36 j%3 := by
  decide +kernel

private theorem check_row_37 : ∀ j : Fin 64,
    (((aRowCode 37*aColumnCode j)/512^63)%512)%3=iDigit 37 j%3 := by
  decide +kernel

private theorem check_row_38 : ∀ j : Fin 64,
    (((aRowCode 38*aColumnCode j)/512^63)%512)%3=iDigit 38 j%3 := by
  decide +kernel

private theorem check_row_39 : ∀ j : Fin 64,
    (((aRowCode 39*aColumnCode j)/512^63)%512)%3=iDigit 39 j%3 := by
  decide +kernel

private theorem check_row_40 : ∀ j : Fin 64,
    (((aRowCode 40*aColumnCode j)/512^63)%512)%3=iDigit 40 j%3 := by
  decide +kernel

private theorem check_row_41 : ∀ j : Fin 64,
    (((aRowCode 41*aColumnCode j)/512^63)%512)%3=iDigit 41 j%3 := by
  decide +kernel

private theorem check_row_42 : ∀ j : Fin 64,
    (((aRowCode 42*aColumnCode j)/512^63)%512)%3=iDigit 42 j%3 := by
  decide +kernel

private theorem check_row_43 : ∀ j : Fin 64,
    (((aRowCode 43*aColumnCode j)/512^63)%512)%3=iDigit 43 j%3 := by
  decide +kernel

private theorem check_row_44 : ∀ j : Fin 64,
    (((aRowCode 44*aColumnCode j)/512^63)%512)%3=iDigit 44 j%3 := by
  decide +kernel

private theorem check_row_45 : ∀ j : Fin 64,
    (((aRowCode 45*aColumnCode j)/512^63)%512)%3=iDigit 45 j%3 := by
  decide +kernel

private theorem check_row_46 : ∀ j : Fin 64,
    (((aRowCode 46*aColumnCode j)/512^63)%512)%3=iDigit 46 j%3 := by
  decide +kernel

private theorem check_row_47 : ∀ j : Fin 64,
    (((aRowCode 47*aColumnCode j)/512^63)%512)%3=iDigit 47 j%3 := by
  decide +kernel

private theorem check_row_48 : ∀ j : Fin 64,
    (((aRowCode 48*aColumnCode j)/512^63)%512)%3=iDigit 48 j%3 := by
  decide +kernel

private theorem check_row_49 : ∀ j : Fin 64,
    (((aRowCode 49*aColumnCode j)/512^63)%512)%3=iDigit 49 j%3 := by
  decide +kernel

private theorem check_row_50 : ∀ j : Fin 64,
    (((aRowCode 50*aColumnCode j)/512^63)%512)%3=iDigit 50 j%3 := by
  decide +kernel

private theorem check_row_51 : ∀ j : Fin 64,
    (((aRowCode 51*aColumnCode j)/512^63)%512)%3=iDigit 51 j%3 := by
  decide +kernel

private theorem check_row_52 : ∀ j : Fin 64,
    (((aRowCode 52*aColumnCode j)/512^63)%512)%3=iDigit 52 j%3 := by
  decide +kernel

private theorem check_row_53 : ∀ j : Fin 64,
    (((aRowCode 53*aColumnCode j)/512^63)%512)%3=iDigit 53 j%3 := by
  decide +kernel

private theorem check_row_54 : ∀ j : Fin 64,
    (((aRowCode 54*aColumnCode j)/512^63)%512)%3=iDigit 54 j%3 := by
  decide +kernel

private theorem check_row_55 : ∀ j : Fin 64,
    (((aRowCode 55*aColumnCode j)/512^63)%512)%3=iDigit 55 j%3 := by
  decide +kernel

private theorem check_row_56 : ∀ j : Fin 64,
    (((aRowCode 56*aColumnCode j)/512^63)%512)%3=iDigit 56 j%3 := by
  decide +kernel

private theorem check_row_57 : ∀ j : Fin 64,
    (((aRowCode 57*aColumnCode j)/512^63)%512)%3=iDigit 57 j%3 := by
  decide +kernel

private theorem check_row_58 : ∀ j : Fin 64,
    (((aRowCode 58*aColumnCode j)/512^63)%512)%3=iDigit 58 j%3 := by
  decide +kernel

private theorem check_row_59 : ∀ j : Fin 64,
    (((aRowCode 59*aColumnCode j)/512^63)%512)%3=iDigit 59 j%3 := by
  decide +kernel

private theorem check_row_60 : ∀ j : Fin 64,
    (((aRowCode 60*aColumnCode j)/512^63)%512)%3=iDigit 60 j%3 := by
  decide +kernel

private theorem check_row_61 : ∀ j : Fin 64,
    (((aRowCode 61*aColumnCode j)/512^63)%512)%3=iDigit 61 j%3 := by
  decide +kernel

private theorem check_row_62 : ∀ j : Fin 64,
    (((aRowCode 62*aColumnCode j)/512^63)%512)%3=iDigit 62 j%3 := by
  decide +kernel

private theorem check_row_63 : ∀ j : Fin 64,
    (((aRowCode 63*aColumnCode j)/512^63)%512)%3=iDigit 63 j%3 := by
  decide +kernel

theorem packed_product_checks : ∀ i j : Fin 64,
    (((aRowCode i*aColumnCode j)/512^63)%512)%3=iDigit i j%3 := by
  intro i j
  fin_cases i
  · exact check_row_00 j
  · exact check_row_01 j
  · exact check_row_02 j
  · exact check_row_03 j
  · exact check_row_04 j
  · exact check_row_05 j
  · exact check_row_06 j
  · exact check_row_07 j
  · exact check_row_08 j
  · exact check_row_09 j
  · exact check_row_10 j
  · exact check_row_11 j
  · exact check_row_12 j
  · exact check_row_13 j
  · exact check_row_14 j
  · exact check_row_15 j
  · exact check_row_16 j
  · exact check_row_17 j
  · exact check_row_18 j
  · exact check_row_19 j
  · exact check_row_20 j
  · exact check_row_21 j
  · exact check_row_22 j
  · exact check_row_23 j
  · exact check_row_24 j
  · exact check_row_25 j
  · exact check_row_26 j
  · exact check_row_27 j
  · exact check_row_28 j
  · exact check_row_29 j
  · exact check_row_30 j
  · exact check_row_31 j
  · exact check_row_32 j
  · exact check_row_33 j
  · exact check_row_34 j
  · exact check_row_35 j
  · exact check_row_36 j
  · exact check_row_37 j
  · exact check_row_38 j
  · exact check_row_39 j
  · exact check_row_40 j
  · exact check_row_41 j
  · exact check_row_42 j
  · exact check_row_43 j
  · exact check_row_44 j
  · exact check_row_45 j
  · exact check_row_46 j
  · exact check_row_47 j
  · exact check_row_48 j
  · exact check_row_49 j
  · exact check_row_50 j
  · exact check_row_51 j
  · exact check_row_52 j
  · exact check_row_53 j
  · exact check_row_54 j
  · exact check_row_55 j
  · exact check_row_56 j
  · exact check_row_57 j
  · exact check_row_58 j
  · exact check_row_59 j
  · exact check_row_60 j
  · exact check_row_61 j
  · exact check_row_62 j
  · exact check_row_63 j

theorem whole_product :
    CFSG.Models.MatrixData.matrix 3 64 rows1*
      CFSG.Models.MatrixData.matrix 3 64 rows1=iData.matrix 3 := by
  exact product_eq_of_data (by decide : 0<64) _ _ aData aData iData
    literal_source_binding literal_source_binding
    (by decide : 64*(3-1)^2<512) packed_product_checks

theorem first_square : CFSG.Models.MatrixData.matrix 3 64 rows1^2=1 := by
  rw [pow_two]
  exact whole_product.trans identity_cache_binding

end SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareKroneckerPilot
