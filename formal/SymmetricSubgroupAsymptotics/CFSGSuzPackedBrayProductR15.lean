import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR14
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR
import SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareKroneckerCaches

/-! ONE edge of the fixed positive Suz DAG;64 selected row checks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR15
open MatrixKroneckerProductReflection

private theorem check_row_00 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 0*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 0 j%3 := by
  decide +kernel

private theorem check_row_01 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 1*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 1 j%3 := by
  decide +kernel

private theorem check_row_02 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 2*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 2 j%3 := by
  decide +kernel

private theorem check_row_03 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 3*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 3 j%3 := by
  decide +kernel

private theorem check_row_04 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 4*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 4 j%3 := by
  decide +kernel

private theorem check_row_05 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 5*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 5 j%3 := by
  decide +kernel

private theorem check_row_06 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 6*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 6 j%3 := by
  decide +kernel

private theorem check_row_07 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 7*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 7 j%3 := by
  decide +kernel

private theorem check_row_08 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 8*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 8 j%3 := by
  decide +kernel

private theorem check_row_09 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 9*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 9 j%3 := by
  decide +kernel

private theorem check_row_10 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 10*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 10 j%3 := by
  decide +kernel

private theorem check_row_11 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 11*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 11 j%3 := by
  decide +kernel

private theorem check_row_12 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 12*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 12 j%3 := by
  decide +kernel

private theorem check_row_13 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 13*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 13 j%3 := by
  decide +kernel

private theorem check_row_14 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 14*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 14 j%3 := by
  decide +kernel

private theorem check_row_15 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 15*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 15 j%3 := by
  decide +kernel

private theorem check_row_16 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 16*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 16 j%3 := by
  decide +kernel

private theorem check_row_17 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 17*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 17 j%3 := by
  decide +kernel

private theorem check_row_18 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 18*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 18 j%3 := by
  decide +kernel

private theorem check_row_19 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 19*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 19 j%3 := by
  decide +kernel

private theorem check_row_20 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 20*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 20 j%3 := by
  decide +kernel

private theorem check_row_21 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 21*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 21 j%3 := by
  decide +kernel

private theorem check_row_22 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 22*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 22 j%3 := by
  decide +kernel

private theorem check_row_23 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 23*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 23 j%3 := by
  decide +kernel

private theorem check_row_24 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 24*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 24 j%3 := by
  decide +kernel

private theorem check_row_25 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 25*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 25 j%3 := by
  decide +kernel

private theorem check_row_26 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 26*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 26 j%3 := by
  decide +kernel

private theorem check_row_27 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 27*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 27 j%3 := by
  decide +kernel

private theorem check_row_28 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 28*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 28 j%3 := by
  decide +kernel

private theorem check_row_29 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 29*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 29 j%3 := by
  decide +kernel

private theorem check_row_30 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 30*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 30 j%3 := by
  decide +kernel

private theorem check_row_31 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 31*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 31 j%3 := by
  decide +kernel

private theorem check_row_32 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 32*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 32 j%3 := by
  decide +kernel

private theorem check_row_33 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 33*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 33 j%3 := by
  decide +kernel

private theorem check_row_34 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 34*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 34 j%3 := by
  decide +kernel

private theorem check_row_35 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 35*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 35 j%3 := by
  decide +kernel

private theorem check_row_36 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 36*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 36 j%3 := by
  decide +kernel

private theorem check_row_37 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 37*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 37 j%3 := by
  decide +kernel

private theorem check_row_38 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 38*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 38 j%3 := by
  decide +kernel

private theorem check_row_39 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 39*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 39 j%3 := by
  decide +kernel

private theorem check_row_40 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 40*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 40 j%3 := by
  decide +kernel

private theorem check_row_41 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 41*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 41 j%3 := by
  decide +kernel

private theorem check_row_42 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 42*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 42 j%3 := by
  decide +kernel

private theorem check_row_43 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 43*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 43 j%3 := by
  decide +kernel

private theorem check_row_44 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 44*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 44 j%3 := by
  decide +kernel

private theorem check_row_45 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 45*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 45 j%3 := by
  decide +kernel

private theorem check_row_46 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 46*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 46 j%3 := by
  decide +kernel

private theorem check_row_47 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 47*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 47 j%3 := by
  decide +kernel

private theorem check_row_48 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 48*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 48 j%3 := by
  decide +kernel

private theorem check_row_49 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 49*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 49 j%3 := by
  decide +kernel

private theorem check_row_50 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 50*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 50 j%3 := by
  decide +kernel

private theorem check_row_51 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 51*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 51 j%3 := by
  decide +kernel

private theorem check_row_52 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 52*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 52 j%3 := by
  decide +kernel

private theorem check_row_53 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 53*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 53 j%3 := by
  decide +kernel

private theorem check_row_54 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 54*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 54 j%3 := by
  decide +kernel

private theorem check_row_55 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 55*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 55 j%3 := by
  decide +kernel

private theorem check_row_56 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 56*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 56 j%3 := by
  decide +kernel

private theorem check_row_57 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 57*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 57 j%3 := by
  decide +kernel

private theorem check_row_58 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 58*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 58 j%3 := by
  decide +kernel

private theorem check_row_59 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 59*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 59 j%3 := by
  decide +kernel

private theorem check_row_60 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 60*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 60 j%3 := by
  decide +kernel

private theorem check_row_61 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 61*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 61 j%3 := by
  decide +kernel

private theorem check_row_62 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 62*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 62 j%3 := by
  decide +kernel

private theorem check_row_63 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode 63*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit 63 j%3 := by
  decide +kernel

theorem packed_checks : ∀ i j : Fin 64,
    (((CFSGSuzPackedBrayCacheR14.rowCode i*CFSGSuzPackedBrayCacheR.columnCode j)/512^63)%512)%3=CFSGSuzFirstSquareKroneckerCaches.iDigit i j%3 := by
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

def matrix : Matrix (Fin 64) (Fin 64) (ZMod 3) :=
  (CFSGSuzPackedBrayProductR14.matrix)*(CFSGSuzPackedBrayProductR.matrix)

theorem cache : matrix=CFSGSuzFirstSquareKroneckerCaches.iData.matrix 3 := by
  exact product_eq_of_data (by decide : 0<64) _ _
    CFSGSuzPackedBrayCacheR14.data CFSGSuzPackedBrayCacheR.data CFSGSuzFirstSquareKroneckerCaches.iData
    CFSGSuzPackedBrayProductR14.cache CFSGSuzPackedBrayProductR.cache
    (by decide : 64*(3-1)^2<512) packed_checks

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR15
