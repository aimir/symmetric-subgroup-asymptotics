import SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareKroneckerCaches
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductB2
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheAB2

/-! ONE edge of the fixed positive Suz DAG;64 selected row checks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductAB2
open MatrixKroneckerProductReflection

private theorem check_row_00 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 0*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 0 j%3 := by
  decide +kernel

private theorem check_row_01 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 1*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 1 j%3 := by
  decide +kernel

private theorem check_row_02 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 2*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 2 j%3 := by
  decide +kernel

private theorem check_row_03 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 3*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 3 j%3 := by
  decide +kernel

private theorem check_row_04 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 4*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 4 j%3 := by
  decide +kernel

private theorem check_row_05 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 5*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 5 j%3 := by
  decide +kernel

private theorem check_row_06 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 6*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 6 j%3 := by
  decide +kernel

private theorem check_row_07 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 7*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 7 j%3 := by
  decide +kernel

private theorem check_row_08 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 8*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 8 j%3 := by
  decide +kernel

private theorem check_row_09 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 9*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 9 j%3 := by
  decide +kernel

private theorem check_row_10 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 10*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 10 j%3 := by
  decide +kernel

private theorem check_row_11 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 11*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 11 j%3 := by
  decide +kernel

private theorem check_row_12 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 12*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 12 j%3 := by
  decide +kernel

private theorem check_row_13 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 13*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 13 j%3 := by
  decide +kernel

private theorem check_row_14 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 14*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 14 j%3 := by
  decide +kernel

private theorem check_row_15 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 15*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 15 j%3 := by
  decide +kernel

private theorem check_row_16 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 16*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 16 j%3 := by
  decide +kernel

private theorem check_row_17 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 17*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 17 j%3 := by
  decide +kernel

private theorem check_row_18 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 18*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 18 j%3 := by
  decide +kernel

private theorem check_row_19 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 19*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 19 j%3 := by
  decide +kernel

private theorem check_row_20 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 20*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 20 j%3 := by
  decide +kernel

private theorem check_row_21 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 21*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 21 j%3 := by
  decide +kernel

private theorem check_row_22 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 22*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 22 j%3 := by
  decide +kernel

private theorem check_row_23 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 23*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 23 j%3 := by
  decide +kernel

private theorem check_row_24 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 24*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 24 j%3 := by
  decide +kernel

private theorem check_row_25 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 25*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 25 j%3 := by
  decide +kernel

private theorem check_row_26 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 26*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 26 j%3 := by
  decide +kernel

private theorem check_row_27 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 27*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 27 j%3 := by
  decide +kernel

private theorem check_row_28 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 28*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 28 j%3 := by
  decide +kernel

private theorem check_row_29 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 29*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 29 j%3 := by
  decide +kernel

private theorem check_row_30 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 30*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 30 j%3 := by
  decide +kernel

private theorem check_row_31 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 31*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 31 j%3 := by
  decide +kernel

private theorem check_row_32 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 32*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 32 j%3 := by
  decide +kernel

private theorem check_row_33 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 33*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 33 j%3 := by
  decide +kernel

private theorem check_row_34 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 34*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 34 j%3 := by
  decide +kernel

private theorem check_row_35 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 35*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 35 j%3 := by
  decide +kernel

private theorem check_row_36 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 36*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 36 j%3 := by
  decide +kernel

private theorem check_row_37 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 37*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 37 j%3 := by
  decide +kernel

private theorem check_row_38 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 38*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 38 j%3 := by
  decide +kernel

private theorem check_row_39 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 39*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 39 j%3 := by
  decide +kernel

private theorem check_row_40 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 40*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 40 j%3 := by
  decide +kernel

private theorem check_row_41 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 41*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 41 j%3 := by
  decide +kernel

private theorem check_row_42 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 42*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 42 j%3 := by
  decide +kernel

private theorem check_row_43 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 43*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 43 j%3 := by
  decide +kernel

private theorem check_row_44 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 44*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 44 j%3 := by
  decide +kernel

private theorem check_row_45 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 45*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 45 j%3 := by
  decide +kernel

private theorem check_row_46 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 46*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 46 j%3 := by
  decide +kernel

private theorem check_row_47 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 47*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 47 j%3 := by
  decide +kernel

private theorem check_row_48 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 48*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 48 j%3 := by
  decide +kernel

private theorem check_row_49 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 49*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 49 j%3 := by
  decide +kernel

private theorem check_row_50 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 50*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 50 j%3 := by
  decide +kernel

private theorem check_row_51 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 51*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 51 j%3 := by
  decide +kernel

private theorem check_row_52 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 52*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 52 j%3 := by
  decide +kernel

private theorem check_row_53 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 53*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 53 j%3 := by
  decide +kernel

private theorem check_row_54 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 54*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 54 j%3 := by
  decide +kernel

private theorem check_row_55 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 55*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 55 j%3 := by
  decide +kernel

private theorem check_row_56 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 56*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 56 j%3 := by
  decide +kernel

private theorem check_row_57 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 57*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 57 j%3 := by
  decide +kernel

private theorem check_row_58 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 58*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 58 j%3 := by
  decide +kernel

private theorem check_row_59 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 59*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 59 j%3 := by
  decide +kernel

private theorem check_row_60 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 60*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 60 j%3 := by
  decide +kernel

private theorem check_row_61 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 61*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 61 j%3 := by
  decide +kernel

private theorem check_row_62 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 62*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 62 j%3 := by
  decide +kernel

private theorem check_row_63 : ∀ j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode 63*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit 63 j%3 := by
  decide +kernel

theorem packed_checks : ∀ i j : Fin 64,
    (((CFSGSuzFirstSquareKroneckerCaches.aRowCode i*CFSGSuzPackedBrayCacheB2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2.digit i j%3 := by
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
  (CFSG.Models.MatrixData.matrix 3 64 CFSG.Models.MatrixGroups.Suz.rows1)*(CFSGSuzPackedBrayProductB2.matrix)

theorem cache : matrix=CFSGSuzPackedBrayCacheAB2.data.matrix 3 := by
  exact product_eq_of_data (by decide : 0<64) _ _
    CFSGSuzFirstSquareKroneckerCaches.aData CFSGSuzPackedBrayCacheB2.data CFSGSuzPackedBrayCacheAB2.data
    CFSGSuzFirstSquareKroneckerCaches.literal_source_binding CFSGSuzPackedBrayProductB2.cache
    (by decide : 64*(3-1)^2<512) packed_checks

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductAB2
