import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductAB2
import SymmetricSubgroupAsymptotics.CFSGSuzFirstSquareKroneckerCaches
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheAB2A

/-! ONE edge of the fixed positive Suz DAG;64 selected row checks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductAB2A
open MatrixKroneckerProductReflection

private theorem check_row_00 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 0*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 0 j%3 := by
  decide +kernel

private theorem check_row_01 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 1*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 1 j%3 := by
  decide +kernel

private theorem check_row_02 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 2*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 2 j%3 := by
  decide +kernel

private theorem check_row_03 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 3*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 3 j%3 := by
  decide +kernel

private theorem check_row_04 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 4*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 4 j%3 := by
  decide +kernel

private theorem check_row_05 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 5*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 5 j%3 := by
  decide +kernel

private theorem check_row_06 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 6*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 6 j%3 := by
  decide +kernel

private theorem check_row_07 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 7*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 7 j%3 := by
  decide +kernel

private theorem check_row_08 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 8*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 8 j%3 := by
  decide +kernel

private theorem check_row_09 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 9*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 9 j%3 := by
  decide +kernel

private theorem check_row_10 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 10*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 10 j%3 := by
  decide +kernel

private theorem check_row_11 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 11*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 11 j%3 := by
  decide +kernel

private theorem check_row_12 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 12*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 12 j%3 := by
  decide +kernel

private theorem check_row_13 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 13*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 13 j%3 := by
  decide +kernel

private theorem check_row_14 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 14*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 14 j%3 := by
  decide +kernel

private theorem check_row_15 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 15*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 15 j%3 := by
  decide +kernel

private theorem check_row_16 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 16*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 16 j%3 := by
  decide +kernel

private theorem check_row_17 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 17*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 17 j%3 := by
  decide +kernel

private theorem check_row_18 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 18*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 18 j%3 := by
  decide +kernel

private theorem check_row_19 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 19*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 19 j%3 := by
  decide +kernel

private theorem check_row_20 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 20*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 20 j%3 := by
  decide +kernel

private theorem check_row_21 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 21*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 21 j%3 := by
  decide +kernel

private theorem check_row_22 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 22*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 22 j%3 := by
  decide +kernel

private theorem check_row_23 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 23*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 23 j%3 := by
  decide +kernel

private theorem check_row_24 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 24*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 24 j%3 := by
  decide +kernel

private theorem check_row_25 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 25*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 25 j%3 := by
  decide +kernel

private theorem check_row_26 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 26*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 26 j%3 := by
  decide +kernel

private theorem check_row_27 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 27*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 27 j%3 := by
  decide +kernel

private theorem check_row_28 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 28*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 28 j%3 := by
  decide +kernel

private theorem check_row_29 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 29*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 29 j%3 := by
  decide +kernel

private theorem check_row_30 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 30*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 30 j%3 := by
  decide +kernel

private theorem check_row_31 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 31*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 31 j%3 := by
  decide +kernel

private theorem check_row_32 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 32*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 32 j%3 := by
  decide +kernel

private theorem check_row_33 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 33*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 33 j%3 := by
  decide +kernel

private theorem check_row_34 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 34*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 34 j%3 := by
  decide +kernel

private theorem check_row_35 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 35*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 35 j%3 := by
  decide +kernel

private theorem check_row_36 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 36*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 36 j%3 := by
  decide +kernel

private theorem check_row_37 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 37*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 37 j%3 := by
  decide +kernel

private theorem check_row_38 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 38*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 38 j%3 := by
  decide +kernel

private theorem check_row_39 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 39*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 39 j%3 := by
  decide +kernel

private theorem check_row_40 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 40*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 40 j%3 := by
  decide +kernel

private theorem check_row_41 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 41*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 41 j%3 := by
  decide +kernel

private theorem check_row_42 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 42*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 42 j%3 := by
  decide +kernel

private theorem check_row_43 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 43*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 43 j%3 := by
  decide +kernel

private theorem check_row_44 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 44*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 44 j%3 := by
  decide +kernel

private theorem check_row_45 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 45*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 45 j%3 := by
  decide +kernel

private theorem check_row_46 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 46*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 46 j%3 := by
  decide +kernel

private theorem check_row_47 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 47*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 47 j%3 := by
  decide +kernel

private theorem check_row_48 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 48*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 48 j%3 := by
  decide +kernel

private theorem check_row_49 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 49*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 49 j%3 := by
  decide +kernel

private theorem check_row_50 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 50*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 50 j%3 := by
  decide +kernel

private theorem check_row_51 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 51*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 51 j%3 := by
  decide +kernel

private theorem check_row_52 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 52*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 52 j%3 := by
  decide +kernel

private theorem check_row_53 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 53*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 53 j%3 := by
  decide +kernel

private theorem check_row_54 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 54*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 54 j%3 := by
  decide +kernel

private theorem check_row_55 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 55*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 55 j%3 := by
  decide +kernel

private theorem check_row_56 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 56*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 56 j%3 := by
  decide +kernel

private theorem check_row_57 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 57*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 57 j%3 := by
  decide +kernel

private theorem check_row_58 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 58*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 58 j%3 := by
  decide +kernel

private theorem check_row_59 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 59*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 59 j%3 := by
  decide +kernel

private theorem check_row_60 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 60*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 60 j%3 := by
  decide +kernel

private theorem check_row_61 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 61*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 61 j%3 := by
  decide +kernel

private theorem check_row_62 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 62*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 62 j%3 := by
  decide +kernel

private theorem check_row_63 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode 63*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit 63 j%3 := by
  decide +kernel

theorem packed_checks : ∀ i j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2.rowCode i*CFSGSuzFirstSquareKroneckerCaches.aColumnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheAB2A.digit i j%3 := by
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
  (CFSGSuzPackedBrayProductAB2.matrix)*(CFSG.Models.MatrixData.matrix 3 64 CFSG.Models.MatrixGroups.Suz.rows1)

theorem cache : matrix=CFSGSuzPackedBrayCacheAB2A.data.matrix 3 := by
  exact product_eq_of_data (by decide : 0<64) _ _
    CFSGSuzPackedBrayCacheAB2.data CFSGSuzFirstSquareKroneckerCaches.aData CFSGSuzPackedBrayCacheAB2A.data
    CFSGSuzPackedBrayProductAB2.cache CFSGSuzFirstSquareKroneckerCaches.literal_source_binding
    (by decide : 64*(3-1)^2<512) packed_checks

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductAB2A
