import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductC
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheC2

/-! ONE edge of the fixed positive Suz DAG;64 selected row checks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductC2
open MatrixKroneckerProductReflection

private theorem check_row_00 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 0*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 0 j%3 := by
  decide +kernel

private theorem check_row_01 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 1*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 1 j%3 := by
  decide +kernel

private theorem check_row_02 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 2*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 2 j%3 := by
  decide +kernel

private theorem check_row_03 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 3*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 3 j%3 := by
  decide +kernel

private theorem check_row_04 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 4*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 4 j%3 := by
  decide +kernel

private theorem check_row_05 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 5*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 5 j%3 := by
  decide +kernel

private theorem check_row_06 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 6*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 6 j%3 := by
  decide +kernel

private theorem check_row_07 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 7*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 7 j%3 := by
  decide +kernel

private theorem check_row_08 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 8*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 8 j%3 := by
  decide +kernel

private theorem check_row_09 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 9*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 9 j%3 := by
  decide +kernel

private theorem check_row_10 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 10*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 10 j%3 := by
  decide +kernel

private theorem check_row_11 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 11*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 11 j%3 := by
  decide +kernel

private theorem check_row_12 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 12*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 12 j%3 := by
  decide +kernel

private theorem check_row_13 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 13*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 13 j%3 := by
  decide +kernel

private theorem check_row_14 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 14*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 14 j%3 := by
  decide +kernel

private theorem check_row_15 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 15*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 15 j%3 := by
  decide +kernel

private theorem check_row_16 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 16*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 16 j%3 := by
  decide +kernel

private theorem check_row_17 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 17*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 17 j%3 := by
  decide +kernel

private theorem check_row_18 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 18*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 18 j%3 := by
  decide +kernel

private theorem check_row_19 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 19*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 19 j%3 := by
  decide +kernel

private theorem check_row_20 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 20*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 20 j%3 := by
  decide +kernel

private theorem check_row_21 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 21*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 21 j%3 := by
  decide +kernel

private theorem check_row_22 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 22*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 22 j%3 := by
  decide +kernel

private theorem check_row_23 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 23*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 23 j%3 := by
  decide +kernel

private theorem check_row_24 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 24*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 24 j%3 := by
  decide +kernel

private theorem check_row_25 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 25*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 25 j%3 := by
  decide +kernel

private theorem check_row_26 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 26*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 26 j%3 := by
  decide +kernel

private theorem check_row_27 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 27*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 27 j%3 := by
  decide +kernel

private theorem check_row_28 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 28*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 28 j%3 := by
  decide +kernel

private theorem check_row_29 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 29*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 29 j%3 := by
  decide +kernel

private theorem check_row_30 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 30*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 30 j%3 := by
  decide +kernel

private theorem check_row_31 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 31*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 31 j%3 := by
  decide +kernel

private theorem check_row_32 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 32*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 32 j%3 := by
  decide +kernel

private theorem check_row_33 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 33*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 33 j%3 := by
  decide +kernel

private theorem check_row_34 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 34*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 34 j%3 := by
  decide +kernel

private theorem check_row_35 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 35*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 35 j%3 := by
  decide +kernel

private theorem check_row_36 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 36*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 36 j%3 := by
  decide +kernel

private theorem check_row_37 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 37*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 37 j%3 := by
  decide +kernel

private theorem check_row_38 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 38*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 38 j%3 := by
  decide +kernel

private theorem check_row_39 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 39*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 39 j%3 := by
  decide +kernel

private theorem check_row_40 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 40*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 40 j%3 := by
  decide +kernel

private theorem check_row_41 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 41*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 41 j%3 := by
  decide +kernel

private theorem check_row_42 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 42*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 42 j%3 := by
  decide +kernel

private theorem check_row_43 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 43*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 43 j%3 := by
  decide +kernel

private theorem check_row_44 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 44*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 44 j%3 := by
  decide +kernel

private theorem check_row_45 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 45*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 45 j%3 := by
  decide +kernel

private theorem check_row_46 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 46*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 46 j%3 := by
  decide +kernel

private theorem check_row_47 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 47*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 47 j%3 := by
  decide +kernel

private theorem check_row_48 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 48*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 48 j%3 := by
  decide +kernel

private theorem check_row_49 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 49*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 49 j%3 := by
  decide +kernel

private theorem check_row_50 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 50*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 50 j%3 := by
  decide +kernel

private theorem check_row_51 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 51*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 51 j%3 := by
  decide +kernel

private theorem check_row_52 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 52*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 52 j%3 := by
  decide +kernel

private theorem check_row_53 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 53*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 53 j%3 := by
  decide +kernel

private theorem check_row_54 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 54*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 54 j%3 := by
  decide +kernel

private theorem check_row_55 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 55*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 55 j%3 := by
  decide +kernel

private theorem check_row_56 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 56*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 56 j%3 := by
  decide +kernel

private theorem check_row_57 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 57*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 57 j%3 := by
  decide +kernel

private theorem check_row_58 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 58*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 58 j%3 := by
  decide +kernel

private theorem check_row_59 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 59*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 59 j%3 := by
  decide +kernel

private theorem check_row_60 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 60*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 60 j%3 := by
  decide +kernel

private theorem check_row_61 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 61*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 61 j%3 := by
  decide +kernel

private theorem check_row_62 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 62*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 62 j%3 := by
  decide +kernel

private theorem check_row_63 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode 63*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit 63 j%3 := by
  decide +kernel

theorem packed_checks : ∀ i j : Fin 64,
    (((CFSGSuzPackedBrayCacheC.rowCode i*CFSGSuzPackedBrayCacheC.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheC2.digit i j%3 := by
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
  (CFSGSuzPackedBrayProductC.matrix)*(CFSGSuzPackedBrayProductC.matrix)

theorem cache : matrix=CFSGSuzPackedBrayCacheC2.data.matrix 3 := by
  exact product_eq_of_data (by decide : 0<64) _ _
    CFSGSuzPackedBrayCacheC.data CFSGSuzPackedBrayCacheC.data CFSGSuzPackedBrayCacheC2.data
    CFSGSuzPackedBrayProductC.cache CFSGSuzPackedBrayProductC.cache
    (by decide : 64*(3-1)^2<512) packed_checks

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductC2
