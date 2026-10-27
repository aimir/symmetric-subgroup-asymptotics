import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR12
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR2
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheR14

/-! ONE edge of the fixed positive Suz DAG;64 selected row checks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR14
open MatrixKroneckerProductReflection

private theorem check_row_00 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 0*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 0 j%3 := by
  decide +kernel

private theorem check_row_01 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 1*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 1 j%3 := by
  decide +kernel

private theorem check_row_02 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 2*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 2 j%3 := by
  decide +kernel

private theorem check_row_03 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 3*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 3 j%3 := by
  decide +kernel

private theorem check_row_04 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 4*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 4 j%3 := by
  decide +kernel

private theorem check_row_05 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 5*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 5 j%3 := by
  decide +kernel

private theorem check_row_06 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 6*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 6 j%3 := by
  decide +kernel

private theorem check_row_07 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 7*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 7 j%3 := by
  decide +kernel

private theorem check_row_08 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 8*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 8 j%3 := by
  decide +kernel

private theorem check_row_09 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 9*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 9 j%3 := by
  decide +kernel

private theorem check_row_10 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 10*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 10 j%3 := by
  decide +kernel

private theorem check_row_11 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 11*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 11 j%3 := by
  decide +kernel

private theorem check_row_12 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 12*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 12 j%3 := by
  decide +kernel

private theorem check_row_13 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 13*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 13 j%3 := by
  decide +kernel

private theorem check_row_14 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 14*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 14 j%3 := by
  decide +kernel

private theorem check_row_15 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 15*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 15 j%3 := by
  decide +kernel

private theorem check_row_16 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 16*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 16 j%3 := by
  decide +kernel

private theorem check_row_17 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 17*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 17 j%3 := by
  decide +kernel

private theorem check_row_18 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 18*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 18 j%3 := by
  decide +kernel

private theorem check_row_19 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 19*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 19 j%3 := by
  decide +kernel

private theorem check_row_20 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 20*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 20 j%3 := by
  decide +kernel

private theorem check_row_21 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 21*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 21 j%3 := by
  decide +kernel

private theorem check_row_22 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 22*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 22 j%3 := by
  decide +kernel

private theorem check_row_23 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 23*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 23 j%3 := by
  decide +kernel

private theorem check_row_24 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 24*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 24 j%3 := by
  decide +kernel

private theorem check_row_25 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 25*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 25 j%3 := by
  decide +kernel

private theorem check_row_26 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 26*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 26 j%3 := by
  decide +kernel

private theorem check_row_27 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 27*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 27 j%3 := by
  decide +kernel

private theorem check_row_28 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 28*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 28 j%3 := by
  decide +kernel

private theorem check_row_29 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 29*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 29 j%3 := by
  decide +kernel

private theorem check_row_30 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 30*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 30 j%3 := by
  decide +kernel

private theorem check_row_31 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 31*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 31 j%3 := by
  decide +kernel

private theorem check_row_32 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 32*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 32 j%3 := by
  decide +kernel

private theorem check_row_33 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 33*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 33 j%3 := by
  decide +kernel

private theorem check_row_34 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 34*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 34 j%3 := by
  decide +kernel

private theorem check_row_35 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 35*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 35 j%3 := by
  decide +kernel

private theorem check_row_36 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 36*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 36 j%3 := by
  decide +kernel

private theorem check_row_37 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 37*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 37 j%3 := by
  decide +kernel

private theorem check_row_38 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 38*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 38 j%3 := by
  decide +kernel

private theorem check_row_39 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 39*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 39 j%3 := by
  decide +kernel

private theorem check_row_40 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 40*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 40 j%3 := by
  decide +kernel

private theorem check_row_41 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 41*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 41 j%3 := by
  decide +kernel

private theorem check_row_42 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 42*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 42 j%3 := by
  decide +kernel

private theorem check_row_43 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 43*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 43 j%3 := by
  decide +kernel

private theorem check_row_44 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 44*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 44 j%3 := by
  decide +kernel

private theorem check_row_45 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 45*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 45 j%3 := by
  decide +kernel

private theorem check_row_46 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 46*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 46 j%3 := by
  decide +kernel

private theorem check_row_47 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 47*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 47 j%3 := by
  decide +kernel

private theorem check_row_48 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 48*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 48 j%3 := by
  decide +kernel

private theorem check_row_49 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 49*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 49 j%3 := by
  decide +kernel

private theorem check_row_50 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 50*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 50 j%3 := by
  decide +kernel

private theorem check_row_51 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 51*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 51 j%3 := by
  decide +kernel

private theorem check_row_52 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 52*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 52 j%3 := by
  decide +kernel

private theorem check_row_53 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 53*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 53 j%3 := by
  decide +kernel

private theorem check_row_54 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 54*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 54 j%3 := by
  decide +kernel

private theorem check_row_55 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 55*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 55 j%3 := by
  decide +kernel

private theorem check_row_56 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 56*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 56 j%3 := by
  decide +kernel

private theorem check_row_57 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 57*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 57 j%3 := by
  decide +kernel

private theorem check_row_58 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 58*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 58 j%3 := by
  decide +kernel

private theorem check_row_59 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 59*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 59 j%3 := by
  decide +kernel

private theorem check_row_60 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 60*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 60 j%3 := by
  decide +kernel

private theorem check_row_61 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 61*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 61 j%3 := by
  decide +kernel

private theorem check_row_62 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 62*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 62 j%3 := by
  decide +kernel

private theorem check_row_63 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode 63*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit 63 j%3 := by
  decide +kernel

theorem packed_checks : ∀ i j : Fin 64,
    (((CFSGSuzPackedBrayCacheR12.rowCode i*CFSGSuzPackedBrayCacheR2.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR14.digit i j%3 := by
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
  (CFSGSuzPackedBrayProductR12.matrix)*(CFSGSuzPackedBrayProductR2.matrix)

theorem cache : matrix=CFSGSuzPackedBrayCacheR14.data.matrix 3 := by
  exact product_eq_of_data (by decide : 0<64) _ _
    CFSGSuzPackedBrayCacheR12.data CFSGSuzPackedBrayCacheR2.data CFSGSuzPackedBrayCacheR14.data
    CFSGSuzPackedBrayProductR12.cache CFSGSuzPackedBrayProductR2.cache
    (by decide : 64*(3-1)^2<512) packed_checks

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR14
