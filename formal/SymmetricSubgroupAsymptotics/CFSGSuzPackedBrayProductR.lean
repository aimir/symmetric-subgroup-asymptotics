import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductAB2A
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheB
import SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheR

/-! ONE edge of the fixed positive Suz DAG;64 selected row checks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR
open MatrixKroneckerProductReflection

private theorem check_row_00 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 0*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 0 j%3 := by
  decide +kernel

private theorem check_row_01 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 1*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 1 j%3 := by
  decide +kernel

private theorem check_row_02 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 2*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 2 j%3 := by
  decide +kernel

private theorem check_row_03 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 3*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 3 j%3 := by
  decide +kernel

private theorem check_row_04 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 4*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 4 j%3 := by
  decide +kernel

private theorem check_row_05 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 5*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 5 j%3 := by
  decide +kernel

private theorem check_row_06 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 6*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 6 j%3 := by
  decide +kernel

private theorem check_row_07 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 7*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 7 j%3 := by
  decide +kernel

private theorem check_row_08 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 8*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 8 j%3 := by
  decide +kernel

private theorem check_row_09 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 9*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 9 j%3 := by
  decide +kernel

private theorem check_row_10 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 10*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 10 j%3 := by
  decide +kernel

private theorem check_row_11 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 11*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 11 j%3 := by
  decide +kernel

private theorem check_row_12 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 12*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 12 j%3 := by
  decide +kernel

private theorem check_row_13 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 13*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 13 j%3 := by
  decide +kernel

private theorem check_row_14 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 14*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 14 j%3 := by
  decide +kernel

private theorem check_row_15 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 15*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 15 j%3 := by
  decide +kernel

private theorem check_row_16 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 16*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 16 j%3 := by
  decide +kernel

private theorem check_row_17 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 17*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 17 j%3 := by
  decide +kernel

private theorem check_row_18 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 18*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 18 j%3 := by
  decide +kernel

private theorem check_row_19 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 19*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 19 j%3 := by
  decide +kernel

private theorem check_row_20 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 20*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 20 j%3 := by
  decide +kernel

private theorem check_row_21 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 21*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 21 j%3 := by
  decide +kernel

private theorem check_row_22 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 22*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 22 j%3 := by
  decide +kernel

private theorem check_row_23 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 23*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 23 j%3 := by
  decide +kernel

private theorem check_row_24 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 24*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 24 j%3 := by
  decide +kernel

private theorem check_row_25 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 25*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 25 j%3 := by
  decide +kernel

private theorem check_row_26 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 26*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 26 j%3 := by
  decide +kernel

private theorem check_row_27 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 27*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 27 j%3 := by
  decide +kernel

private theorem check_row_28 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 28*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 28 j%3 := by
  decide +kernel

private theorem check_row_29 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 29*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 29 j%3 := by
  decide +kernel

private theorem check_row_30 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 30*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 30 j%3 := by
  decide +kernel

private theorem check_row_31 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 31*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 31 j%3 := by
  decide +kernel

private theorem check_row_32 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 32*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 32 j%3 := by
  decide +kernel

private theorem check_row_33 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 33*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 33 j%3 := by
  decide +kernel

private theorem check_row_34 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 34*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 34 j%3 := by
  decide +kernel

private theorem check_row_35 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 35*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 35 j%3 := by
  decide +kernel

private theorem check_row_36 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 36*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 36 j%3 := by
  decide +kernel

private theorem check_row_37 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 37*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 37 j%3 := by
  decide +kernel

private theorem check_row_38 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 38*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 38 j%3 := by
  decide +kernel

private theorem check_row_39 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 39*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 39 j%3 := by
  decide +kernel

private theorem check_row_40 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 40*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 40 j%3 := by
  decide +kernel

private theorem check_row_41 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 41*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 41 j%3 := by
  decide +kernel

private theorem check_row_42 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 42*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 42 j%3 := by
  decide +kernel

private theorem check_row_43 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 43*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 43 j%3 := by
  decide +kernel

private theorem check_row_44 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 44*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 44 j%3 := by
  decide +kernel

private theorem check_row_45 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 45*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 45 j%3 := by
  decide +kernel

private theorem check_row_46 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 46*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 46 j%3 := by
  decide +kernel

private theorem check_row_47 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 47*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 47 j%3 := by
  decide +kernel

private theorem check_row_48 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 48*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 48 j%3 := by
  decide +kernel

private theorem check_row_49 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 49*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 49 j%3 := by
  decide +kernel

private theorem check_row_50 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 50*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 50 j%3 := by
  decide +kernel

private theorem check_row_51 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 51*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 51 j%3 := by
  decide +kernel

private theorem check_row_52 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 52*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 52 j%3 := by
  decide +kernel

private theorem check_row_53 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 53*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 53 j%3 := by
  decide +kernel

private theorem check_row_54 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 54*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 54 j%3 := by
  decide +kernel

private theorem check_row_55 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 55*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 55 j%3 := by
  decide +kernel

private theorem check_row_56 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 56*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 56 j%3 := by
  decide +kernel

private theorem check_row_57 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 57*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 57 j%3 := by
  decide +kernel

private theorem check_row_58 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 58*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 58 j%3 := by
  decide +kernel

private theorem check_row_59 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 59*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 59 j%3 := by
  decide +kernel

private theorem check_row_60 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 60*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 60 j%3 := by
  decide +kernel

private theorem check_row_61 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 61*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 61 j%3 := by
  decide +kernel

private theorem check_row_62 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 62*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 62 j%3 := by
  decide +kernel

private theorem check_row_63 : ∀ j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode 63*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit 63 j%3 := by
  decide +kernel

theorem packed_checks : ∀ i j : Fin 64,
    (((CFSGSuzPackedBrayCacheAB2A.rowCode i*CFSGSuzPackedBrayCacheB.columnCode j)/512^63)%512)%3=CFSGSuzPackedBrayCacheR.digit i j%3 := by
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
  (CFSGSuzPackedBrayProductAB2A.matrix)*(CFSG.Models.MatrixData.matrix 3 64 CFSG.Models.MatrixGroups.Suz.rows2)

theorem cache : matrix=CFSGSuzPackedBrayCacheR.data.matrix 3 := by
  exact product_eq_of_data (by decide : 0<64) _ _
    CFSGSuzPackedBrayCacheAB2A.data CFSGSuzPackedBrayCacheB.data CFSGSuzPackedBrayCacheR.data
    CFSGSuzPackedBrayProductAB2A.cache CFSGSuzPackedBrayCacheB.literal_source_binding
    (by decide : 64*(3-1)^2<512) packed_checks

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayProductR
