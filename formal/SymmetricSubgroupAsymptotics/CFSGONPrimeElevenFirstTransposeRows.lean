import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.CFSGONPrimeElevenPackedData
import SymmetricSubgroupAsymptotics.CFSGONCachedColumnRowVectorBinding

/-! Packed-Nat transpose only. Original source binding reuses old checked column caches. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGONPrimeElevenFirstTransposeRows
open MatrixNaturalRowDotReflection CFSGONPrimeElevenPackedData

private theorem row_0 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 0=
      packedDigit 2 (firstRowCode 0) j.val := by
  rw [first_row_zero_code]
  exact CFSGONSelectedPrimeElevenTransposeRowZeroPilot.first_transpose

private theorem row_1 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 1=
      packedDigit 2 (firstRowCode 1) j.val := by
  decide +kernel

private theorem row_2 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 2=
      packedDigit 2 (firstRowCode 2) j.val := by
  decide +kernel

private theorem row_3 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 3=
      packedDigit 2 (firstRowCode 3) j.val := by
  decide +kernel

private theorem row_4 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 4=
      packedDigit 2 (firstRowCode 4) j.val := by
  decide +kernel

private theorem row_5 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 5=
      packedDigit 2 (firstRowCode 5) j.val := by
  decide +kernel

private theorem row_6 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 6=
      packedDigit 2 (firstRowCode 6) j.val := by
  decide +kernel

private theorem row_7 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 7=
      packedDigit 2 (firstRowCode 7) j.val := by
  decide +kernel

private theorem row_8 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 8=
      packedDigit 2 (firstRowCode 8) j.val := by
  decide +kernel

private theorem row_9 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 9=
      packedDigit 2 (firstRowCode 9) j.val := by
  decide +kernel

private theorem row_10 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 10=
      packedDigit 2 (firstRowCode 10) j.val := by
  decide +kernel

private theorem row_11 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 11=
      packedDigit 2 (firstRowCode 11) j.val := by
  decide +kernel

private theorem row_12 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 12=
      packedDigit 2 (firstRowCode 12) j.val := by
  decide +kernel

private theorem row_13 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 13=
      packedDigit 2 (firstRowCode 13) j.val := by
  decide +kernel

private theorem row_14 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 14=
      packedDigit 2 (firstRowCode 14) j.val := by
  decide +kernel

private theorem row_15 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 15=
      packedDigit 2 (firstRowCode 15) j.val := by
  decide +kernel

private theorem row_16 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 16=
      packedDigit 2 (firstRowCode 16) j.val := by
  decide +kernel

private theorem row_17 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 17=
      packedDigit 2 (firstRowCode 17) j.val := by
  decide +kernel

private theorem row_18 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 18=
      packedDigit 2 (firstRowCode 18) j.val := by
  decide +kernel

private theorem row_19 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 19=
      packedDigit 2 (firstRowCode 19) j.val := by
  decide +kernel

private theorem row_20 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 20=
      packedDigit 2 (firstRowCode 20) j.val := by
  decide +kernel

private theorem row_21 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 21=
      packedDigit 2 (firstRowCode 21) j.val := by
  decide +kernel

private theorem row_22 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 22=
      packedDigit 2 (firstRowCode 22) j.val := by
  decide +kernel

private theorem row_23 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 23=
      packedDigit 2 (firstRowCode 23) j.val := by
  decide +kernel

private theorem row_24 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 24=
      packedDigit 2 (firstRowCode 24) j.val := by
  decide +kernel

private theorem row_25 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 25=
      packedDigit 2 (firstRowCode 25) j.val := by
  decide +kernel

private theorem row_26 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 26=
      packedDigit 2 (firstRowCode 26) j.val := by
  decide +kernel

private theorem row_27 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 27=
      packedDigit 2 (firstRowCode 27) j.val := by
  decide +kernel

private theorem row_28 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 28=
      packedDigit 2 (firstRowCode 28) j.val := by
  decide +kernel

private theorem row_29 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 29=
      packedDigit 2 (firstRowCode 29) j.val := by
  decide +kernel

private theorem row_30 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 30=
      packedDigit 2 (firstRowCode 30) j.val := by
  decide +kernel

private theorem row_31 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 31=
      packedDigit 2 (firstRowCode 31) j.val := by
  decide +kernel

private theorem row_32 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 32=
      packedDigit 2 (firstRowCode 32) j.val := by
  decide +kernel

private theorem row_33 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 33=
      packedDigit 2 (firstRowCode 33) j.val := by
  decide +kernel

private theorem row_34 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 34=
      packedDigit 2 (firstRowCode 34) j.val := by
  decide +kernel

private theorem row_35 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 35=
      packedDigit 2 (firstRowCode 35) j.val := by
  decide +kernel

private theorem row_36 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 36=
      packedDigit 2 (firstRowCode 36) j.val := by
  decide +kernel

private theorem row_37 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 37=
      packedDigit 2 (firstRowCode 37) j.val := by
  decide +kernel

private theorem row_38 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 38=
      packedDigit 2 (firstRowCode 38) j.val := by
  decide +kernel

private theorem row_39 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 39=
      packedDigit 2 (firstRowCode 39) j.val := by
  decide +kernel

private theorem row_40 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 40=
      packedDigit 2 (firstRowCode 40) j.val := by
  decide +kernel

private theorem row_41 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 41=
      packedDigit 2 (firstRowCode 41) j.val := by
  decide +kernel

private theorem row_42 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 42=
      packedDigit 2 (firstRowCode 42) j.val := by
  decide +kernel

private theorem row_43 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 43=
      packedDigit 2 (firstRowCode 43) j.val := by
  decide +kernel

private theorem row_44 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 44=
      packedDigit 2 (firstRowCode 44) j.val := by
  decide +kernel

private theorem row_45 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 45=
      packedDigit 2 (firstRowCode 45) j.val := by
  decide +kernel

private theorem row_46 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 46=
      packedDigit 2 (firstRowCode 46) j.val := by
  decide +kernel

private theorem row_47 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 47=
      packedDigit 2 (firstRowCode 47) j.val := by
  decide +kernel

private theorem row_48 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 48=
      packedDigit 2 (firstRowCode 48) j.val := by
  decide +kernel

private theorem row_49 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 49=
      packedDigit 2 (firstRowCode 49) j.val := by
  decide +kernel

private theorem row_50 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 50=
      packedDigit 2 (firstRowCode 50) j.val := by
  decide +kernel

private theorem row_51 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 51=
      packedDigit 2 (firstRowCode 51) j.val := by
  decide +kernel

private theorem row_52 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 52=
      packedDigit 2 (firstRowCode 52) j.val := by
  decide +kernel

private theorem row_53 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 53=
      packedDigit 2 (firstRowCode 53) j.val := by
  decide +kernel

private theorem row_54 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 54=
      packedDigit 2 (firstRowCode 54) j.val := by
  decide +kernel

private theorem row_55 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 55=
      packedDigit 2 (firstRowCode 55) j.val := by
  decide +kernel

private theorem row_56 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 56=
      packedDigit 2 (firstRowCode 56) j.val := by
  decide +kernel

private theorem row_57 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 57=
      packedDigit 2 (firstRowCode 57) j.val := by
  decide +kernel

private theorem row_58 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 58=
      packedDigit 2 (firstRowCode 58) j.val := by
  decide +kernel

private theorem row_59 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 59=
      packedDigit 2 (firstRowCode 59) j.val := by
  decide +kernel

private theorem row_60 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 60=
      packedDigit 2 (firstRowCode 60) j.val := by
  decide +kernel

private theorem row_61 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 61=
      packedDigit 2 (firstRowCode 61) j.val := by
  decide +kernel

private theorem row_62 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 62=
      packedDigit 2 (firstRowCode 62) j.val := by
  decide +kernel

private theorem row_63 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 63=
      packedDigit 2 (firstRowCode 63) j.val := by
  decide +kernel

private theorem row_64 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 64=
      packedDigit 2 (firstRowCode 64) j.val := by
  decide +kernel

private theorem row_65 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 65=
      packedDigit 2 (firstRowCode 65) j.val := by
  decide +kernel

private theorem row_66 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 66=
      packedDigit 2 (firstRowCode 66) j.val := by
  decide +kernel

private theorem row_67 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 67=
      packedDigit 2 (firstRowCode 67) j.val := by
  decide +kernel

private theorem row_68 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 68=
      packedDigit 2 (firstRowCode 68) j.val := by
  decide +kernel

private theorem row_69 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 69=
      packedDigit 2 (firstRowCode 69) j.val := by
  decide +kernel

private theorem row_70 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 70=
      packedDigit 2 (firstRowCode 70) j.val := by
  decide +kernel

private theorem row_71 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 71=
      packedDigit 2 (firstRowCode 71) j.val := by
  decide +kernel

private theorem row_72 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 72=
      packedDigit 2 (firstRowCode 72) j.val := by
  decide +kernel

private theorem row_73 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 73=
      packedDigit 2 (firstRowCode 73) j.val := by
  decide +kernel

private theorem row_74 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 74=
      packedDigit 2 (firstRowCode 74) j.val := by
  decide +kernel

private theorem row_75 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 75=
      packedDigit 2 (firstRowCode 75) j.val := by
  decide +kernel

private theorem row_76 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 76=
      packedDigit 2 (firstRowCode 76) j.val := by
  decide +kernel

private theorem row_77 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 77=
      packedDigit 2 (firstRowCode 77) j.val := by
  decide +kernel

private theorem row_78 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 78=
      packedDigit 2 (firstRowCode 78) j.val := by
  decide +kernel

private theorem row_79 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 79=
      packedDigit 2 (firstRowCode 79) j.val := by
  decide +kernel

private theorem row_80 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 80=
      packedDigit 2 (firstRowCode 80) j.val := by
  decide +kernel

private theorem row_81 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 81=
      packedDigit 2 (firstRowCode 81) j.val := by
  decide +kernel

private theorem row_82 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 82=
      packedDigit 2 (firstRowCode 82) j.val := by
  decide +kernel

private theorem row_83 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 83=
      packedDigit 2 (firstRowCode 83) j.val := by
  decide +kernel

private theorem row_84 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 84=
      packedDigit 2 (firstRowCode 84) j.val := by
  decide +kernel

private theorem row_85 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 85=
      packedDigit 2 (firstRowCode 85) j.val := by
  decide +kernel

private theorem row_86 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 86=
      packedDigit 2 (firstRowCode 86) j.val := by
  decide +kernel

private theorem row_87 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 87=
      packedDigit 2 (firstRowCode 87) j.val := by
  decide +kernel

private theorem row_88 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 88=
      packedDigit 2 (firstRowCode 88) j.val := by
  decide +kernel

private theorem row_89 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 89=
      packedDigit 2 (firstRowCode 89) j.val := by
  decide +kernel

private theorem row_90 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 90=
      packedDigit 2 (firstRowCode 90) j.val := by
  decide +kernel

private theorem row_91 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 91=
      packedDigit 2 (firstRowCode 91) j.val := by
  decide +kernel

private theorem row_92 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 92=
      packedDigit 2 (firstRowCode 92) j.val := by
  decide +kernel

private theorem row_93 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 93=
      packedDigit 2 (firstRowCode 93) j.val := by
  decide +kernel

private theorem row_94 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 94=
      packedDigit 2 (firstRowCode 94) j.val := by
  decide +kernel

private theorem row_95 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 95=
      packedDigit 2 (firstRowCode 95) j.val := by
  decide +kernel

private theorem row_96 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 96=
      packedDigit 2 (firstRowCode 96) j.val := by
  decide +kernel

private theorem row_97 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 97=
      packedDigit 2 (firstRowCode 97) j.val := by
  decide +kernel

private theorem row_98 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 98=
      packedDigit 2 (firstRowCode 98) j.val := by
  decide +kernel

private theorem row_99 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 99=
      packedDigit 2 (firstRowCode 99) j.val := by
  decide +kernel

private theorem row_100 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 100=
      packedDigit 2 (firstRowCode 100) j.val := by
  decide +kernel

private theorem row_101 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 101=
      packedDigit 2 (firstRowCode 101) j.val := by
  decide +kernel

private theorem row_102 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 102=
      packedDigit 2 (firstRowCode 102) j.val := by
  decide +kernel

private theorem row_103 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 103=
      packedDigit 2 (firstRowCode 103) j.val := by
  decide +kernel

private theorem row_104 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 104=
      packedDigit 2 (firstRowCode 104) j.val := by
  decide +kernel

private theorem row_105 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 105=
      packedDigit 2 (firstRowCode 105) j.val := by
  decide +kernel

private theorem row_106 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 106=
      packedDigit 2 (firstRowCode 106) j.val := by
  decide +kernel

private theorem row_107 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 107=
      packedDigit 2 (firstRowCode 107) j.val := by
  decide +kernel

private theorem row_108 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 108=
      packedDigit 2 (firstRowCode 108) j.val := by
  decide +kernel

private theorem row_109 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 109=
      packedDigit 2 (firstRowCode 109) j.val := by
  decide +kernel

private theorem row_110 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 110=
      packedDigit 2 (firstRowCode 110) j.val := by
  decide +kernel

private theorem row_111 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 111=
      packedDigit 2 (firstRowCode 111) j.val := by
  decide +kernel

private theorem row_112 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 112=
      packedDigit 2 (firstRowCode 112) j.val := by
  decide +kernel

private theorem row_113 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 113=
      packedDigit 2 (firstRowCode 113) j.val := by
  decide +kernel

private theorem row_114 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 114=
      packedDigit 2 (firstRowCode 114) j.val := by
  decide +kernel

private theorem row_115 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 115=
      packedDigit 2 (firstRowCode 115) j.val := by
  decide +kernel

private theorem row_116 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 116=
      packedDigit 2 (firstRowCode 116) j.val := by
  decide +kernel

private theorem row_117 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 117=
      packedDigit 2 (firstRowCode 117) j.val := by
  decide +kernel

private theorem row_118 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 118=
      packedDigit 2 (firstRowCode 118) j.val := by
  decide +kernel

private theorem row_119 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 119=
      packedDigit 2 (firstRowCode 119) j.val := by
  decide +kernel

private theorem row_120 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 120=
      packedDigit 2 (firstRowCode 120) j.val := by
  decide +kernel

private theorem row_121 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 121=
      packedDigit 2 (firstRowCode 121) j.val := by
  decide +kernel

private theorem row_122 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 122=
      packedDigit 2 (firstRowCode 122) j.val := by
  decide +kernel

private theorem row_123 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 123=
      packedDigit 2 (firstRowCode 123) j.val := by
  decide +kernel

private theorem row_124 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 124=
      packedDigit 2 (firstRowCode 124) j.val := by
  decide +kernel

private theorem row_125 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 125=
      packedDigit 2 (firstRowCode 125) j.val := by
  decide +kernel

private theorem row_126 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 126=
      packedDigit 2 (firstRowCode 126) j.val := by
  decide +kernel

private theorem row_127 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 127=
      packedDigit 2 (firstRowCode 127) j.val := by
  decide +kernel

private theorem row_128 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 128=
      packedDigit 2 (firstRowCode 128) j.val := by
  decide +kernel

private theorem row_129 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 129=
      packedDigit 2 (firstRowCode 129) j.val := by
  decide +kernel

private theorem row_130 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 130=
      packedDigit 2 (firstRowCode 130) j.val := by
  decide +kernel

private theorem row_131 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 131=
      packedDigit 2 (firstRowCode 131) j.val := by
  decide +kernel

private theorem row_132 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 132=
      packedDigit 2 (firstRowCode 132) j.val := by
  decide +kernel

private theorem row_133 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 133=
      packedDigit 2 (firstRowCode 133) j.val := by
  decide +kernel

private theorem row_134 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 134=
      packedDigit 2 (firstRowCode 134) j.val := by
  decide +kernel

private theorem row_135 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 135=
      packedDigit 2 (firstRowCode 135) j.val := by
  decide +kernel

private theorem row_136 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 136=
      packedDigit 2 (firstRowCode 136) j.val := by
  decide +kernel

private theorem row_137 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 137=
      packedDigit 2 (firstRowCode 137) j.val := by
  decide +kernel

private theorem row_138 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 138=
      packedDigit 2 (firstRowCode 138) j.val := by
  decide +kernel

private theorem row_139 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 139=
      packedDigit 2 (firstRowCode 139) j.val := by
  decide +kernel

private theorem row_140 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 140=
      packedDigit 2 (firstRowCode 140) j.val := by
  decide +kernel

private theorem row_141 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 141=
      packedDigit 2 (firstRowCode 141) j.val := by
  decide +kernel

private theorem row_142 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 142=
      packedDigit 2 (firstRowCode 142) j.val := by
  decide +kernel

private theorem row_143 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 143=
      packedDigit 2 (firstRowCode 143) j.val := by
  decide +kernel

private theorem row_144 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 144=
      packedDigit 2 (firstRowCode 144) j.val := by
  decide +kernel

private theorem row_145 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 145=
      packedDigit 2 (firstRowCode 145) j.val := by
  decide +kernel

private theorem row_146 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 146=
      packedDigit 2 (firstRowCode 146) j.val := by
  decide +kernel

private theorem row_147 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 147=
      packedDigit 2 (firstRowCode 147) j.val := by
  decide +kernel

private theorem row_148 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 148=
      packedDigit 2 (firstRowCode 148) j.val := by
  decide +kernel

private theorem row_149 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 149=
      packedDigit 2 (firstRowCode 149) j.val := by
  decide +kernel

private theorem row_150 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 150=
      packedDigit 2 (firstRowCode 150) j.val := by
  decide +kernel

private theorem row_151 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 151=
      packedDigit 2 (firstRowCode 151) j.val := by
  decide +kernel

private theorem row_152 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 152=
      packedDigit 2 (firstRowCode 152) j.val := by
  decide +kernel

private theorem row_153 : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 153=
      packedDigit 2 (firstRowCode 153) j.val := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem transpose (i j : Fin 154) :
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) i.val=
      packedDigit 2 (firstRowCode i.val) j.val := by
  fin_cases i
  · simpa only [Fin.val_mk] using row_0 j
  · simpa only [Fin.val_mk] using row_1 j
  · simpa only [Fin.val_mk] using row_2 j
  · simpa only [Fin.val_mk] using row_3 j
  · simpa only [Fin.val_mk] using row_4 j
  · simpa only [Fin.val_mk] using row_5 j
  · simpa only [Fin.val_mk] using row_6 j
  · simpa only [Fin.val_mk] using row_7 j
  · simpa only [Fin.val_mk] using row_8 j
  · simpa only [Fin.val_mk] using row_9 j
  · simpa only [Fin.val_mk] using row_10 j
  · simpa only [Fin.val_mk] using row_11 j
  · simpa only [Fin.val_mk] using row_12 j
  · simpa only [Fin.val_mk] using row_13 j
  · simpa only [Fin.val_mk] using row_14 j
  · simpa only [Fin.val_mk] using row_15 j
  · simpa only [Fin.val_mk] using row_16 j
  · simpa only [Fin.val_mk] using row_17 j
  · simpa only [Fin.val_mk] using row_18 j
  · simpa only [Fin.val_mk] using row_19 j
  · simpa only [Fin.val_mk] using row_20 j
  · simpa only [Fin.val_mk] using row_21 j
  · simpa only [Fin.val_mk] using row_22 j
  · simpa only [Fin.val_mk] using row_23 j
  · simpa only [Fin.val_mk] using row_24 j
  · simpa only [Fin.val_mk] using row_25 j
  · simpa only [Fin.val_mk] using row_26 j
  · simpa only [Fin.val_mk] using row_27 j
  · simpa only [Fin.val_mk] using row_28 j
  · simpa only [Fin.val_mk] using row_29 j
  · simpa only [Fin.val_mk] using row_30 j
  · simpa only [Fin.val_mk] using row_31 j
  · simpa only [Fin.val_mk] using row_32 j
  · simpa only [Fin.val_mk] using row_33 j
  · simpa only [Fin.val_mk] using row_34 j
  · simpa only [Fin.val_mk] using row_35 j
  · simpa only [Fin.val_mk] using row_36 j
  · simpa only [Fin.val_mk] using row_37 j
  · simpa only [Fin.val_mk] using row_38 j
  · simpa only [Fin.val_mk] using row_39 j
  · simpa only [Fin.val_mk] using row_40 j
  · simpa only [Fin.val_mk] using row_41 j
  · simpa only [Fin.val_mk] using row_42 j
  · simpa only [Fin.val_mk] using row_43 j
  · simpa only [Fin.val_mk] using row_44 j
  · simpa only [Fin.val_mk] using row_45 j
  · simpa only [Fin.val_mk] using row_46 j
  · simpa only [Fin.val_mk] using row_47 j
  · simpa only [Fin.val_mk] using row_48 j
  · simpa only [Fin.val_mk] using row_49 j
  · simpa only [Fin.val_mk] using row_50 j
  · simpa only [Fin.val_mk] using row_51 j
  · simpa only [Fin.val_mk] using row_52 j
  · simpa only [Fin.val_mk] using row_53 j
  · simpa only [Fin.val_mk] using row_54 j
  · simpa only [Fin.val_mk] using row_55 j
  · simpa only [Fin.val_mk] using row_56 j
  · simpa only [Fin.val_mk] using row_57 j
  · simpa only [Fin.val_mk] using row_58 j
  · simpa only [Fin.val_mk] using row_59 j
  · simpa only [Fin.val_mk] using row_60 j
  · simpa only [Fin.val_mk] using row_61 j
  · simpa only [Fin.val_mk] using row_62 j
  · simpa only [Fin.val_mk] using row_63 j
  · simpa only [Fin.val_mk] using row_64 j
  · simpa only [Fin.val_mk] using row_65 j
  · simpa only [Fin.val_mk] using row_66 j
  · simpa only [Fin.val_mk] using row_67 j
  · simpa only [Fin.val_mk] using row_68 j
  · simpa only [Fin.val_mk] using row_69 j
  · simpa only [Fin.val_mk] using row_70 j
  · simpa only [Fin.val_mk] using row_71 j
  · simpa only [Fin.val_mk] using row_72 j
  · simpa only [Fin.val_mk] using row_73 j
  · simpa only [Fin.val_mk] using row_74 j
  · simpa only [Fin.val_mk] using row_75 j
  · simpa only [Fin.val_mk] using row_76 j
  · simpa only [Fin.val_mk] using row_77 j
  · simpa only [Fin.val_mk] using row_78 j
  · simpa only [Fin.val_mk] using row_79 j
  · simpa only [Fin.val_mk] using row_80 j
  · simpa only [Fin.val_mk] using row_81 j
  · simpa only [Fin.val_mk] using row_82 j
  · simpa only [Fin.val_mk] using row_83 j
  · simpa only [Fin.val_mk] using row_84 j
  · simpa only [Fin.val_mk] using row_85 j
  · simpa only [Fin.val_mk] using row_86 j
  · simpa only [Fin.val_mk] using row_87 j
  · simpa only [Fin.val_mk] using row_88 j
  · simpa only [Fin.val_mk] using row_89 j
  · simpa only [Fin.val_mk] using row_90 j
  · simpa only [Fin.val_mk] using row_91 j
  · simpa only [Fin.val_mk] using row_92 j
  · simpa only [Fin.val_mk] using row_93 j
  · simpa only [Fin.val_mk] using row_94 j
  · simpa only [Fin.val_mk] using row_95 j
  · simpa only [Fin.val_mk] using row_96 j
  · simpa only [Fin.val_mk] using row_97 j
  · simpa only [Fin.val_mk] using row_98 j
  · simpa only [Fin.val_mk] using row_99 j
  · simpa only [Fin.val_mk] using row_100 j
  · simpa only [Fin.val_mk] using row_101 j
  · simpa only [Fin.val_mk] using row_102 j
  · simpa only [Fin.val_mk] using row_103 j
  · simpa only [Fin.val_mk] using row_104 j
  · simpa only [Fin.val_mk] using row_105 j
  · simpa only [Fin.val_mk] using row_106 j
  · simpa only [Fin.val_mk] using row_107 j
  · simpa only [Fin.val_mk] using row_108 j
  · simpa only [Fin.val_mk] using row_109 j
  · simpa only [Fin.val_mk] using row_110 j
  · simpa only [Fin.val_mk] using row_111 j
  · simpa only [Fin.val_mk] using row_112 j
  · simpa only [Fin.val_mk] using row_113 j
  · simpa only [Fin.val_mk] using row_114 j
  · simpa only [Fin.val_mk] using row_115 j
  · simpa only [Fin.val_mk] using row_116 j
  · simpa only [Fin.val_mk] using row_117 j
  · simpa only [Fin.val_mk] using row_118 j
  · simpa only [Fin.val_mk] using row_119 j
  · simpa only [Fin.val_mk] using row_120 j
  · simpa only [Fin.val_mk] using row_121 j
  · simpa only [Fin.val_mk] using row_122 j
  · simpa only [Fin.val_mk] using row_123 j
  · simpa only [Fin.val_mk] using row_124 j
  · simpa only [Fin.val_mk] using row_125 j
  · simpa only [Fin.val_mk] using row_126 j
  · simpa only [Fin.val_mk] using row_127 j
  · simpa only [Fin.val_mk] using row_128 j
  · simpa only [Fin.val_mk] using row_129 j
  · simpa only [Fin.val_mk] using row_130 j
  · simpa only [Fin.val_mk] using row_131 j
  · simpa only [Fin.val_mk] using row_132 j
  · simpa only [Fin.val_mk] using row_133 j
  · simpa only [Fin.val_mk] using row_134 j
  · simpa only [Fin.val_mk] using row_135 j
  · simpa only [Fin.val_mk] using row_136 j
  · simpa only [Fin.val_mk] using row_137 j
  · simpa only [Fin.val_mk] using row_138 j
  · simpa only [Fin.val_mk] using row_139 j
  · simpa only [Fin.val_mk] using row_140 j
  · simpa only [Fin.val_mk] using row_141 j
  · simpa only [Fin.val_mk] using row_142 j
  · simpa only [Fin.val_mk] using row_143 j
  · simpa only [Fin.val_mk] using row_144 j
  · simpa only [Fin.val_mk] using row_145 j
  · simpa only [Fin.val_mk] using row_146 j
  · simpa only [Fin.val_mk] using row_147 j
  · simpa only [Fin.val_mk] using row_148 j
  · simpa only [Fin.val_mk] using row_149 j
  · simpa only [Fin.val_mk] using row_150 j
  · simpa only [Fin.val_mk] using row_151 j
  · simpa only [Fin.val_mk] using row_152 j
  · simpa only [Fin.val_mk] using row_153 j

theorem binding (i j : Fin 154) :
    rawDigit CFSG.Models.MatrixGroups.ON.rows1 i.val j.val=
      packedDigit 2 (firstRowCode i.val) j.val :=
  CFSGONCachedColumnRowVectorBinding.first_row_binding firstRowCode transpose i j

end SymmetricSubgroupAsymptotics.CFSGONPrimeElevenFirstTransposeRows
