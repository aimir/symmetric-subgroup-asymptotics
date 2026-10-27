import SymmetricSubgroupAsymptotics.CFSGThPrimeNineteenPackedData
import Mathlib.Tactic.FinCases

/-! One original matrix:248 independent row commands; row0 reuses checked pilot. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGThPrimeNineteenFirstRows
open MatrixNaturalRowDotReflection CFSGThPrimeNineteenPackedData

private theorem row_0 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 0 j.val=
      packedDigit 2 (firstRowCode 0) j.val := by
  rw [first_row_zero_code]
  exact CFSGThSelectedPrimeNineteenRowZeroPilot.first_row_binding

private theorem row_1 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 1 j.val=
      packedDigit 2 (firstRowCode 1) j.val := by
  decide +kernel

private theorem row_2 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 2 j.val=
      packedDigit 2 (firstRowCode 2) j.val := by
  decide +kernel

private theorem row_3 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 3 j.val=
      packedDigit 2 (firstRowCode 3) j.val := by
  decide +kernel

private theorem row_4 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 4 j.val=
      packedDigit 2 (firstRowCode 4) j.val := by
  decide +kernel

private theorem row_5 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 5 j.val=
      packedDigit 2 (firstRowCode 5) j.val := by
  decide +kernel

private theorem row_6 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 6 j.val=
      packedDigit 2 (firstRowCode 6) j.val := by
  decide +kernel

private theorem row_7 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 7 j.val=
      packedDigit 2 (firstRowCode 7) j.val := by
  decide +kernel

private theorem row_8 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 8 j.val=
      packedDigit 2 (firstRowCode 8) j.val := by
  decide +kernel

private theorem row_9 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 9 j.val=
      packedDigit 2 (firstRowCode 9) j.val := by
  decide +kernel

private theorem row_10 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 10 j.val=
      packedDigit 2 (firstRowCode 10) j.val := by
  decide +kernel

private theorem row_11 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 11 j.val=
      packedDigit 2 (firstRowCode 11) j.val := by
  decide +kernel

private theorem row_12 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 12 j.val=
      packedDigit 2 (firstRowCode 12) j.val := by
  decide +kernel

private theorem row_13 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 13 j.val=
      packedDigit 2 (firstRowCode 13) j.val := by
  decide +kernel

private theorem row_14 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 14 j.val=
      packedDigit 2 (firstRowCode 14) j.val := by
  decide +kernel

private theorem row_15 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 15 j.val=
      packedDigit 2 (firstRowCode 15) j.val := by
  decide +kernel

private theorem row_16 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 16 j.val=
      packedDigit 2 (firstRowCode 16) j.val := by
  decide +kernel

private theorem row_17 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 17 j.val=
      packedDigit 2 (firstRowCode 17) j.val := by
  decide +kernel

private theorem row_18 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 18 j.val=
      packedDigit 2 (firstRowCode 18) j.val := by
  decide +kernel

private theorem row_19 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 19 j.val=
      packedDigit 2 (firstRowCode 19) j.val := by
  decide +kernel

private theorem row_20 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 20 j.val=
      packedDigit 2 (firstRowCode 20) j.val := by
  decide +kernel

private theorem row_21 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 21 j.val=
      packedDigit 2 (firstRowCode 21) j.val := by
  decide +kernel

private theorem row_22 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 22 j.val=
      packedDigit 2 (firstRowCode 22) j.val := by
  decide +kernel

private theorem row_23 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 23 j.val=
      packedDigit 2 (firstRowCode 23) j.val := by
  decide +kernel

private theorem row_24 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 24 j.val=
      packedDigit 2 (firstRowCode 24) j.val := by
  decide +kernel

private theorem row_25 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 25 j.val=
      packedDigit 2 (firstRowCode 25) j.val := by
  decide +kernel

private theorem row_26 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 26 j.val=
      packedDigit 2 (firstRowCode 26) j.val := by
  decide +kernel

private theorem row_27 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 27 j.val=
      packedDigit 2 (firstRowCode 27) j.val := by
  decide +kernel

private theorem row_28 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 28 j.val=
      packedDigit 2 (firstRowCode 28) j.val := by
  decide +kernel

private theorem row_29 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 29 j.val=
      packedDigit 2 (firstRowCode 29) j.val := by
  decide +kernel

private theorem row_30 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 30 j.val=
      packedDigit 2 (firstRowCode 30) j.val := by
  decide +kernel

private theorem row_31 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 31 j.val=
      packedDigit 2 (firstRowCode 31) j.val := by
  decide +kernel

private theorem row_32 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 32 j.val=
      packedDigit 2 (firstRowCode 32) j.val := by
  decide +kernel

private theorem row_33 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 33 j.val=
      packedDigit 2 (firstRowCode 33) j.val := by
  decide +kernel

private theorem row_34 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 34 j.val=
      packedDigit 2 (firstRowCode 34) j.val := by
  decide +kernel

private theorem row_35 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 35 j.val=
      packedDigit 2 (firstRowCode 35) j.val := by
  decide +kernel

private theorem row_36 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 36 j.val=
      packedDigit 2 (firstRowCode 36) j.val := by
  decide +kernel

private theorem row_37 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 37 j.val=
      packedDigit 2 (firstRowCode 37) j.val := by
  decide +kernel

private theorem row_38 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 38 j.val=
      packedDigit 2 (firstRowCode 38) j.val := by
  decide +kernel

private theorem row_39 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 39 j.val=
      packedDigit 2 (firstRowCode 39) j.val := by
  decide +kernel

private theorem row_40 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 40 j.val=
      packedDigit 2 (firstRowCode 40) j.val := by
  decide +kernel

private theorem row_41 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 41 j.val=
      packedDigit 2 (firstRowCode 41) j.val := by
  decide +kernel

private theorem row_42 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 42 j.val=
      packedDigit 2 (firstRowCode 42) j.val := by
  decide +kernel

private theorem row_43 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 43 j.val=
      packedDigit 2 (firstRowCode 43) j.val := by
  decide +kernel

private theorem row_44 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 44 j.val=
      packedDigit 2 (firstRowCode 44) j.val := by
  decide +kernel

private theorem row_45 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 45 j.val=
      packedDigit 2 (firstRowCode 45) j.val := by
  decide +kernel

private theorem row_46 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 46 j.val=
      packedDigit 2 (firstRowCode 46) j.val := by
  decide +kernel

private theorem row_47 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 47 j.val=
      packedDigit 2 (firstRowCode 47) j.val := by
  decide +kernel

private theorem row_48 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 48 j.val=
      packedDigit 2 (firstRowCode 48) j.val := by
  decide +kernel

private theorem row_49 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 49 j.val=
      packedDigit 2 (firstRowCode 49) j.val := by
  decide +kernel

private theorem row_50 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 50 j.val=
      packedDigit 2 (firstRowCode 50) j.val := by
  decide +kernel

private theorem row_51 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 51 j.val=
      packedDigit 2 (firstRowCode 51) j.val := by
  decide +kernel

private theorem row_52 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 52 j.val=
      packedDigit 2 (firstRowCode 52) j.val := by
  decide +kernel

private theorem row_53 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 53 j.val=
      packedDigit 2 (firstRowCode 53) j.val := by
  decide +kernel

private theorem row_54 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 54 j.val=
      packedDigit 2 (firstRowCode 54) j.val := by
  decide +kernel

private theorem row_55 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 55 j.val=
      packedDigit 2 (firstRowCode 55) j.val := by
  decide +kernel

private theorem row_56 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 56 j.val=
      packedDigit 2 (firstRowCode 56) j.val := by
  decide +kernel

private theorem row_57 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 57 j.val=
      packedDigit 2 (firstRowCode 57) j.val := by
  decide +kernel

private theorem row_58 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 58 j.val=
      packedDigit 2 (firstRowCode 58) j.val := by
  decide +kernel

private theorem row_59 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 59 j.val=
      packedDigit 2 (firstRowCode 59) j.val := by
  decide +kernel

private theorem row_60 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 60 j.val=
      packedDigit 2 (firstRowCode 60) j.val := by
  decide +kernel

private theorem row_61 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 61 j.val=
      packedDigit 2 (firstRowCode 61) j.val := by
  decide +kernel

private theorem row_62 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 62 j.val=
      packedDigit 2 (firstRowCode 62) j.val := by
  decide +kernel

private theorem row_63 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 63 j.val=
      packedDigit 2 (firstRowCode 63) j.val := by
  decide +kernel

private theorem row_64 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 64 j.val=
      packedDigit 2 (firstRowCode 64) j.val := by
  decide +kernel

private theorem row_65 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 65 j.val=
      packedDigit 2 (firstRowCode 65) j.val := by
  decide +kernel

private theorem row_66 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 66 j.val=
      packedDigit 2 (firstRowCode 66) j.val := by
  decide +kernel

private theorem row_67 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 67 j.val=
      packedDigit 2 (firstRowCode 67) j.val := by
  decide +kernel

private theorem row_68 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 68 j.val=
      packedDigit 2 (firstRowCode 68) j.val := by
  decide +kernel

private theorem row_69 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 69 j.val=
      packedDigit 2 (firstRowCode 69) j.val := by
  decide +kernel

private theorem row_70 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 70 j.val=
      packedDigit 2 (firstRowCode 70) j.val := by
  decide +kernel

private theorem row_71 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 71 j.val=
      packedDigit 2 (firstRowCode 71) j.val := by
  decide +kernel

private theorem row_72 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 72 j.val=
      packedDigit 2 (firstRowCode 72) j.val := by
  decide +kernel

private theorem row_73 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 73 j.val=
      packedDigit 2 (firstRowCode 73) j.val := by
  decide +kernel

private theorem row_74 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 74 j.val=
      packedDigit 2 (firstRowCode 74) j.val := by
  decide +kernel

private theorem row_75 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 75 j.val=
      packedDigit 2 (firstRowCode 75) j.val := by
  decide +kernel

private theorem row_76 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 76 j.val=
      packedDigit 2 (firstRowCode 76) j.val := by
  decide +kernel

private theorem row_77 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 77 j.val=
      packedDigit 2 (firstRowCode 77) j.val := by
  decide +kernel

private theorem row_78 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 78 j.val=
      packedDigit 2 (firstRowCode 78) j.val := by
  decide +kernel

private theorem row_79 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 79 j.val=
      packedDigit 2 (firstRowCode 79) j.val := by
  decide +kernel

private theorem row_80 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 80 j.val=
      packedDigit 2 (firstRowCode 80) j.val := by
  decide +kernel

private theorem row_81 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 81 j.val=
      packedDigit 2 (firstRowCode 81) j.val := by
  decide +kernel

private theorem row_82 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 82 j.val=
      packedDigit 2 (firstRowCode 82) j.val := by
  decide +kernel

private theorem row_83 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 83 j.val=
      packedDigit 2 (firstRowCode 83) j.val := by
  decide +kernel

private theorem row_84 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 84 j.val=
      packedDigit 2 (firstRowCode 84) j.val := by
  decide +kernel

private theorem row_85 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 85 j.val=
      packedDigit 2 (firstRowCode 85) j.val := by
  decide +kernel

private theorem row_86 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 86 j.val=
      packedDigit 2 (firstRowCode 86) j.val := by
  decide +kernel

private theorem row_87 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 87 j.val=
      packedDigit 2 (firstRowCode 87) j.val := by
  decide +kernel

private theorem row_88 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 88 j.val=
      packedDigit 2 (firstRowCode 88) j.val := by
  decide +kernel

private theorem row_89 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 89 j.val=
      packedDigit 2 (firstRowCode 89) j.val := by
  decide +kernel

private theorem row_90 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 90 j.val=
      packedDigit 2 (firstRowCode 90) j.val := by
  decide +kernel

private theorem row_91 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 91 j.val=
      packedDigit 2 (firstRowCode 91) j.val := by
  decide +kernel

private theorem row_92 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 92 j.val=
      packedDigit 2 (firstRowCode 92) j.val := by
  decide +kernel

private theorem row_93 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 93 j.val=
      packedDigit 2 (firstRowCode 93) j.val := by
  decide +kernel

private theorem row_94 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 94 j.val=
      packedDigit 2 (firstRowCode 94) j.val := by
  decide +kernel

private theorem row_95 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 95 j.val=
      packedDigit 2 (firstRowCode 95) j.val := by
  decide +kernel

private theorem row_96 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 96 j.val=
      packedDigit 2 (firstRowCode 96) j.val := by
  decide +kernel

private theorem row_97 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 97 j.val=
      packedDigit 2 (firstRowCode 97) j.val := by
  decide +kernel

private theorem row_98 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 98 j.val=
      packedDigit 2 (firstRowCode 98) j.val := by
  decide +kernel

private theorem row_99 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 99 j.val=
      packedDigit 2 (firstRowCode 99) j.val := by
  decide +kernel

private theorem row_100 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 100 j.val=
      packedDigit 2 (firstRowCode 100) j.val := by
  decide +kernel

private theorem row_101 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 101 j.val=
      packedDigit 2 (firstRowCode 101) j.val := by
  decide +kernel

private theorem row_102 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 102 j.val=
      packedDigit 2 (firstRowCode 102) j.val := by
  decide +kernel

private theorem row_103 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 103 j.val=
      packedDigit 2 (firstRowCode 103) j.val := by
  decide +kernel

private theorem row_104 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 104 j.val=
      packedDigit 2 (firstRowCode 104) j.val := by
  decide +kernel

private theorem row_105 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 105 j.val=
      packedDigit 2 (firstRowCode 105) j.val := by
  decide +kernel

private theorem row_106 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 106 j.val=
      packedDigit 2 (firstRowCode 106) j.val := by
  decide +kernel

private theorem row_107 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 107 j.val=
      packedDigit 2 (firstRowCode 107) j.val := by
  decide +kernel

private theorem row_108 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 108 j.val=
      packedDigit 2 (firstRowCode 108) j.val := by
  decide +kernel

private theorem row_109 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 109 j.val=
      packedDigit 2 (firstRowCode 109) j.val := by
  decide +kernel

private theorem row_110 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 110 j.val=
      packedDigit 2 (firstRowCode 110) j.val := by
  decide +kernel

private theorem row_111 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 111 j.val=
      packedDigit 2 (firstRowCode 111) j.val := by
  decide +kernel

private theorem row_112 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 112 j.val=
      packedDigit 2 (firstRowCode 112) j.val := by
  decide +kernel

private theorem row_113 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 113 j.val=
      packedDigit 2 (firstRowCode 113) j.val := by
  decide +kernel

private theorem row_114 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 114 j.val=
      packedDigit 2 (firstRowCode 114) j.val := by
  decide +kernel

private theorem row_115 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 115 j.val=
      packedDigit 2 (firstRowCode 115) j.val := by
  decide +kernel

private theorem row_116 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 116 j.val=
      packedDigit 2 (firstRowCode 116) j.val := by
  decide +kernel

private theorem row_117 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 117 j.val=
      packedDigit 2 (firstRowCode 117) j.val := by
  decide +kernel

private theorem row_118 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 118 j.val=
      packedDigit 2 (firstRowCode 118) j.val := by
  decide +kernel

private theorem row_119 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 119 j.val=
      packedDigit 2 (firstRowCode 119) j.val := by
  decide +kernel

private theorem row_120 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 120 j.val=
      packedDigit 2 (firstRowCode 120) j.val := by
  decide +kernel

private theorem row_121 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 121 j.val=
      packedDigit 2 (firstRowCode 121) j.val := by
  decide +kernel

private theorem row_122 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 122 j.val=
      packedDigit 2 (firstRowCode 122) j.val := by
  decide +kernel

private theorem row_123 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 123 j.val=
      packedDigit 2 (firstRowCode 123) j.val := by
  decide +kernel

private theorem row_124 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 124 j.val=
      packedDigit 2 (firstRowCode 124) j.val := by
  decide +kernel

private theorem row_125 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 125 j.val=
      packedDigit 2 (firstRowCode 125) j.val := by
  decide +kernel

private theorem row_126 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 126 j.val=
      packedDigit 2 (firstRowCode 126) j.val := by
  decide +kernel

private theorem row_127 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 127 j.val=
      packedDigit 2 (firstRowCode 127) j.val := by
  decide +kernel

private theorem row_128 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 128 j.val=
      packedDigit 2 (firstRowCode 128) j.val := by
  decide +kernel

private theorem row_129 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 129 j.val=
      packedDigit 2 (firstRowCode 129) j.val := by
  decide +kernel

private theorem row_130 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 130 j.val=
      packedDigit 2 (firstRowCode 130) j.val := by
  decide +kernel

private theorem row_131 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 131 j.val=
      packedDigit 2 (firstRowCode 131) j.val := by
  decide +kernel

private theorem row_132 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 132 j.val=
      packedDigit 2 (firstRowCode 132) j.val := by
  decide +kernel

private theorem row_133 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 133 j.val=
      packedDigit 2 (firstRowCode 133) j.val := by
  decide +kernel

private theorem row_134 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 134 j.val=
      packedDigit 2 (firstRowCode 134) j.val := by
  decide +kernel

private theorem row_135 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 135 j.val=
      packedDigit 2 (firstRowCode 135) j.val := by
  decide +kernel

private theorem row_136 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 136 j.val=
      packedDigit 2 (firstRowCode 136) j.val := by
  decide +kernel

private theorem row_137 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 137 j.val=
      packedDigit 2 (firstRowCode 137) j.val := by
  decide +kernel

private theorem row_138 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 138 j.val=
      packedDigit 2 (firstRowCode 138) j.val := by
  decide +kernel

private theorem row_139 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 139 j.val=
      packedDigit 2 (firstRowCode 139) j.val := by
  decide +kernel

private theorem row_140 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 140 j.val=
      packedDigit 2 (firstRowCode 140) j.val := by
  decide +kernel

private theorem row_141 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 141 j.val=
      packedDigit 2 (firstRowCode 141) j.val := by
  decide +kernel

private theorem row_142 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 142 j.val=
      packedDigit 2 (firstRowCode 142) j.val := by
  decide +kernel

private theorem row_143 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 143 j.val=
      packedDigit 2 (firstRowCode 143) j.val := by
  decide +kernel

private theorem row_144 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 144 j.val=
      packedDigit 2 (firstRowCode 144) j.val := by
  decide +kernel

private theorem row_145 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 145 j.val=
      packedDigit 2 (firstRowCode 145) j.val := by
  decide +kernel

private theorem row_146 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 146 j.val=
      packedDigit 2 (firstRowCode 146) j.val := by
  decide +kernel

private theorem row_147 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 147 j.val=
      packedDigit 2 (firstRowCode 147) j.val := by
  decide +kernel

private theorem row_148 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 148 j.val=
      packedDigit 2 (firstRowCode 148) j.val := by
  decide +kernel

private theorem row_149 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 149 j.val=
      packedDigit 2 (firstRowCode 149) j.val := by
  decide +kernel

private theorem row_150 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 150 j.val=
      packedDigit 2 (firstRowCode 150) j.val := by
  decide +kernel

private theorem row_151 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 151 j.val=
      packedDigit 2 (firstRowCode 151) j.val := by
  decide +kernel

private theorem row_152 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 152 j.val=
      packedDigit 2 (firstRowCode 152) j.val := by
  decide +kernel

private theorem row_153 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 153 j.val=
      packedDigit 2 (firstRowCode 153) j.val := by
  decide +kernel

private theorem row_154 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 154 j.val=
      packedDigit 2 (firstRowCode 154) j.val := by
  decide +kernel

private theorem row_155 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 155 j.val=
      packedDigit 2 (firstRowCode 155) j.val := by
  decide +kernel

private theorem row_156 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 156 j.val=
      packedDigit 2 (firstRowCode 156) j.val := by
  decide +kernel

private theorem row_157 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 157 j.val=
      packedDigit 2 (firstRowCode 157) j.val := by
  decide +kernel

private theorem row_158 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 158 j.val=
      packedDigit 2 (firstRowCode 158) j.val := by
  decide +kernel

private theorem row_159 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 159 j.val=
      packedDigit 2 (firstRowCode 159) j.val := by
  decide +kernel

private theorem row_160 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 160 j.val=
      packedDigit 2 (firstRowCode 160) j.val := by
  decide +kernel

private theorem row_161 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 161 j.val=
      packedDigit 2 (firstRowCode 161) j.val := by
  decide +kernel

private theorem row_162 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 162 j.val=
      packedDigit 2 (firstRowCode 162) j.val := by
  decide +kernel

private theorem row_163 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 163 j.val=
      packedDigit 2 (firstRowCode 163) j.val := by
  decide +kernel

private theorem row_164 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 164 j.val=
      packedDigit 2 (firstRowCode 164) j.val := by
  decide +kernel

private theorem row_165 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 165 j.val=
      packedDigit 2 (firstRowCode 165) j.val := by
  decide +kernel

private theorem row_166 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 166 j.val=
      packedDigit 2 (firstRowCode 166) j.val := by
  decide +kernel

private theorem row_167 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 167 j.val=
      packedDigit 2 (firstRowCode 167) j.val := by
  decide +kernel

private theorem row_168 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 168 j.val=
      packedDigit 2 (firstRowCode 168) j.val := by
  decide +kernel

private theorem row_169 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 169 j.val=
      packedDigit 2 (firstRowCode 169) j.val := by
  decide +kernel

private theorem row_170 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 170 j.val=
      packedDigit 2 (firstRowCode 170) j.val := by
  decide +kernel

private theorem row_171 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 171 j.val=
      packedDigit 2 (firstRowCode 171) j.val := by
  decide +kernel

private theorem row_172 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 172 j.val=
      packedDigit 2 (firstRowCode 172) j.val := by
  decide +kernel

private theorem row_173 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 173 j.val=
      packedDigit 2 (firstRowCode 173) j.val := by
  decide +kernel

private theorem row_174 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 174 j.val=
      packedDigit 2 (firstRowCode 174) j.val := by
  decide +kernel

private theorem row_175 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 175 j.val=
      packedDigit 2 (firstRowCode 175) j.val := by
  decide +kernel

private theorem row_176 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 176 j.val=
      packedDigit 2 (firstRowCode 176) j.val := by
  decide +kernel

private theorem row_177 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 177 j.val=
      packedDigit 2 (firstRowCode 177) j.val := by
  decide +kernel

private theorem row_178 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 178 j.val=
      packedDigit 2 (firstRowCode 178) j.val := by
  decide +kernel

private theorem row_179 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 179 j.val=
      packedDigit 2 (firstRowCode 179) j.val := by
  decide +kernel

private theorem row_180 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 180 j.val=
      packedDigit 2 (firstRowCode 180) j.val := by
  decide +kernel

private theorem row_181 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 181 j.val=
      packedDigit 2 (firstRowCode 181) j.val := by
  decide +kernel

private theorem row_182 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 182 j.val=
      packedDigit 2 (firstRowCode 182) j.val := by
  decide +kernel

private theorem row_183 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 183 j.val=
      packedDigit 2 (firstRowCode 183) j.val := by
  decide +kernel

private theorem row_184 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 184 j.val=
      packedDigit 2 (firstRowCode 184) j.val := by
  decide +kernel

private theorem row_185 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 185 j.val=
      packedDigit 2 (firstRowCode 185) j.val := by
  decide +kernel

private theorem row_186 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 186 j.val=
      packedDigit 2 (firstRowCode 186) j.val := by
  decide +kernel

private theorem row_187 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 187 j.val=
      packedDigit 2 (firstRowCode 187) j.val := by
  decide +kernel

private theorem row_188 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 188 j.val=
      packedDigit 2 (firstRowCode 188) j.val := by
  decide +kernel

private theorem row_189 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 189 j.val=
      packedDigit 2 (firstRowCode 189) j.val := by
  decide +kernel

private theorem row_190 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 190 j.val=
      packedDigit 2 (firstRowCode 190) j.val := by
  decide +kernel

private theorem row_191 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 191 j.val=
      packedDigit 2 (firstRowCode 191) j.val := by
  decide +kernel

private theorem row_192 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 192 j.val=
      packedDigit 2 (firstRowCode 192) j.val := by
  decide +kernel

private theorem row_193 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 193 j.val=
      packedDigit 2 (firstRowCode 193) j.val := by
  decide +kernel

private theorem row_194 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 194 j.val=
      packedDigit 2 (firstRowCode 194) j.val := by
  decide +kernel

private theorem row_195 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 195 j.val=
      packedDigit 2 (firstRowCode 195) j.val := by
  decide +kernel

private theorem row_196 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 196 j.val=
      packedDigit 2 (firstRowCode 196) j.val := by
  decide +kernel

private theorem row_197 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 197 j.val=
      packedDigit 2 (firstRowCode 197) j.val := by
  decide +kernel

private theorem row_198 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 198 j.val=
      packedDigit 2 (firstRowCode 198) j.val := by
  decide +kernel

private theorem row_199 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 199 j.val=
      packedDigit 2 (firstRowCode 199) j.val := by
  decide +kernel

private theorem row_200 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 200 j.val=
      packedDigit 2 (firstRowCode 200) j.val := by
  decide +kernel

private theorem row_201 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 201 j.val=
      packedDigit 2 (firstRowCode 201) j.val := by
  decide +kernel

private theorem row_202 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 202 j.val=
      packedDigit 2 (firstRowCode 202) j.val := by
  decide +kernel

private theorem row_203 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 203 j.val=
      packedDigit 2 (firstRowCode 203) j.val := by
  decide +kernel

private theorem row_204 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 204 j.val=
      packedDigit 2 (firstRowCode 204) j.val := by
  decide +kernel

private theorem row_205 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 205 j.val=
      packedDigit 2 (firstRowCode 205) j.val := by
  decide +kernel

private theorem row_206 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 206 j.val=
      packedDigit 2 (firstRowCode 206) j.val := by
  decide +kernel

private theorem row_207 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 207 j.val=
      packedDigit 2 (firstRowCode 207) j.val := by
  decide +kernel

private theorem row_208 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 208 j.val=
      packedDigit 2 (firstRowCode 208) j.val := by
  decide +kernel

private theorem row_209 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 209 j.val=
      packedDigit 2 (firstRowCode 209) j.val := by
  decide +kernel

private theorem row_210 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 210 j.val=
      packedDigit 2 (firstRowCode 210) j.val := by
  decide +kernel

private theorem row_211 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 211 j.val=
      packedDigit 2 (firstRowCode 211) j.val := by
  decide +kernel

private theorem row_212 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 212 j.val=
      packedDigit 2 (firstRowCode 212) j.val := by
  decide +kernel

private theorem row_213 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 213 j.val=
      packedDigit 2 (firstRowCode 213) j.val := by
  decide +kernel

private theorem row_214 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 214 j.val=
      packedDigit 2 (firstRowCode 214) j.val := by
  decide +kernel

private theorem row_215 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 215 j.val=
      packedDigit 2 (firstRowCode 215) j.val := by
  decide +kernel

private theorem row_216 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 216 j.val=
      packedDigit 2 (firstRowCode 216) j.val := by
  decide +kernel

private theorem row_217 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 217 j.val=
      packedDigit 2 (firstRowCode 217) j.val := by
  decide +kernel

private theorem row_218 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 218 j.val=
      packedDigit 2 (firstRowCode 218) j.val := by
  decide +kernel

private theorem row_219 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 219 j.val=
      packedDigit 2 (firstRowCode 219) j.val := by
  decide +kernel

private theorem row_220 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 220 j.val=
      packedDigit 2 (firstRowCode 220) j.val := by
  decide +kernel

private theorem row_221 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 221 j.val=
      packedDigit 2 (firstRowCode 221) j.val := by
  decide +kernel

private theorem row_222 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 222 j.val=
      packedDigit 2 (firstRowCode 222) j.val := by
  decide +kernel

private theorem row_223 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 223 j.val=
      packedDigit 2 (firstRowCode 223) j.val := by
  decide +kernel

private theorem row_224 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 224 j.val=
      packedDigit 2 (firstRowCode 224) j.val := by
  decide +kernel

private theorem row_225 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 225 j.val=
      packedDigit 2 (firstRowCode 225) j.val := by
  decide +kernel

private theorem row_226 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 226 j.val=
      packedDigit 2 (firstRowCode 226) j.val := by
  decide +kernel

private theorem row_227 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 227 j.val=
      packedDigit 2 (firstRowCode 227) j.val := by
  decide +kernel

private theorem row_228 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 228 j.val=
      packedDigit 2 (firstRowCode 228) j.val := by
  decide +kernel

private theorem row_229 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 229 j.val=
      packedDigit 2 (firstRowCode 229) j.val := by
  decide +kernel

private theorem row_230 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 230 j.val=
      packedDigit 2 (firstRowCode 230) j.val := by
  decide +kernel

private theorem row_231 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 231 j.val=
      packedDigit 2 (firstRowCode 231) j.val := by
  decide +kernel

private theorem row_232 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 232 j.val=
      packedDigit 2 (firstRowCode 232) j.val := by
  decide +kernel

private theorem row_233 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 233 j.val=
      packedDigit 2 (firstRowCode 233) j.val := by
  decide +kernel

private theorem row_234 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 234 j.val=
      packedDigit 2 (firstRowCode 234) j.val := by
  decide +kernel

private theorem row_235 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 235 j.val=
      packedDigit 2 (firstRowCode 235) j.val := by
  decide +kernel

private theorem row_236 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 236 j.val=
      packedDigit 2 (firstRowCode 236) j.val := by
  decide +kernel

private theorem row_237 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 237 j.val=
      packedDigit 2 (firstRowCode 237) j.val := by
  decide +kernel

private theorem row_238 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 238 j.val=
      packedDigit 2 (firstRowCode 238) j.val := by
  decide +kernel

private theorem row_239 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 239 j.val=
      packedDigit 2 (firstRowCode 239) j.val := by
  decide +kernel

private theorem row_240 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 240 j.val=
      packedDigit 2 (firstRowCode 240) j.val := by
  decide +kernel

private theorem row_241 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 241 j.val=
      packedDigit 2 (firstRowCode 241) j.val := by
  decide +kernel

private theorem row_242 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 242 j.val=
      packedDigit 2 (firstRowCode 242) j.val := by
  decide +kernel

private theorem row_243 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 243 j.val=
      packedDigit 2 (firstRowCode 243) j.val := by
  decide +kernel

private theorem row_244 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 244 j.val=
      packedDigit 2 (firstRowCode 244) j.val := by
  decide +kernel

private theorem row_245 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 245 j.val=
      packedDigit 2 (firstRowCode 245) j.val := by
  decide +kernel

private theorem row_246 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 246 j.val=
      packedDigit 2 (firstRowCode 246) j.val := by
  decide +kernel

private theorem row_247 : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 247 j.val=
      packedDigit 2 (firstRowCode 247) j.val := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem binding (i j : Fin 248) :
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 i.val j.val=
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
  · simpa only [Fin.val_mk] using row_154 j
  · simpa only [Fin.val_mk] using row_155 j
  · simpa only [Fin.val_mk] using row_156 j
  · simpa only [Fin.val_mk] using row_157 j
  · simpa only [Fin.val_mk] using row_158 j
  · simpa only [Fin.val_mk] using row_159 j
  · simpa only [Fin.val_mk] using row_160 j
  · simpa only [Fin.val_mk] using row_161 j
  · simpa only [Fin.val_mk] using row_162 j
  · simpa only [Fin.val_mk] using row_163 j
  · simpa only [Fin.val_mk] using row_164 j
  · simpa only [Fin.val_mk] using row_165 j
  · simpa only [Fin.val_mk] using row_166 j
  · simpa only [Fin.val_mk] using row_167 j
  · simpa only [Fin.val_mk] using row_168 j
  · simpa only [Fin.val_mk] using row_169 j
  · simpa only [Fin.val_mk] using row_170 j
  · simpa only [Fin.val_mk] using row_171 j
  · simpa only [Fin.val_mk] using row_172 j
  · simpa only [Fin.val_mk] using row_173 j
  · simpa only [Fin.val_mk] using row_174 j
  · simpa only [Fin.val_mk] using row_175 j
  · simpa only [Fin.val_mk] using row_176 j
  · simpa only [Fin.val_mk] using row_177 j
  · simpa only [Fin.val_mk] using row_178 j
  · simpa only [Fin.val_mk] using row_179 j
  · simpa only [Fin.val_mk] using row_180 j
  · simpa only [Fin.val_mk] using row_181 j
  · simpa only [Fin.val_mk] using row_182 j
  · simpa only [Fin.val_mk] using row_183 j
  · simpa only [Fin.val_mk] using row_184 j
  · simpa only [Fin.val_mk] using row_185 j
  · simpa only [Fin.val_mk] using row_186 j
  · simpa only [Fin.val_mk] using row_187 j
  · simpa only [Fin.val_mk] using row_188 j
  · simpa only [Fin.val_mk] using row_189 j
  · simpa only [Fin.val_mk] using row_190 j
  · simpa only [Fin.val_mk] using row_191 j
  · simpa only [Fin.val_mk] using row_192 j
  · simpa only [Fin.val_mk] using row_193 j
  · simpa only [Fin.val_mk] using row_194 j
  · simpa only [Fin.val_mk] using row_195 j
  · simpa only [Fin.val_mk] using row_196 j
  · simpa only [Fin.val_mk] using row_197 j
  · simpa only [Fin.val_mk] using row_198 j
  · simpa only [Fin.val_mk] using row_199 j
  · simpa only [Fin.val_mk] using row_200 j
  · simpa only [Fin.val_mk] using row_201 j
  · simpa only [Fin.val_mk] using row_202 j
  · simpa only [Fin.val_mk] using row_203 j
  · simpa only [Fin.val_mk] using row_204 j
  · simpa only [Fin.val_mk] using row_205 j
  · simpa only [Fin.val_mk] using row_206 j
  · simpa only [Fin.val_mk] using row_207 j
  · simpa only [Fin.val_mk] using row_208 j
  · simpa only [Fin.val_mk] using row_209 j
  · simpa only [Fin.val_mk] using row_210 j
  · simpa only [Fin.val_mk] using row_211 j
  · simpa only [Fin.val_mk] using row_212 j
  · simpa only [Fin.val_mk] using row_213 j
  · simpa only [Fin.val_mk] using row_214 j
  · simpa only [Fin.val_mk] using row_215 j
  · simpa only [Fin.val_mk] using row_216 j
  · simpa only [Fin.val_mk] using row_217 j
  · simpa only [Fin.val_mk] using row_218 j
  · simpa only [Fin.val_mk] using row_219 j
  · simpa only [Fin.val_mk] using row_220 j
  · simpa only [Fin.val_mk] using row_221 j
  · simpa only [Fin.val_mk] using row_222 j
  · simpa only [Fin.val_mk] using row_223 j
  · simpa only [Fin.val_mk] using row_224 j
  · simpa only [Fin.val_mk] using row_225 j
  · simpa only [Fin.val_mk] using row_226 j
  · simpa only [Fin.val_mk] using row_227 j
  · simpa only [Fin.val_mk] using row_228 j
  · simpa only [Fin.val_mk] using row_229 j
  · simpa only [Fin.val_mk] using row_230 j
  · simpa only [Fin.val_mk] using row_231 j
  · simpa only [Fin.val_mk] using row_232 j
  · simpa only [Fin.val_mk] using row_233 j
  · simpa only [Fin.val_mk] using row_234 j
  · simpa only [Fin.val_mk] using row_235 j
  · simpa only [Fin.val_mk] using row_236 j
  · simpa only [Fin.val_mk] using row_237 j
  · simpa only [Fin.val_mk] using row_238 j
  · simpa only [Fin.val_mk] using row_239 j
  · simpa only [Fin.val_mk] using row_240 j
  · simpa only [Fin.val_mk] using row_241 j
  · simpa only [Fin.val_mk] using row_242 j
  · simpa only [Fin.val_mk] using row_243 j
  · simpa only [Fin.val_mk] using row_244 j
  · simpa only [Fin.val_mk] using row_245 j
  · simpa only [Fin.val_mk] using row_246 j
  · simpa only [Fin.val_mk] using row_247 j

end SymmetricSubgroupAsymptotics.CFSGThPrimeNineteenFirstRows
