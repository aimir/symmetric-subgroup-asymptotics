import SymmetricSubgroupAsymptotics.CFSGHNPrimeElevenPackedData
import Mathlib.Tactic.FinCases

/-! One original matrix:133 independent row commands; row0 reuses checked pilot. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGHNPrimeElevenFirstRows
open MatrixNaturalRowDotReflection CFSGHNPrimeElevenPackedData

private theorem row_0 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 0 j.val=
      packedDigit 3 (firstRowCode 0) j.val := by
  rw [first_row_zero_code]
  exact CFSGHNSelectedPrimeElevenRowZeroPilot.first_row_binding

private theorem row_1 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 1 j.val=
      packedDigit 3 (firstRowCode 1) j.val := by
  decide +kernel

private theorem row_2 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 2 j.val=
      packedDigit 3 (firstRowCode 2) j.val := by
  decide +kernel

private theorem row_3 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 3 j.val=
      packedDigit 3 (firstRowCode 3) j.val := by
  decide +kernel

private theorem row_4 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 4 j.val=
      packedDigit 3 (firstRowCode 4) j.val := by
  decide +kernel

private theorem row_5 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 5 j.val=
      packedDigit 3 (firstRowCode 5) j.val := by
  decide +kernel

private theorem row_6 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 6 j.val=
      packedDigit 3 (firstRowCode 6) j.val := by
  decide +kernel

private theorem row_7 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 7 j.val=
      packedDigit 3 (firstRowCode 7) j.val := by
  decide +kernel

private theorem row_8 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 8 j.val=
      packedDigit 3 (firstRowCode 8) j.val := by
  decide +kernel

private theorem row_9 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 9 j.val=
      packedDigit 3 (firstRowCode 9) j.val := by
  decide +kernel

private theorem row_10 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 10 j.val=
      packedDigit 3 (firstRowCode 10) j.val := by
  decide +kernel

private theorem row_11 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 11 j.val=
      packedDigit 3 (firstRowCode 11) j.val := by
  decide +kernel

private theorem row_12 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 12 j.val=
      packedDigit 3 (firstRowCode 12) j.val := by
  decide +kernel

private theorem row_13 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 13 j.val=
      packedDigit 3 (firstRowCode 13) j.val := by
  decide +kernel

private theorem row_14 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 14 j.val=
      packedDigit 3 (firstRowCode 14) j.val := by
  decide +kernel

private theorem row_15 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 15 j.val=
      packedDigit 3 (firstRowCode 15) j.val := by
  decide +kernel

private theorem row_16 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 16 j.val=
      packedDigit 3 (firstRowCode 16) j.val := by
  decide +kernel

private theorem row_17 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 17 j.val=
      packedDigit 3 (firstRowCode 17) j.val := by
  decide +kernel

private theorem row_18 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 18 j.val=
      packedDigit 3 (firstRowCode 18) j.val := by
  decide +kernel

private theorem row_19 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 19 j.val=
      packedDigit 3 (firstRowCode 19) j.val := by
  decide +kernel

private theorem row_20 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 20 j.val=
      packedDigit 3 (firstRowCode 20) j.val := by
  decide +kernel

private theorem row_21 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 21 j.val=
      packedDigit 3 (firstRowCode 21) j.val := by
  decide +kernel

private theorem row_22 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 22 j.val=
      packedDigit 3 (firstRowCode 22) j.val := by
  decide +kernel

private theorem row_23 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 23 j.val=
      packedDigit 3 (firstRowCode 23) j.val := by
  decide +kernel

private theorem row_24 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 24 j.val=
      packedDigit 3 (firstRowCode 24) j.val := by
  decide +kernel

private theorem row_25 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 25 j.val=
      packedDigit 3 (firstRowCode 25) j.val := by
  decide +kernel

private theorem row_26 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 26 j.val=
      packedDigit 3 (firstRowCode 26) j.val := by
  decide +kernel

private theorem row_27 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 27 j.val=
      packedDigit 3 (firstRowCode 27) j.val := by
  decide +kernel

private theorem row_28 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 28 j.val=
      packedDigit 3 (firstRowCode 28) j.val := by
  decide +kernel

private theorem row_29 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 29 j.val=
      packedDigit 3 (firstRowCode 29) j.val := by
  decide +kernel

private theorem row_30 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 30 j.val=
      packedDigit 3 (firstRowCode 30) j.val := by
  decide +kernel

private theorem row_31 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 31 j.val=
      packedDigit 3 (firstRowCode 31) j.val := by
  decide +kernel

private theorem row_32 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 32 j.val=
      packedDigit 3 (firstRowCode 32) j.val := by
  decide +kernel

private theorem row_33 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 33 j.val=
      packedDigit 3 (firstRowCode 33) j.val := by
  decide +kernel

private theorem row_34 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 34 j.val=
      packedDigit 3 (firstRowCode 34) j.val := by
  decide +kernel

private theorem row_35 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 35 j.val=
      packedDigit 3 (firstRowCode 35) j.val := by
  decide +kernel

private theorem row_36 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 36 j.val=
      packedDigit 3 (firstRowCode 36) j.val := by
  decide +kernel

private theorem row_37 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 37 j.val=
      packedDigit 3 (firstRowCode 37) j.val := by
  decide +kernel

private theorem row_38 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 38 j.val=
      packedDigit 3 (firstRowCode 38) j.val := by
  decide +kernel

private theorem row_39 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 39 j.val=
      packedDigit 3 (firstRowCode 39) j.val := by
  decide +kernel

private theorem row_40 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 40 j.val=
      packedDigit 3 (firstRowCode 40) j.val := by
  decide +kernel

private theorem row_41 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 41 j.val=
      packedDigit 3 (firstRowCode 41) j.val := by
  decide +kernel

private theorem row_42 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 42 j.val=
      packedDigit 3 (firstRowCode 42) j.val := by
  decide +kernel

private theorem row_43 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 43 j.val=
      packedDigit 3 (firstRowCode 43) j.val := by
  decide +kernel

private theorem row_44 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 44 j.val=
      packedDigit 3 (firstRowCode 44) j.val := by
  decide +kernel

private theorem row_45 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 45 j.val=
      packedDigit 3 (firstRowCode 45) j.val := by
  decide +kernel

private theorem row_46 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 46 j.val=
      packedDigit 3 (firstRowCode 46) j.val := by
  decide +kernel

private theorem row_47 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 47 j.val=
      packedDigit 3 (firstRowCode 47) j.val := by
  decide +kernel

private theorem row_48 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 48 j.val=
      packedDigit 3 (firstRowCode 48) j.val := by
  decide +kernel

private theorem row_49 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 49 j.val=
      packedDigit 3 (firstRowCode 49) j.val := by
  decide +kernel

private theorem row_50 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 50 j.val=
      packedDigit 3 (firstRowCode 50) j.val := by
  decide +kernel

private theorem row_51 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 51 j.val=
      packedDigit 3 (firstRowCode 51) j.val := by
  decide +kernel

private theorem row_52 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 52 j.val=
      packedDigit 3 (firstRowCode 52) j.val := by
  decide +kernel

private theorem row_53 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 53 j.val=
      packedDigit 3 (firstRowCode 53) j.val := by
  decide +kernel

private theorem row_54 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 54 j.val=
      packedDigit 3 (firstRowCode 54) j.val := by
  decide +kernel

private theorem row_55 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 55 j.val=
      packedDigit 3 (firstRowCode 55) j.val := by
  decide +kernel

private theorem row_56 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 56 j.val=
      packedDigit 3 (firstRowCode 56) j.val := by
  decide +kernel

private theorem row_57 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 57 j.val=
      packedDigit 3 (firstRowCode 57) j.val := by
  decide +kernel

private theorem row_58 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 58 j.val=
      packedDigit 3 (firstRowCode 58) j.val := by
  decide +kernel

private theorem row_59 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 59 j.val=
      packedDigit 3 (firstRowCode 59) j.val := by
  decide +kernel

private theorem row_60 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 60 j.val=
      packedDigit 3 (firstRowCode 60) j.val := by
  decide +kernel

private theorem row_61 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 61 j.val=
      packedDigit 3 (firstRowCode 61) j.val := by
  decide +kernel

private theorem row_62 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 62 j.val=
      packedDigit 3 (firstRowCode 62) j.val := by
  decide +kernel

private theorem row_63 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 63 j.val=
      packedDigit 3 (firstRowCode 63) j.val := by
  decide +kernel

private theorem row_64 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 64 j.val=
      packedDigit 3 (firstRowCode 64) j.val := by
  decide +kernel

private theorem row_65 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 65 j.val=
      packedDigit 3 (firstRowCode 65) j.val := by
  decide +kernel

private theorem row_66 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 66 j.val=
      packedDigit 3 (firstRowCode 66) j.val := by
  decide +kernel

private theorem row_67 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 67 j.val=
      packedDigit 3 (firstRowCode 67) j.val := by
  decide +kernel

private theorem row_68 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 68 j.val=
      packedDigit 3 (firstRowCode 68) j.val := by
  decide +kernel

private theorem row_69 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 69 j.val=
      packedDigit 3 (firstRowCode 69) j.val := by
  decide +kernel

private theorem row_70 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 70 j.val=
      packedDigit 3 (firstRowCode 70) j.val := by
  decide +kernel

private theorem row_71 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 71 j.val=
      packedDigit 3 (firstRowCode 71) j.val := by
  decide +kernel

private theorem row_72 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 72 j.val=
      packedDigit 3 (firstRowCode 72) j.val := by
  decide +kernel

private theorem row_73 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 73 j.val=
      packedDigit 3 (firstRowCode 73) j.val := by
  decide +kernel

private theorem row_74 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 74 j.val=
      packedDigit 3 (firstRowCode 74) j.val := by
  decide +kernel

private theorem row_75 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 75 j.val=
      packedDigit 3 (firstRowCode 75) j.val := by
  decide +kernel

private theorem row_76 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 76 j.val=
      packedDigit 3 (firstRowCode 76) j.val := by
  decide +kernel

private theorem row_77 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 77 j.val=
      packedDigit 3 (firstRowCode 77) j.val := by
  decide +kernel

private theorem row_78 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 78 j.val=
      packedDigit 3 (firstRowCode 78) j.val := by
  decide +kernel

private theorem row_79 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 79 j.val=
      packedDigit 3 (firstRowCode 79) j.val := by
  decide +kernel

private theorem row_80 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 80 j.val=
      packedDigit 3 (firstRowCode 80) j.val := by
  decide +kernel

private theorem row_81 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 81 j.val=
      packedDigit 3 (firstRowCode 81) j.val := by
  decide +kernel

private theorem row_82 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 82 j.val=
      packedDigit 3 (firstRowCode 82) j.val := by
  decide +kernel

private theorem row_83 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 83 j.val=
      packedDigit 3 (firstRowCode 83) j.val := by
  decide +kernel

private theorem row_84 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 84 j.val=
      packedDigit 3 (firstRowCode 84) j.val := by
  decide +kernel

private theorem row_85 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 85 j.val=
      packedDigit 3 (firstRowCode 85) j.val := by
  decide +kernel

private theorem row_86 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 86 j.val=
      packedDigit 3 (firstRowCode 86) j.val := by
  decide +kernel

private theorem row_87 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 87 j.val=
      packedDigit 3 (firstRowCode 87) j.val := by
  decide +kernel

private theorem row_88 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 88 j.val=
      packedDigit 3 (firstRowCode 88) j.val := by
  decide +kernel

private theorem row_89 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 89 j.val=
      packedDigit 3 (firstRowCode 89) j.val := by
  decide +kernel

private theorem row_90 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 90 j.val=
      packedDigit 3 (firstRowCode 90) j.val := by
  decide +kernel

private theorem row_91 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 91 j.val=
      packedDigit 3 (firstRowCode 91) j.val := by
  decide +kernel

private theorem row_92 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 92 j.val=
      packedDigit 3 (firstRowCode 92) j.val := by
  decide +kernel

private theorem row_93 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 93 j.val=
      packedDigit 3 (firstRowCode 93) j.val := by
  decide +kernel

private theorem row_94 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 94 j.val=
      packedDigit 3 (firstRowCode 94) j.val := by
  decide +kernel

private theorem row_95 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 95 j.val=
      packedDigit 3 (firstRowCode 95) j.val := by
  decide +kernel

private theorem row_96 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 96 j.val=
      packedDigit 3 (firstRowCode 96) j.val := by
  decide +kernel

private theorem row_97 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 97 j.val=
      packedDigit 3 (firstRowCode 97) j.val := by
  decide +kernel

private theorem row_98 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 98 j.val=
      packedDigit 3 (firstRowCode 98) j.val := by
  decide +kernel

private theorem row_99 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 99 j.val=
      packedDigit 3 (firstRowCode 99) j.val := by
  decide +kernel

private theorem row_100 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 100 j.val=
      packedDigit 3 (firstRowCode 100) j.val := by
  decide +kernel

private theorem row_101 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 101 j.val=
      packedDigit 3 (firstRowCode 101) j.val := by
  decide +kernel

private theorem row_102 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 102 j.val=
      packedDigit 3 (firstRowCode 102) j.val := by
  decide +kernel

private theorem row_103 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 103 j.val=
      packedDigit 3 (firstRowCode 103) j.val := by
  decide +kernel

private theorem row_104 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 104 j.val=
      packedDigit 3 (firstRowCode 104) j.val := by
  decide +kernel

private theorem row_105 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 105 j.val=
      packedDigit 3 (firstRowCode 105) j.val := by
  decide +kernel

private theorem row_106 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 106 j.val=
      packedDigit 3 (firstRowCode 106) j.val := by
  decide +kernel

private theorem row_107 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 107 j.val=
      packedDigit 3 (firstRowCode 107) j.val := by
  decide +kernel

private theorem row_108 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 108 j.val=
      packedDigit 3 (firstRowCode 108) j.val := by
  decide +kernel

private theorem row_109 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 109 j.val=
      packedDigit 3 (firstRowCode 109) j.val := by
  decide +kernel

private theorem row_110 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 110 j.val=
      packedDigit 3 (firstRowCode 110) j.val := by
  decide +kernel

private theorem row_111 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 111 j.val=
      packedDigit 3 (firstRowCode 111) j.val := by
  decide +kernel

private theorem row_112 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 112 j.val=
      packedDigit 3 (firstRowCode 112) j.val := by
  decide +kernel

private theorem row_113 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 113 j.val=
      packedDigit 3 (firstRowCode 113) j.val := by
  decide +kernel

private theorem row_114 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 114 j.val=
      packedDigit 3 (firstRowCode 114) j.val := by
  decide +kernel

private theorem row_115 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 115 j.val=
      packedDigit 3 (firstRowCode 115) j.val := by
  decide +kernel

private theorem row_116 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 116 j.val=
      packedDigit 3 (firstRowCode 116) j.val := by
  decide +kernel

private theorem row_117 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 117 j.val=
      packedDigit 3 (firstRowCode 117) j.val := by
  decide +kernel

private theorem row_118 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 118 j.val=
      packedDigit 3 (firstRowCode 118) j.val := by
  decide +kernel

private theorem row_119 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 119 j.val=
      packedDigit 3 (firstRowCode 119) j.val := by
  decide +kernel

private theorem row_120 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 120 j.val=
      packedDigit 3 (firstRowCode 120) j.val := by
  decide +kernel

private theorem row_121 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 121 j.val=
      packedDigit 3 (firstRowCode 121) j.val := by
  decide +kernel

private theorem row_122 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 122 j.val=
      packedDigit 3 (firstRowCode 122) j.val := by
  decide +kernel

private theorem row_123 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 123 j.val=
      packedDigit 3 (firstRowCode 123) j.val := by
  decide +kernel

private theorem row_124 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 124 j.val=
      packedDigit 3 (firstRowCode 124) j.val := by
  decide +kernel

private theorem row_125 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 125 j.val=
      packedDigit 3 (firstRowCode 125) j.val := by
  decide +kernel

private theorem row_126 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 126 j.val=
      packedDigit 3 (firstRowCode 126) j.val := by
  decide +kernel

private theorem row_127 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 127 j.val=
      packedDigit 3 (firstRowCode 127) j.val := by
  decide +kernel

private theorem row_128 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 128 j.val=
      packedDigit 3 (firstRowCode 128) j.val := by
  decide +kernel

private theorem row_129 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 129 j.val=
      packedDigit 3 (firstRowCode 129) j.val := by
  decide +kernel

private theorem row_130 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 130 j.val=
      packedDigit 3 (firstRowCode 130) j.val := by
  decide +kernel

private theorem row_131 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 131 j.val=
      packedDigit 3 (firstRowCode 131) j.val := by
  decide +kernel

private theorem row_132 : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 132 j.val=
      packedDigit 3 (firstRowCode 132) j.val := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem binding (i j : Fin 133) :
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 i.val j.val=
      packedDigit 3 (firstRowCode i.val) j.val := by
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

end SymmetricSubgroupAsymptotics.CFSGHNPrimeElevenFirstRows
