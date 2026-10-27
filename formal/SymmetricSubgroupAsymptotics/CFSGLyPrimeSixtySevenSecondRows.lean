import SymmetricSubgroupAsymptotics.CFSGLyPrimeSixtySevenPackedData
import Mathlib.Tactic.FinCases

/-! One original matrix:111 independent row commands; row0 reuses checked pilot. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGLyPrimeSixtySevenSecondRows
open MatrixNaturalRowDotReflection CFSGLyPrimeSixtySevenPackedData

private theorem row_0 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 0 j.val=
      packedDigit 3 (secondRowCode 0) j.val := by
  rw [second_row_zero_code]
  exact CFSGLySelectedPrimeSixtySevenRowZeroPilot.second_row_binding

private theorem row_1 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 1 j.val=
      packedDigit 3 (secondRowCode 1) j.val := by
  decide +kernel

private theorem row_2 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 2 j.val=
      packedDigit 3 (secondRowCode 2) j.val := by
  decide +kernel

private theorem row_3 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 3 j.val=
      packedDigit 3 (secondRowCode 3) j.val := by
  decide +kernel

private theorem row_4 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 4 j.val=
      packedDigit 3 (secondRowCode 4) j.val := by
  decide +kernel

private theorem row_5 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 5 j.val=
      packedDigit 3 (secondRowCode 5) j.val := by
  decide +kernel

private theorem row_6 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 6 j.val=
      packedDigit 3 (secondRowCode 6) j.val := by
  decide +kernel

private theorem row_7 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 7 j.val=
      packedDigit 3 (secondRowCode 7) j.val := by
  decide +kernel

private theorem row_8 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 8 j.val=
      packedDigit 3 (secondRowCode 8) j.val := by
  decide +kernel

private theorem row_9 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 9 j.val=
      packedDigit 3 (secondRowCode 9) j.val := by
  decide +kernel

private theorem row_10 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 10 j.val=
      packedDigit 3 (secondRowCode 10) j.val := by
  decide +kernel

private theorem row_11 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 11 j.val=
      packedDigit 3 (secondRowCode 11) j.val := by
  decide +kernel

private theorem row_12 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 12 j.val=
      packedDigit 3 (secondRowCode 12) j.val := by
  decide +kernel

private theorem row_13 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 13 j.val=
      packedDigit 3 (secondRowCode 13) j.val := by
  decide +kernel

private theorem row_14 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 14 j.val=
      packedDigit 3 (secondRowCode 14) j.val := by
  decide +kernel

private theorem row_15 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 15 j.val=
      packedDigit 3 (secondRowCode 15) j.val := by
  decide +kernel

private theorem row_16 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 16 j.val=
      packedDigit 3 (secondRowCode 16) j.val := by
  decide +kernel

private theorem row_17 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 17 j.val=
      packedDigit 3 (secondRowCode 17) j.val := by
  decide +kernel

private theorem row_18 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 18 j.val=
      packedDigit 3 (secondRowCode 18) j.val := by
  decide +kernel

private theorem row_19 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 19 j.val=
      packedDigit 3 (secondRowCode 19) j.val := by
  decide +kernel

private theorem row_20 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 20 j.val=
      packedDigit 3 (secondRowCode 20) j.val := by
  decide +kernel

private theorem row_21 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 21 j.val=
      packedDigit 3 (secondRowCode 21) j.val := by
  decide +kernel

private theorem row_22 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 22 j.val=
      packedDigit 3 (secondRowCode 22) j.val := by
  decide +kernel

private theorem row_23 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 23 j.val=
      packedDigit 3 (secondRowCode 23) j.val := by
  decide +kernel

private theorem row_24 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 24 j.val=
      packedDigit 3 (secondRowCode 24) j.val := by
  decide +kernel

private theorem row_25 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 25 j.val=
      packedDigit 3 (secondRowCode 25) j.val := by
  decide +kernel

private theorem row_26 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 26 j.val=
      packedDigit 3 (secondRowCode 26) j.val := by
  decide +kernel

private theorem row_27 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 27 j.val=
      packedDigit 3 (secondRowCode 27) j.val := by
  decide +kernel

private theorem row_28 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 28 j.val=
      packedDigit 3 (secondRowCode 28) j.val := by
  decide +kernel

private theorem row_29 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 29 j.val=
      packedDigit 3 (secondRowCode 29) j.val := by
  decide +kernel

private theorem row_30 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 30 j.val=
      packedDigit 3 (secondRowCode 30) j.val := by
  decide +kernel

private theorem row_31 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 31 j.val=
      packedDigit 3 (secondRowCode 31) j.val := by
  decide +kernel

private theorem row_32 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 32 j.val=
      packedDigit 3 (secondRowCode 32) j.val := by
  decide +kernel

private theorem row_33 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 33 j.val=
      packedDigit 3 (secondRowCode 33) j.val := by
  decide +kernel

private theorem row_34 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 34 j.val=
      packedDigit 3 (secondRowCode 34) j.val := by
  decide +kernel

private theorem row_35 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 35 j.val=
      packedDigit 3 (secondRowCode 35) j.val := by
  decide +kernel

private theorem row_36 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 36 j.val=
      packedDigit 3 (secondRowCode 36) j.val := by
  decide +kernel

private theorem row_37 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 37 j.val=
      packedDigit 3 (secondRowCode 37) j.val := by
  decide +kernel

private theorem row_38 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 38 j.val=
      packedDigit 3 (secondRowCode 38) j.val := by
  decide +kernel

private theorem row_39 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 39 j.val=
      packedDigit 3 (secondRowCode 39) j.val := by
  decide +kernel

private theorem row_40 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 40 j.val=
      packedDigit 3 (secondRowCode 40) j.val := by
  decide +kernel

private theorem row_41 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 41 j.val=
      packedDigit 3 (secondRowCode 41) j.val := by
  decide +kernel

private theorem row_42 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 42 j.val=
      packedDigit 3 (secondRowCode 42) j.val := by
  decide +kernel

private theorem row_43 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 43 j.val=
      packedDigit 3 (secondRowCode 43) j.val := by
  decide +kernel

private theorem row_44 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 44 j.val=
      packedDigit 3 (secondRowCode 44) j.val := by
  decide +kernel

private theorem row_45 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 45 j.val=
      packedDigit 3 (secondRowCode 45) j.val := by
  decide +kernel

private theorem row_46 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 46 j.val=
      packedDigit 3 (secondRowCode 46) j.val := by
  decide +kernel

private theorem row_47 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 47 j.val=
      packedDigit 3 (secondRowCode 47) j.val := by
  decide +kernel

private theorem row_48 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 48 j.val=
      packedDigit 3 (secondRowCode 48) j.val := by
  decide +kernel

private theorem row_49 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 49 j.val=
      packedDigit 3 (secondRowCode 49) j.val := by
  decide +kernel

private theorem row_50 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 50 j.val=
      packedDigit 3 (secondRowCode 50) j.val := by
  decide +kernel

private theorem row_51 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 51 j.val=
      packedDigit 3 (secondRowCode 51) j.val := by
  decide +kernel

private theorem row_52 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 52 j.val=
      packedDigit 3 (secondRowCode 52) j.val := by
  decide +kernel

private theorem row_53 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 53 j.val=
      packedDigit 3 (secondRowCode 53) j.val := by
  decide +kernel

private theorem row_54 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 54 j.val=
      packedDigit 3 (secondRowCode 54) j.val := by
  decide +kernel

private theorem row_55 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 55 j.val=
      packedDigit 3 (secondRowCode 55) j.val := by
  decide +kernel

private theorem row_56 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 56 j.val=
      packedDigit 3 (secondRowCode 56) j.val := by
  decide +kernel

private theorem row_57 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 57 j.val=
      packedDigit 3 (secondRowCode 57) j.val := by
  decide +kernel

private theorem row_58 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 58 j.val=
      packedDigit 3 (secondRowCode 58) j.val := by
  decide +kernel

private theorem row_59 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 59 j.val=
      packedDigit 3 (secondRowCode 59) j.val := by
  decide +kernel

private theorem row_60 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 60 j.val=
      packedDigit 3 (secondRowCode 60) j.val := by
  decide +kernel

private theorem row_61 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 61 j.val=
      packedDigit 3 (secondRowCode 61) j.val := by
  decide +kernel

private theorem row_62 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 62 j.val=
      packedDigit 3 (secondRowCode 62) j.val := by
  decide +kernel

private theorem row_63 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 63 j.val=
      packedDigit 3 (secondRowCode 63) j.val := by
  decide +kernel

private theorem row_64 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 64 j.val=
      packedDigit 3 (secondRowCode 64) j.val := by
  decide +kernel

private theorem row_65 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 65 j.val=
      packedDigit 3 (secondRowCode 65) j.val := by
  decide +kernel

private theorem row_66 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 66 j.val=
      packedDigit 3 (secondRowCode 66) j.val := by
  decide +kernel

private theorem row_67 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 67 j.val=
      packedDigit 3 (secondRowCode 67) j.val := by
  decide +kernel

private theorem row_68 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 68 j.val=
      packedDigit 3 (secondRowCode 68) j.val := by
  decide +kernel

private theorem row_69 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 69 j.val=
      packedDigit 3 (secondRowCode 69) j.val := by
  decide +kernel

private theorem row_70 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 70 j.val=
      packedDigit 3 (secondRowCode 70) j.val := by
  decide +kernel

private theorem row_71 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 71 j.val=
      packedDigit 3 (secondRowCode 71) j.val := by
  decide +kernel

private theorem row_72 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 72 j.val=
      packedDigit 3 (secondRowCode 72) j.val := by
  decide +kernel

private theorem row_73 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 73 j.val=
      packedDigit 3 (secondRowCode 73) j.val := by
  decide +kernel

private theorem row_74 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 74 j.val=
      packedDigit 3 (secondRowCode 74) j.val := by
  decide +kernel

private theorem row_75 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 75 j.val=
      packedDigit 3 (secondRowCode 75) j.val := by
  decide +kernel

private theorem row_76 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 76 j.val=
      packedDigit 3 (secondRowCode 76) j.val := by
  decide +kernel

private theorem row_77 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 77 j.val=
      packedDigit 3 (secondRowCode 77) j.val := by
  decide +kernel

private theorem row_78 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 78 j.val=
      packedDigit 3 (secondRowCode 78) j.val := by
  decide +kernel

private theorem row_79 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 79 j.val=
      packedDigit 3 (secondRowCode 79) j.val := by
  decide +kernel

private theorem row_80 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 80 j.val=
      packedDigit 3 (secondRowCode 80) j.val := by
  decide +kernel

private theorem row_81 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 81 j.val=
      packedDigit 3 (secondRowCode 81) j.val := by
  decide +kernel

private theorem row_82 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 82 j.val=
      packedDigit 3 (secondRowCode 82) j.val := by
  decide +kernel

private theorem row_83 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 83 j.val=
      packedDigit 3 (secondRowCode 83) j.val := by
  decide +kernel

private theorem row_84 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 84 j.val=
      packedDigit 3 (secondRowCode 84) j.val := by
  decide +kernel

private theorem row_85 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 85 j.val=
      packedDigit 3 (secondRowCode 85) j.val := by
  decide +kernel

private theorem row_86 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 86 j.val=
      packedDigit 3 (secondRowCode 86) j.val := by
  decide +kernel

private theorem row_87 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 87 j.val=
      packedDigit 3 (secondRowCode 87) j.val := by
  decide +kernel

private theorem row_88 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 88 j.val=
      packedDigit 3 (secondRowCode 88) j.val := by
  decide +kernel

private theorem row_89 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 89 j.val=
      packedDigit 3 (secondRowCode 89) j.val := by
  decide +kernel

private theorem row_90 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 90 j.val=
      packedDigit 3 (secondRowCode 90) j.val := by
  decide +kernel

private theorem row_91 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 91 j.val=
      packedDigit 3 (secondRowCode 91) j.val := by
  decide +kernel

private theorem row_92 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 92 j.val=
      packedDigit 3 (secondRowCode 92) j.val := by
  decide +kernel

private theorem row_93 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 93 j.val=
      packedDigit 3 (secondRowCode 93) j.val := by
  decide +kernel

private theorem row_94 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 94 j.val=
      packedDigit 3 (secondRowCode 94) j.val := by
  decide +kernel

private theorem row_95 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 95 j.val=
      packedDigit 3 (secondRowCode 95) j.val := by
  decide +kernel

private theorem row_96 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 96 j.val=
      packedDigit 3 (secondRowCode 96) j.val := by
  decide +kernel

private theorem row_97 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 97 j.val=
      packedDigit 3 (secondRowCode 97) j.val := by
  decide +kernel

private theorem row_98 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 98 j.val=
      packedDigit 3 (secondRowCode 98) j.val := by
  decide +kernel

private theorem row_99 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 99 j.val=
      packedDigit 3 (secondRowCode 99) j.val := by
  decide +kernel

private theorem row_100 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 100 j.val=
      packedDigit 3 (secondRowCode 100) j.val := by
  decide +kernel

private theorem row_101 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 101 j.val=
      packedDigit 3 (secondRowCode 101) j.val := by
  decide +kernel

private theorem row_102 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 102 j.val=
      packedDigit 3 (secondRowCode 102) j.val := by
  decide +kernel

private theorem row_103 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 103 j.val=
      packedDigit 3 (secondRowCode 103) j.val := by
  decide +kernel

private theorem row_104 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 104 j.val=
      packedDigit 3 (secondRowCode 104) j.val := by
  decide +kernel

private theorem row_105 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 105 j.val=
      packedDigit 3 (secondRowCode 105) j.val := by
  decide +kernel

private theorem row_106 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 106 j.val=
      packedDigit 3 (secondRowCode 106) j.val := by
  decide +kernel

private theorem row_107 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 107 j.val=
      packedDigit 3 (secondRowCode 107) j.val := by
  decide +kernel

private theorem row_108 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 108 j.val=
      packedDigit 3 (secondRowCode 108) j.val := by
  decide +kernel

private theorem row_109 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 109 j.val=
      packedDigit 3 (secondRowCode 109) j.val := by
  decide +kernel

private theorem row_110 : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 110 j.val=
      packedDigit 3 (secondRowCode 110) j.val := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem binding (i j : Fin 111) :
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 i.val j.val=
      packedDigit 3 (secondRowCode i.val) j.val := by
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

end SymmetricSubgroupAsymptotics.CFSGLyPrimeSixtySevenSecondRows
