import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.CFSGCoOneUpstreamPrimeElevenPackedData

/-! One original Co1 matrix: 24 independent literal row bindings. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoOneUpstreamPrimeElevenSecondRows
open MatrixNaturalRowDotReflection CFSGCoOneUpstreamPrimeElevenPackedData

private theorem row_0 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 0 j.val =
      packedDigit 1 (secondRowCode 0) j.val := by decide +kernel

private theorem row_1 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 1 j.val =
      packedDigit 1 (secondRowCode 1) j.val := by decide +kernel

private theorem row_2 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 2 j.val =
      packedDigit 1 (secondRowCode 2) j.val := by decide +kernel

private theorem row_3 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 3 j.val =
      packedDigit 1 (secondRowCode 3) j.val := by decide +kernel

private theorem row_4 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 4 j.val =
      packedDigit 1 (secondRowCode 4) j.val := by decide +kernel

private theorem row_5 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 5 j.val =
      packedDigit 1 (secondRowCode 5) j.val := by decide +kernel

private theorem row_6 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 6 j.val =
      packedDigit 1 (secondRowCode 6) j.val := by decide +kernel

private theorem row_7 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 7 j.val =
      packedDigit 1 (secondRowCode 7) j.val := by decide +kernel

private theorem row_8 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 8 j.val =
      packedDigit 1 (secondRowCode 8) j.val := by decide +kernel

private theorem row_9 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 9 j.val =
      packedDigit 1 (secondRowCode 9) j.val := by decide +kernel

private theorem row_10 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 10 j.val =
      packedDigit 1 (secondRowCode 10) j.val := by decide +kernel

private theorem row_11 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 11 j.val =
      packedDigit 1 (secondRowCode 11) j.val := by decide +kernel

private theorem row_12 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 12 j.val =
      packedDigit 1 (secondRowCode 12) j.val := by decide +kernel

private theorem row_13 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 13 j.val =
      packedDigit 1 (secondRowCode 13) j.val := by decide +kernel

private theorem row_14 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 14 j.val =
      packedDigit 1 (secondRowCode 14) j.val := by decide +kernel

private theorem row_15 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 15 j.val =
      packedDigit 1 (secondRowCode 15) j.val := by decide +kernel

private theorem row_16 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 16 j.val =
      packedDigit 1 (secondRowCode 16) j.val := by decide +kernel

private theorem row_17 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 17 j.val =
      packedDigit 1 (secondRowCode 17) j.val := by decide +kernel

private theorem row_18 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 18 j.val =
      packedDigit 1 (secondRowCode 18) j.val := by decide +kernel

private theorem row_19 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 19 j.val =
      packedDigit 1 (secondRowCode 19) j.val := by decide +kernel

private theorem row_20 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 20 j.val =
      packedDigit 1 (secondRowCode 20) j.val := by decide +kernel

private theorem row_21 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 21 j.val =
      packedDigit 1 (secondRowCode 21) j.val := by decide +kernel

private theorem row_22 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 22 j.val =
      packedDigit 1 (secondRowCode 22) j.val := by decide +kernel

private theorem row_23 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 23 j.val =
      packedDigit 1 (secondRowCode 23) j.val := by decide +kernel

theorem binding (i j : Fin 24) :
    rawDigit CFSG.Models.MatrixGroups.Co1.rows2 i.val j.val =
      packedDigit 1 (secondRowCode i.val) j.val := by
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

end SymmetricSubgroupAsymptotics.CFSGCoOneUpstreamPrimeElevenSecondRows
