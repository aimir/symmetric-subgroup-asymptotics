import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.CFSGCoOneUpstreamPrimeElevenPackedData

/-! One original Co1 matrix: 24 independent literal row bindings. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoOneUpstreamPrimeElevenFirstRows
open MatrixNaturalRowDotReflection CFSGCoOneUpstreamPrimeElevenPackedData

private theorem row_0 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 0 j.val =
      packedDigit 1 (firstRowCode 0) j.val := by decide +kernel

private theorem row_1 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 1 j.val =
      packedDigit 1 (firstRowCode 1) j.val := by decide +kernel

private theorem row_2 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 2 j.val =
      packedDigit 1 (firstRowCode 2) j.val := by decide +kernel

private theorem row_3 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 3 j.val =
      packedDigit 1 (firstRowCode 3) j.val := by decide +kernel

private theorem row_4 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 4 j.val =
      packedDigit 1 (firstRowCode 4) j.val := by decide +kernel

private theorem row_5 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 5 j.val =
      packedDigit 1 (firstRowCode 5) j.val := by decide +kernel

private theorem row_6 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 6 j.val =
      packedDigit 1 (firstRowCode 6) j.val := by decide +kernel

private theorem row_7 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 7 j.val =
      packedDigit 1 (firstRowCode 7) j.val := by decide +kernel

private theorem row_8 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 8 j.val =
      packedDigit 1 (firstRowCode 8) j.val := by decide +kernel

private theorem row_9 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 9 j.val =
      packedDigit 1 (firstRowCode 9) j.val := by decide +kernel

private theorem row_10 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 10 j.val =
      packedDigit 1 (firstRowCode 10) j.val := by decide +kernel

private theorem row_11 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 11 j.val =
      packedDigit 1 (firstRowCode 11) j.val := by decide +kernel

private theorem row_12 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 12 j.val =
      packedDigit 1 (firstRowCode 12) j.val := by decide +kernel

private theorem row_13 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 13 j.val =
      packedDigit 1 (firstRowCode 13) j.val := by decide +kernel

private theorem row_14 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 14 j.val =
      packedDigit 1 (firstRowCode 14) j.val := by decide +kernel

private theorem row_15 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 15 j.val =
      packedDigit 1 (firstRowCode 15) j.val := by decide +kernel

private theorem row_16 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 16 j.val =
      packedDigit 1 (firstRowCode 16) j.val := by decide +kernel

private theorem row_17 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 17 j.val =
      packedDigit 1 (firstRowCode 17) j.val := by decide +kernel

private theorem row_18 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 18 j.val =
      packedDigit 1 (firstRowCode 18) j.val := by decide +kernel

private theorem row_19 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 19 j.val =
      packedDigit 1 (firstRowCode 19) j.val := by decide +kernel

private theorem row_20 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 20 j.val =
      packedDigit 1 (firstRowCode 20) j.val := by decide +kernel

private theorem row_21 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 21 j.val =
      packedDigit 1 (firstRowCode 21) j.val := by decide +kernel

private theorem row_22 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 22 j.val =
      packedDigit 1 (firstRowCode 22) j.val := by decide +kernel

private theorem row_23 : ∀ j : Fin 24,
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 23 j.val =
      packedDigit 1 (firstRowCode 23) j.val := by decide +kernel

theorem binding (i j : Fin 24) :
    rawDigit CFSG.Models.MatrixGroups.Co1.rows1 i.val j.val =
      packedDigit 1 (firstRowCode i.val) j.val := by
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

end SymmetricSubgroupAsymptotics.CFSGCoOneUpstreamPrimeElevenFirstRows
