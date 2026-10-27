import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! RECOVERY PILOT ONLY: the SAME selected x orbit, rows0..31.
Every numerical command is confined to ONE row. In particular there is no
495-row universal decision, no new orbit search, and no class-size claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock00
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 :=
  ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩

private theorem row_image_0 (p : Fin 12) :
    (rows 0).val p = rowForward 0 p := by
  calc
    (rows 0).val p = rowPoint 0 p := (rowPoint_eq 0 p).symm
    _ = rowForward 0 p := by fin_cases p <;> decide +kernel

private theorem transition_check_0 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 0) (generatorPermutation s p) =
      generatorPermutation s (rowForward 0 p) := by
  decide +kernel

private theorem code_encoding_0 :
    code 0 = ∑ p : Fin 12, (rowForward 0 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_0 : code 0 < code 1 := by
  decide +kernel

private theorem row_image_1 (p : Fin 12) :
    (rows 1).val p = rowForward 1 p := by
  calc
    (rows 1).val p = rowPoint 1 p := (rowPoint_eq 1 p).symm
    _ = rowForward 1 p := by fin_cases p <;> decide +kernel

private theorem transition_check_1 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 1) (generatorPermutation s p) =
      generatorPermutation s (rowForward 1 p) := by
  decide +kernel

private theorem code_encoding_1 :
    code 1 = ∑ p : Fin 12, (rowForward 1 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_1 : code 1 < code 2 := by
  decide +kernel

private theorem row_image_2 (p : Fin 12) :
    (rows 2).val p = rowForward 2 p := by
  calc
    (rows 2).val p = rowPoint 2 p := (rowPoint_eq 2 p).symm
    _ = rowForward 2 p := by fin_cases p <;> decide +kernel

private theorem transition_check_2 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 2) (generatorPermutation s p) =
      generatorPermutation s (rowForward 2 p) := by
  decide +kernel

private theorem code_encoding_2 :
    code 2 = ∑ p : Fin 12, (rowForward 2 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_2 : code 2 < code 3 := by
  decide +kernel

private theorem row_image_3 (p : Fin 12) :
    (rows 3).val p = rowForward 3 p := by
  calc
    (rows 3).val p = rowPoint 3 p := (rowPoint_eq 3 p).symm
    _ = rowForward 3 p := by fin_cases p <;> decide +kernel

private theorem transition_check_3 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 3) (generatorPermutation s p) =
      generatorPermutation s (rowForward 3 p) := by
  decide +kernel

private theorem code_encoding_3 :
    code 3 = ∑ p : Fin 12, (rowForward 3 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_3 : code 3 < code 4 := by
  decide +kernel

private theorem row_image_4 (p : Fin 12) :
    (rows 4).val p = rowForward 4 p := by
  calc
    (rows 4).val p = rowPoint 4 p := (rowPoint_eq 4 p).symm
    _ = rowForward 4 p := by fin_cases p <;> decide +kernel

private theorem transition_check_4 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 4) (generatorPermutation s p) =
      generatorPermutation s (rowForward 4 p) := by
  decide +kernel

private theorem code_encoding_4 :
    code 4 = ∑ p : Fin 12, (rowForward 4 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_4 : code 4 < code 5 := by
  decide +kernel

private theorem row_image_5 (p : Fin 12) :
    (rows 5).val p = rowForward 5 p := by
  calc
    (rows 5).val p = rowPoint 5 p := (rowPoint_eq 5 p).symm
    _ = rowForward 5 p := by fin_cases p <;> decide +kernel

private theorem transition_check_5 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 5) (generatorPermutation s p) =
      generatorPermutation s (rowForward 5 p) := by
  decide +kernel

private theorem code_encoding_5 :
    code 5 = ∑ p : Fin 12, (rowForward 5 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_5 : code 5 < code 6 := by
  decide +kernel

private theorem row_image_6 (p : Fin 12) :
    (rows 6).val p = rowForward 6 p := by
  calc
    (rows 6).val p = rowPoint 6 p := (rowPoint_eq 6 p).symm
    _ = rowForward 6 p := by fin_cases p <;> decide +kernel

private theorem transition_check_6 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 6) (generatorPermutation s p) =
      generatorPermutation s (rowForward 6 p) := by
  decide +kernel

private theorem code_encoding_6 :
    code 6 = ∑ p : Fin 12, (rowForward 6 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_6 : code 6 < code 7 := by
  decide +kernel

private theorem row_image_7 (p : Fin 12) :
    (rows 7).val p = rowForward 7 p := by
  calc
    (rows 7).val p = rowPoint 7 p := (rowPoint_eq 7 p).symm
    _ = rowForward 7 p := by fin_cases p <;> decide +kernel

private theorem transition_check_7 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 7) (generatorPermutation s p) =
      generatorPermutation s (rowForward 7 p) := by
  decide +kernel

private theorem code_encoding_7 :
    code 7 = ∑ p : Fin 12, (rowForward 7 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_7 : code 7 < code 8 := by
  decide +kernel

private theorem row_image_8 (p : Fin 12) :
    (rows 8).val p = rowForward 8 p := by
  calc
    (rows 8).val p = rowPoint 8 p := (rowPoint_eq 8 p).symm
    _ = rowForward 8 p := by fin_cases p <;> decide +kernel

private theorem transition_check_8 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 8) (generatorPermutation s p) =
      generatorPermutation s (rowForward 8 p) := by
  decide +kernel

private theorem code_encoding_8 :
    code 8 = ∑ p : Fin 12, (rowForward 8 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_8 : code 8 < code 9 := by
  decide +kernel

private theorem row_image_9 (p : Fin 12) :
    (rows 9).val p = rowForward 9 p := by
  calc
    (rows 9).val p = rowPoint 9 p := (rowPoint_eq 9 p).symm
    _ = rowForward 9 p := by fin_cases p <;> decide +kernel

private theorem transition_check_9 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 9) (generatorPermutation s p) =
      generatorPermutation s (rowForward 9 p) := by
  decide +kernel

private theorem code_encoding_9 :
    code 9 = ∑ p : Fin 12, (rowForward 9 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_9 : code 9 < code 10 := by
  decide +kernel

private theorem row_image_10 (p : Fin 12) :
    (rows 10).val p = rowForward 10 p := by
  calc
    (rows 10).val p = rowPoint 10 p := (rowPoint_eq 10 p).symm
    _ = rowForward 10 p := by fin_cases p <;> decide +kernel

private theorem transition_check_10 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 10) (generatorPermutation s p) =
      generatorPermutation s (rowForward 10 p) := by
  decide +kernel

private theorem code_encoding_10 :
    code 10 = ∑ p : Fin 12, (rowForward 10 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_10 : code 10 < code 11 := by
  decide +kernel

private theorem row_image_11 (p : Fin 12) :
    (rows 11).val p = rowForward 11 p := by
  calc
    (rows 11).val p = rowPoint 11 p := (rowPoint_eq 11 p).symm
    _ = rowForward 11 p := by fin_cases p <;> decide +kernel

private theorem transition_check_11 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 11) (generatorPermutation s p) =
      generatorPermutation s (rowForward 11 p) := by
  decide +kernel

private theorem code_encoding_11 :
    code 11 = ∑ p : Fin 12, (rowForward 11 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_11 : code 11 < code 12 := by
  decide +kernel

private theorem row_image_12 (p : Fin 12) :
    (rows 12).val p = rowForward 12 p := by
  calc
    (rows 12).val p = rowPoint 12 p := (rowPoint_eq 12 p).symm
    _ = rowForward 12 p := by fin_cases p <;> decide +kernel

private theorem transition_check_12 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 12) (generatorPermutation s p) =
      generatorPermutation s (rowForward 12 p) := by
  decide +kernel

private theorem code_encoding_12 :
    code 12 = ∑ p : Fin 12, (rowForward 12 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_12 : code 12 < code 13 := by
  decide +kernel

private theorem row_image_13 (p : Fin 12) :
    (rows 13).val p = rowForward 13 p := by
  calc
    (rows 13).val p = rowPoint 13 p := (rowPoint_eq 13 p).symm
    _ = rowForward 13 p := by fin_cases p <;> decide +kernel

private theorem transition_check_13 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 13) (generatorPermutation s p) =
      generatorPermutation s (rowForward 13 p) := by
  decide +kernel

private theorem code_encoding_13 :
    code 13 = ∑ p : Fin 12, (rowForward 13 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_13 : code 13 < code 14 := by
  decide +kernel

private theorem row_image_14 (p : Fin 12) :
    (rows 14).val p = rowForward 14 p := by
  calc
    (rows 14).val p = rowPoint 14 p := (rowPoint_eq 14 p).symm
    _ = rowForward 14 p := by fin_cases p <;> decide +kernel

private theorem transition_check_14 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 14) (generatorPermutation s p) =
      generatorPermutation s (rowForward 14 p) := by
  decide +kernel

private theorem code_encoding_14 :
    code 14 = ∑ p : Fin 12, (rowForward 14 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_14 : code 14 < code 15 := by
  decide +kernel

private theorem row_image_15 (p : Fin 12) :
    (rows 15).val p = rowForward 15 p := by
  calc
    (rows 15).val p = rowPoint 15 p := (rowPoint_eq 15 p).symm
    _ = rowForward 15 p := by fin_cases p <;> decide +kernel

private theorem transition_check_15 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 15) (generatorPermutation s p) =
      generatorPermutation s (rowForward 15 p) := by
  decide +kernel

private theorem code_encoding_15 :
    code 15 = ∑ p : Fin 12, (rowForward 15 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_15 : code 15 < code 16 := by
  decide +kernel

private theorem row_image_16 (p : Fin 12) :
    (rows 16).val p = rowForward 16 p := by
  calc
    (rows 16).val p = rowPoint 16 p := (rowPoint_eq 16 p).symm
    _ = rowForward 16 p := by fin_cases p <;> decide +kernel

private theorem transition_check_16 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 16) (generatorPermutation s p) =
      generatorPermutation s (rowForward 16 p) := by
  decide +kernel

private theorem code_encoding_16 :
    code 16 = ∑ p : Fin 12, (rowForward 16 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_16 : code 16 < code 17 := by
  decide +kernel

private theorem row_image_17 (p : Fin 12) :
    (rows 17).val p = rowForward 17 p := by
  calc
    (rows 17).val p = rowPoint 17 p := (rowPoint_eq 17 p).symm
    _ = rowForward 17 p := by fin_cases p <;> decide +kernel

private theorem transition_check_17 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 17) (generatorPermutation s p) =
      generatorPermutation s (rowForward 17 p) := by
  decide +kernel

private theorem code_encoding_17 :
    code 17 = ∑ p : Fin 12, (rowForward 17 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_17 : code 17 < code 18 := by
  decide +kernel

private theorem row_image_18 (p : Fin 12) :
    (rows 18).val p = rowForward 18 p := by
  calc
    (rows 18).val p = rowPoint 18 p := (rowPoint_eq 18 p).symm
    _ = rowForward 18 p := by fin_cases p <;> decide +kernel

private theorem transition_check_18 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 18) (generatorPermutation s p) =
      generatorPermutation s (rowForward 18 p) := by
  decide +kernel

private theorem code_encoding_18 :
    code 18 = ∑ p : Fin 12, (rowForward 18 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_18 : code 18 < code 19 := by
  decide +kernel

private theorem row_image_19 (p : Fin 12) :
    (rows 19).val p = rowForward 19 p := by
  calc
    (rows 19).val p = rowPoint 19 p := (rowPoint_eq 19 p).symm
    _ = rowForward 19 p := by fin_cases p <;> decide +kernel

private theorem transition_check_19 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 19) (generatorPermutation s p) =
      generatorPermutation s (rowForward 19 p) := by
  decide +kernel

private theorem code_encoding_19 :
    code 19 = ∑ p : Fin 12, (rowForward 19 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_19 : code 19 < code 20 := by
  decide +kernel

private theorem row_image_20 (p : Fin 12) :
    (rows 20).val p = rowForward 20 p := by
  calc
    (rows 20).val p = rowPoint 20 p := (rowPoint_eq 20 p).symm
    _ = rowForward 20 p := by fin_cases p <;> decide +kernel

private theorem transition_check_20 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 20) (generatorPermutation s p) =
      generatorPermutation s (rowForward 20 p) := by
  decide +kernel

private theorem code_encoding_20 :
    code 20 = ∑ p : Fin 12, (rowForward 20 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_20 : code 20 < code 21 := by
  decide +kernel

private theorem row_image_21 (p : Fin 12) :
    (rows 21).val p = rowForward 21 p := by
  calc
    (rows 21).val p = rowPoint 21 p := (rowPoint_eq 21 p).symm
    _ = rowForward 21 p := by fin_cases p <;> decide +kernel

private theorem transition_check_21 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 21) (generatorPermutation s p) =
      generatorPermutation s (rowForward 21 p) := by
  decide +kernel

private theorem code_encoding_21 :
    code 21 = ∑ p : Fin 12, (rowForward 21 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_21 : code 21 < code 22 := by
  decide +kernel

private theorem row_image_22 (p : Fin 12) :
    (rows 22).val p = rowForward 22 p := by
  calc
    (rows 22).val p = rowPoint 22 p := (rowPoint_eq 22 p).symm
    _ = rowForward 22 p := by fin_cases p <;> decide +kernel

private theorem transition_check_22 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 22) (generatorPermutation s p) =
      generatorPermutation s (rowForward 22 p) := by
  decide +kernel

private theorem code_encoding_22 :
    code 22 = ∑ p : Fin 12, (rowForward 22 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_22 : code 22 < code 23 := by
  decide +kernel

private theorem row_image_23 (p : Fin 12) :
    (rows 23).val p = rowForward 23 p := by
  calc
    (rows 23).val p = rowPoint 23 p := (rowPoint_eq 23 p).symm
    _ = rowForward 23 p := by fin_cases p <;> decide +kernel

private theorem transition_check_23 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 23) (generatorPermutation s p) =
      generatorPermutation s (rowForward 23 p) := by
  decide +kernel

private theorem code_encoding_23 :
    code 23 = ∑ p : Fin 12, (rowForward 23 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_23 : code 23 < code 24 := by
  decide +kernel

private theorem row_image_24 (p : Fin 12) :
    (rows 24).val p = rowForward 24 p := by
  calc
    (rows 24).val p = rowPoint 24 p := (rowPoint_eq 24 p).symm
    _ = rowForward 24 p := by fin_cases p <;> decide +kernel

private theorem transition_check_24 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 24) (generatorPermutation s p) =
      generatorPermutation s (rowForward 24 p) := by
  decide +kernel

private theorem code_encoding_24 :
    code 24 = ∑ p : Fin 12, (rowForward 24 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_24 : code 24 < code 25 := by
  decide +kernel

private theorem row_image_25 (p : Fin 12) :
    (rows 25).val p = rowForward 25 p := by
  calc
    (rows 25).val p = rowPoint 25 p := (rowPoint_eq 25 p).symm
    _ = rowForward 25 p := by fin_cases p <;> decide +kernel

private theorem transition_check_25 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 25) (generatorPermutation s p) =
      generatorPermutation s (rowForward 25 p) := by
  decide +kernel

private theorem code_encoding_25 :
    code 25 = ∑ p : Fin 12, (rowForward 25 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_25 : code 25 < code 26 := by
  decide +kernel

private theorem row_image_26 (p : Fin 12) :
    (rows 26).val p = rowForward 26 p := by
  calc
    (rows 26).val p = rowPoint 26 p := (rowPoint_eq 26 p).symm
    _ = rowForward 26 p := by fin_cases p <;> decide +kernel

private theorem transition_check_26 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 26) (generatorPermutation s p) =
      generatorPermutation s (rowForward 26 p) := by
  decide +kernel

private theorem code_encoding_26 :
    code 26 = ∑ p : Fin 12, (rowForward 26 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_26 : code 26 < code 27 := by
  decide +kernel

private theorem row_image_27 (p : Fin 12) :
    (rows 27).val p = rowForward 27 p := by
  calc
    (rows 27).val p = rowPoint 27 p := (rowPoint_eq 27 p).symm
    _ = rowForward 27 p := by fin_cases p <;> decide +kernel

private theorem transition_check_27 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 27) (generatorPermutation s p) =
      generatorPermutation s (rowForward 27 p) := by
  decide +kernel

private theorem code_encoding_27 :
    code 27 = ∑ p : Fin 12, (rowForward 27 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_27 : code 27 < code 28 := by
  decide +kernel

private theorem row_image_28 (p : Fin 12) :
    (rows 28).val p = rowForward 28 p := by
  calc
    (rows 28).val p = rowPoint 28 p := (rowPoint_eq 28 p).symm
    _ = rowForward 28 p := by fin_cases p <;> decide +kernel

private theorem transition_check_28 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 28) (generatorPermutation s p) =
      generatorPermutation s (rowForward 28 p) := by
  decide +kernel

private theorem code_encoding_28 :
    code 28 = ∑ p : Fin 12, (rowForward 28 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_28 : code 28 < code 29 := by
  decide +kernel

private theorem row_image_29 (p : Fin 12) :
    (rows 29).val p = rowForward 29 p := by
  calc
    (rows 29).val p = rowPoint 29 p := (rowPoint_eq 29 p).symm
    _ = rowForward 29 p := by fin_cases p <;> decide +kernel

private theorem transition_check_29 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 29) (generatorPermutation s p) =
      generatorPermutation s (rowForward 29 p) := by
  decide +kernel

private theorem code_encoding_29 :
    code 29 = ∑ p : Fin 12, (rowForward 29 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_29 : code 29 < code 30 := by
  decide +kernel

private theorem row_image_30 (p : Fin 12) :
    (rows 30).val p = rowForward 30 p := by
  calc
    (rows 30).val p = rowPoint 30 p := (rowPoint_eq 30 p).symm
    _ = rowForward 30 p := by fin_cases p <;> decide +kernel

private theorem transition_check_30 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 30) (generatorPermutation s p) =
      generatorPermutation s (rowForward 30 p) := by
  decide +kernel

private theorem code_encoding_30 :
    code 30 = ∑ p : Fin 12, (rowForward 30 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_30 : code 30 < code 31 := by
  decide +kernel

private theorem row_image_31 (p : Fin 12) :
    (rows 31).val p = rowForward 31 p := by
  calc
    (rows 31).val p = rowPoint 31 p := (rowPoint_eq 31 p).symm
    _ = rowForward 31 p := by fin_cases p <;> decide +kernel

private theorem transition_check_31 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 31) (generatorPermutation s p) =
      generatorPermutation s (rowForward 31 p) := by
  decide +kernel

private theorem code_encoding_31 :
    code 31 = ∑ p : Fin 12, (rowForward 31 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_31 : code 31 < code 32 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (0 : Fin 495) from rfl))
      (row_image_0 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (1 : Fin 495) from rfl))
      (row_image_1 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (2 : Fin 495) from rfl))
      (row_image_2 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (3 : Fin 495) from rfl))
      (row_image_3 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (4 : Fin 495) from rfl))
      (row_image_4 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (5 : Fin 495) from rfl))
      (row_image_5 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (6 : Fin 495) from rfl))
      (row_image_6 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (7 : Fin 495) from rfl))
      (row_image_7 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (8 : Fin 495) from rfl))
      (row_image_8 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (9 : Fin 495) from rfl))
      (row_image_9 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (10 : Fin 495) from rfl))
      (row_image_10 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (11 : Fin 495) from rfl))
      (row_image_11 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (12 : Fin 495) from rfl))
      (row_image_12 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (13 : Fin 495) from rfl))
      (row_image_13 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (14 : Fin 495) from rfl))
      (row_image_14 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (15 : Fin 495) from rfl))
      (row_image_15 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (16 : Fin 495) from rfl))
      (row_image_16 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (17 : Fin 495) from rfl))
      (row_image_17 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (18 : Fin 495) from rfl))
      (row_image_18 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (19 : Fin 495) from rfl))
      (row_image_19 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (20 : Fin 495) from rfl))
      (row_image_20 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (21 : Fin 495) from rfl))
      (row_image_21 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (22 : Fin 495) from rfl))
      (row_image_22 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (23 : Fin 495) from rfl))
      (row_image_23 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (24 : Fin 495) from rfl))
      (row_image_24 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (25 : Fin 495) from rfl))
      (row_image_25 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (26 : Fin 495) from rfl))
      (row_image_26 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (27 : Fin 495) from rfl))
      (row_image_27 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (28 : Fin 495) from rfl))
      (row_image_28 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (29 : Fin 495) from rfl))
      (row_image_29 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (30 : Fin 495) from rfl))
      (row_image_30 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (31 : Fin 495) from rfl))
      (row_image_31 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i
  · exact transition_check_0 s p
  · exact transition_check_1 s p
  · exact transition_check_2 s p
  · exact transition_check_3 s p
  · exact transition_check_4 s p
  · exact transition_check_5 s p
  · exact transition_check_6 s p
  · exact transition_check_7 s p
  · exact transition_check_8 s p
  · exact transition_check_9 s p
  · exact transition_check_10 s p
  · exact transition_check_11 s p
  · exact transition_check_12 s p
  · exact transition_check_13 s p
  · exact transition_check_14 s p
  · exact transition_check_15 s p
  · exact transition_check_16 s p
  · exact transition_check_17 s p
  · exact transition_check_18 s p
  · exact transition_check_19 s p
  · exact transition_check_20 s p
  · exact transition_check_21 s p
  · exact transition_check_22 s p
  · exact transition_check_23 s p
  · exact transition_check_24 s p
  · exact transition_check_25 s p
  · exact transition_check_26 s p
  · exact transition_check_27 s p
  · exact transition_check_28 s p
  · exact transition_check_29 s p
  · exact transition_check_30 s p
  · exact transition_check_31 s p

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i
  · exact code_encoding_0
  · exact code_encoding_1
  · exact code_encoding_2
  · exact code_encoding_3
  · exact code_encoding_4
  · exact code_encoding_5
  · exact code_encoding_6
  · exact code_encoding_7
  · exact code_encoding_8
  · exact code_encoding_9
  · exact code_encoding_10
  · exact code_encoding_11
  · exact code_encoding_12
  · exact code_encoding_13
  · exact code_encoding_14
  · exact code_encoding_15
  · exact code_encoding_16
  · exact code_encoding_17
  · exact code_encoding_18
  · exact code_encoding_19
  · exact code_encoding_20
  · exact code_encoding_21
  · exact code_encoding_22
  · exact code_encoding_23
  · exact code_encoding_24
  · exact code_encoding_25
  · exact code_encoding_26
  · exact code_encoding_27
  · exact code_encoding_28
  · exact code_encoding_29
  · exact code_encoding_30
  · exact code_encoding_31

theorem code_adjacent (i : Fin 32) :
    code (blockIndex i) < code ⟨i.val+1,Nat.lt_trans (Nat.succ_lt_succ i.isLt) (by decide)⟩ := by
  fin_cases i
  · exact code_adjacent_0
  · exact code_adjacent_1
  · exact code_adjacent_2
  · exact code_adjacent_3
  · exact code_adjacent_4
  · exact code_adjacent_5
  · exact code_adjacent_6
  · exact code_adjacent_7
  · exact code_adjacent_8
  · exact code_adjacent_9
  · exact code_adjacent_10
  · exact code_adjacent_11
  · exact code_adjacent_12
  · exact code_adjacent_13
  · exact code_adjacent_14
  · exact code_adjacent_15
  · exact code_adjacent_16
  · exact code_adjacent_17
  · exact code_adjacent_18
  · exact code_adjacent_19
  · exact code_adjacent_20
  · exact code_adjacent_21
  · exact code_adjacent_22
  · exact code_adjacent_23
  · exact code_adjacent_24
  · exact code_adjacent_25
  · exact code_adjacent_26
  · exact code_adjacent_27
  · exact code_adjacent_28
  · exact code_adjacent_29
  · exact code_adjacent_30
  · exact code_adjacent_31

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock00
