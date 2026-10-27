import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows32..63.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock01
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨32+i.val,by omega⟩

private theorem row_image_32 (p : Fin 12) :
    (rows 32).val p = rowForward 32 p := by
  calc
    (rows 32).val p = rowPoint 32 p := (rowPoint_eq 32 p).symm
    _ = rowForward 32 p := by fin_cases p <;> decide +kernel

private theorem transition_check_32 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 32) (generatorPermutation s p) =
      generatorPermutation s (rowForward 32 p) := by
  decide +kernel

private theorem code_encoding_32 :
    code 32 = ∑ p : Fin 12, (rowForward 32 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_32 : code 32 < code 33 := by
  decide +kernel

private theorem row_image_33 (p : Fin 12) :
    (rows 33).val p = rowForward 33 p := by
  calc
    (rows 33).val p = rowPoint 33 p := (rowPoint_eq 33 p).symm
    _ = rowForward 33 p := by fin_cases p <;> decide +kernel

private theorem transition_check_33 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 33) (generatorPermutation s p) =
      generatorPermutation s (rowForward 33 p) := by
  decide +kernel

private theorem code_encoding_33 :
    code 33 = ∑ p : Fin 12, (rowForward 33 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_33 : code 33 < code 34 := by
  decide +kernel

private theorem row_image_34 (p : Fin 12) :
    (rows 34).val p = rowForward 34 p := by
  calc
    (rows 34).val p = rowPoint 34 p := (rowPoint_eq 34 p).symm
    _ = rowForward 34 p := by fin_cases p <;> decide +kernel

private theorem transition_check_34 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 34) (generatorPermutation s p) =
      generatorPermutation s (rowForward 34 p) := by
  decide +kernel

private theorem code_encoding_34 :
    code 34 = ∑ p : Fin 12, (rowForward 34 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_34 : code 34 < code 35 := by
  decide +kernel

private theorem row_image_35 (p : Fin 12) :
    (rows 35).val p = rowForward 35 p := by
  calc
    (rows 35).val p = rowPoint 35 p := (rowPoint_eq 35 p).symm
    _ = rowForward 35 p := by fin_cases p <;> decide +kernel

private theorem transition_check_35 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 35) (generatorPermutation s p) =
      generatorPermutation s (rowForward 35 p) := by
  decide +kernel

private theorem code_encoding_35 :
    code 35 = ∑ p : Fin 12, (rowForward 35 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_35 : code 35 < code 36 := by
  decide +kernel

private theorem row_image_36 (p : Fin 12) :
    (rows 36).val p = rowForward 36 p := by
  calc
    (rows 36).val p = rowPoint 36 p := (rowPoint_eq 36 p).symm
    _ = rowForward 36 p := by fin_cases p <;> decide +kernel

private theorem transition_check_36 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 36) (generatorPermutation s p) =
      generatorPermutation s (rowForward 36 p) := by
  decide +kernel

private theorem code_encoding_36 :
    code 36 = ∑ p : Fin 12, (rowForward 36 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_36 : code 36 < code 37 := by
  decide +kernel

private theorem row_image_37 (p : Fin 12) :
    (rows 37).val p = rowForward 37 p := by
  calc
    (rows 37).val p = rowPoint 37 p := (rowPoint_eq 37 p).symm
    _ = rowForward 37 p := by fin_cases p <;> decide +kernel

private theorem transition_check_37 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 37) (generatorPermutation s p) =
      generatorPermutation s (rowForward 37 p) := by
  decide +kernel

private theorem code_encoding_37 :
    code 37 = ∑ p : Fin 12, (rowForward 37 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_37 : code 37 < code 38 := by
  decide +kernel

private theorem row_image_38 (p : Fin 12) :
    (rows 38).val p = rowForward 38 p := by
  calc
    (rows 38).val p = rowPoint 38 p := (rowPoint_eq 38 p).symm
    _ = rowForward 38 p := by fin_cases p <;> decide +kernel

private theorem transition_check_38 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 38) (generatorPermutation s p) =
      generatorPermutation s (rowForward 38 p) := by
  decide +kernel

private theorem code_encoding_38 :
    code 38 = ∑ p : Fin 12, (rowForward 38 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_38 : code 38 < code 39 := by
  decide +kernel

private theorem row_image_39 (p : Fin 12) :
    (rows 39).val p = rowForward 39 p := by
  calc
    (rows 39).val p = rowPoint 39 p := (rowPoint_eq 39 p).symm
    _ = rowForward 39 p := by fin_cases p <;> decide +kernel

private theorem transition_check_39 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 39) (generatorPermutation s p) =
      generatorPermutation s (rowForward 39 p) := by
  decide +kernel

private theorem code_encoding_39 :
    code 39 = ∑ p : Fin 12, (rowForward 39 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_39 : code 39 < code 40 := by
  decide +kernel

private theorem row_image_40 (p : Fin 12) :
    (rows 40).val p = rowForward 40 p := by
  calc
    (rows 40).val p = rowPoint 40 p := (rowPoint_eq 40 p).symm
    _ = rowForward 40 p := by fin_cases p <;> decide +kernel

private theorem transition_check_40 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 40) (generatorPermutation s p) =
      generatorPermutation s (rowForward 40 p) := by
  decide +kernel

private theorem code_encoding_40 :
    code 40 = ∑ p : Fin 12, (rowForward 40 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_40 : code 40 < code 41 := by
  decide +kernel

private theorem row_image_41 (p : Fin 12) :
    (rows 41).val p = rowForward 41 p := by
  calc
    (rows 41).val p = rowPoint 41 p := (rowPoint_eq 41 p).symm
    _ = rowForward 41 p := by fin_cases p <;> decide +kernel

private theorem transition_check_41 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 41) (generatorPermutation s p) =
      generatorPermutation s (rowForward 41 p) := by
  decide +kernel

private theorem code_encoding_41 :
    code 41 = ∑ p : Fin 12, (rowForward 41 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_41 : code 41 < code 42 := by
  decide +kernel

private theorem row_image_42 (p : Fin 12) :
    (rows 42).val p = rowForward 42 p := by
  calc
    (rows 42).val p = rowPoint 42 p := (rowPoint_eq 42 p).symm
    _ = rowForward 42 p := by fin_cases p <;> decide +kernel

private theorem transition_check_42 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 42) (generatorPermutation s p) =
      generatorPermutation s (rowForward 42 p) := by
  decide +kernel

private theorem code_encoding_42 :
    code 42 = ∑ p : Fin 12, (rowForward 42 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_42 : code 42 < code 43 := by
  decide +kernel

private theorem row_image_43 (p : Fin 12) :
    (rows 43).val p = rowForward 43 p := by
  calc
    (rows 43).val p = rowPoint 43 p := (rowPoint_eq 43 p).symm
    _ = rowForward 43 p := by fin_cases p <;> decide +kernel

private theorem transition_check_43 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 43) (generatorPermutation s p) =
      generatorPermutation s (rowForward 43 p) := by
  decide +kernel

private theorem code_encoding_43 :
    code 43 = ∑ p : Fin 12, (rowForward 43 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_43 : code 43 < code 44 := by
  decide +kernel

private theorem row_image_44 (p : Fin 12) :
    (rows 44).val p = rowForward 44 p := by
  calc
    (rows 44).val p = rowPoint 44 p := (rowPoint_eq 44 p).symm
    _ = rowForward 44 p := by fin_cases p <;> decide +kernel

private theorem transition_check_44 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 44) (generatorPermutation s p) =
      generatorPermutation s (rowForward 44 p) := by
  decide +kernel

private theorem code_encoding_44 :
    code 44 = ∑ p : Fin 12, (rowForward 44 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_44 : code 44 < code 45 := by
  decide +kernel

private theorem row_image_45 (p : Fin 12) :
    (rows 45).val p = rowForward 45 p := by
  calc
    (rows 45).val p = rowPoint 45 p := (rowPoint_eq 45 p).symm
    _ = rowForward 45 p := by fin_cases p <;> decide +kernel

private theorem transition_check_45 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 45) (generatorPermutation s p) =
      generatorPermutation s (rowForward 45 p) := by
  decide +kernel

private theorem code_encoding_45 :
    code 45 = ∑ p : Fin 12, (rowForward 45 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_45 : code 45 < code 46 := by
  decide +kernel

private theorem row_image_46 (p : Fin 12) :
    (rows 46).val p = rowForward 46 p := by
  calc
    (rows 46).val p = rowPoint 46 p := (rowPoint_eq 46 p).symm
    _ = rowForward 46 p := by fin_cases p <;> decide +kernel

private theorem transition_check_46 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 46) (generatorPermutation s p) =
      generatorPermutation s (rowForward 46 p) := by
  decide +kernel

private theorem code_encoding_46 :
    code 46 = ∑ p : Fin 12, (rowForward 46 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_46 : code 46 < code 47 := by
  decide +kernel

private theorem row_image_47 (p : Fin 12) :
    (rows 47).val p = rowForward 47 p := by
  calc
    (rows 47).val p = rowPoint 47 p := (rowPoint_eq 47 p).symm
    _ = rowForward 47 p := by fin_cases p <;> decide +kernel

private theorem transition_check_47 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 47) (generatorPermutation s p) =
      generatorPermutation s (rowForward 47 p) := by
  decide +kernel

private theorem code_encoding_47 :
    code 47 = ∑ p : Fin 12, (rowForward 47 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_47 : code 47 < code 48 := by
  decide +kernel

private theorem row_image_48 (p : Fin 12) :
    (rows 48).val p = rowForward 48 p := by
  calc
    (rows 48).val p = rowPoint 48 p := (rowPoint_eq 48 p).symm
    _ = rowForward 48 p := by fin_cases p <;> decide +kernel

private theorem transition_check_48 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 48) (generatorPermutation s p) =
      generatorPermutation s (rowForward 48 p) := by
  decide +kernel

private theorem code_encoding_48 :
    code 48 = ∑ p : Fin 12, (rowForward 48 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_48 : code 48 < code 49 := by
  decide +kernel

private theorem row_image_49 (p : Fin 12) :
    (rows 49).val p = rowForward 49 p := by
  calc
    (rows 49).val p = rowPoint 49 p := (rowPoint_eq 49 p).symm
    _ = rowForward 49 p := by fin_cases p <;> decide +kernel

private theorem transition_check_49 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 49) (generatorPermutation s p) =
      generatorPermutation s (rowForward 49 p) := by
  decide +kernel

private theorem code_encoding_49 :
    code 49 = ∑ p : Fin 12, (rowForward 49 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_49 : code 49 < code 50 := by
  decide +kernel

private theorem row_image_50 (p : Fin 12) :
    (rows 50).val p = rowForward 50 p := by
  calc
    (rows 50).val p = rowPoint 50 p := (rowPoint_eq 50 p).symm
    _ = rowForward 50 p := by fin_cases p <;> decide +kernel

private theorem transition_check_50 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 50) (generatorPermutation s p) =
      generatorPermutation s (rowForward 50 p) := by
  decide +kernel

private theorem code_encoding_50 :
    code 50 = ∑ p : Fin 12, (rowForward 50 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_50 : code 50 < code 51 := by
  decide +kernel

private theorem row_image_51 (p : Fin 12) :
    (rows 51).val p = rowForward 51 p := by
  calc
    (rows 51).val p = rowPoint 51 p := (rowPoint_eq 51 p).symm
    _ = rowForward 51 p := by fin_cases p <;> decide +kernel

private theorem transition_check_51 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 51) (generatorPermutation s p) =
      generatorPermutation s (rowForward 51 p) := by
  decide +kernel

private theorem code_encoding_51 :
    code 51 = ∑ p : Fin 12, (rowForward 51 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_51 : code 51 < code 52 := by
  decide +kernel

private theorem row_image_52 (p : Fin 12) :
    (rows 52).val p = rowForward 52 p := by
  calc
    (rows 52).val p = rowPoint 52 p := (rowPoint_eq 52 p).symm
    _ = rowForward 52 p := by fin_cases p <;> decide +kernel

private theorem transition_check_52 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 52) (generatorPermutation s p) =
      generatorPermutation s (rowForward 52 p) := by
  decide +kernel

private theorem code_encoding_52 :
    code 52 = ∑ p : Fin 12, (rowForward 52 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_52 : code 52 < code 53 := by
  decide +kernel

private theorem row_image_53 (p : Fin 12) :
    (rows 53).val p = rowForward 53 p := by
  calc
    (rows 53).val p = rowPoint 53 p := (rowPoint_eq 53 p).symm
    _ = rowForward 53 p := by fin_cases p <;> decide +kernel

private theorem transition_check_53 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 53) (generatorPermutation s p) =
      generatorPermutation s (rowForward 53 p) := by
  decide +kernel

private theorem code_encoding_53 :
    code 53 = ∑ p : Fin 12, (rowForward 53 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_53 : code 53 < code 54 := by
  decide +kernel

private theorem row_image_54 (p : Fin 12) :
    (rows 54).val p = rowForward 54 p := by
  calc
    (rows 54).val p = rowPoint 54 p := (rowPoint_eq 54 p).symm
    _ = rowForward 54 p := by fin_cases p <;> decide +kernel

private theorem transition_check_54 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 54) (generatorPermutation s p) =
      generatorPermutation s (rowForward 54 p) := by
  decide +kernel

private theorem code_encoding_54 :
    code 54 = ∑ p : Fin 12, (rowForward 54 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_54 : code 54 < code 55 := by
  decide +kernel

private theorem row_image_55 (p : Fin 12) :
    (rows 55).val p = rowForward 55 p := by
  calc
    (rows 55).val p = rowPoint 55 p := (rowPoint_eq 55 p).symm
    _ = rowForward 55 p := by fin_cases p <;> decide +kernel

private theorem transition_check_55 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 55) (generatorPermutation s p) =
      generatorPermutation s (rowForward 55 p) := by
  decide +kernel

private theorem code_encoding_55 :
    code 55 = ∑ p : Fin 12, (rowForward 55 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_55 : code 55 < code 56 := by
  decide +kernel

private theorem row_image_56 (p : Fin 12) :
    (rows 56).val p = rowForward 56 p := by
  calc
    (rows 56).val p = rowPoint 56 p := (rowPoint_eq 56 p).symm
    _ = rowForward 56 p := by fin_cases p <;> decide +kernel

private theorem transition_check_56 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 56) (generatorPermutation s p) =
      generatorPermutation s (rowForward 56 p) := by
  decide +kernel

private theorem code_encoding_56 :
    code 56 = ∑ p : Fin 12, (rowForward 56 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_56 : code 56 < code 57 := by
  decide +kernel

private theorem row_image_57 (p : Fin 12) :
    (rows 57).val p = rowForward 57 p := by
  calc
    (rows 57).val p = rowPoint 57 p := (rowPoint_eq 57 p).symm
    _ = rowForward 57 p := by fin_cases p <;> decide +kernel

private theorem transition_check_57 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 57) (generatorPermutation s p) =
      generatorPermutation s (rowForward 57 p) := by
  decide +kernel

private theorem code_encoding_57 :
    code 57 = ∑ p : Fin 12, (rowForward 57 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_57 : code 57 < code 58 := by
  decide +kernel

private theorem row_image_58 (p : Fin 12) :
    (rows 58).val p = rowForward 58 p := by
  calc
    (rows 58).val p = rowPoint 58 p := (rowPoint_eq 58 p).symm
    _ = rowForward 58 p := by fin_cases p <;> decide +kernel

private theorem transition_check_58 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 58) (generatorPermutation s p) =
      generatorPermutation s (rowForward 58 p) := by
  decide +kernel

private theorem code_encoding_58 :
    code 58 = ∑ p : Fin 12, (rowForward 58 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_58 : code 58 < code 59 := by
  decide +kernel

private theorem row_image_59 (p : Fin 12) :
    (rows 59).val p = rowForward 59 p := by
  calc
    (rows 59).val p = rowPoint 59 p := (rowPoint_eq 59 p).symm
    _ = rowForward 59 p := by fin_cases p <;> decide +kernel

private theorem transition_check_59 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 59) (generatorPermutation s p) =
      generatorPermutation s (rowForward 59 p) := by
  decide +kernel

private theorem code_encoding_59 :
    code 59 = ∑ p : Fin 12, (rowForward 59 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_59 : code 59 < code 60 := by
  decide +kernel

private theorem row_image_60 (p : Fin 12) :
    (rows 60).val p = rowForward 60 p := by
  calc
    (rows 60).val p = rowPoint 60 p := (rowPoint_eq 60 p).symm
    _ = rowForward 60 p := by fin_cases p <;> decide +kernel

private theorem transition_check_60 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 60) (generatorPermutation s p) =
      generatorPermutation s (rowForward 60 p) := by
  decide +kernel

private theorem code_encoding_60 :
    code 60 = ∑ p : Fin 12, (rowForward 60 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_60 : code 60 < code 61 := by
  decide +kernel

private theorem row_image_61 (p : Fin 12) :
    (rows 61).val p = rowForward 61 p := by
  calc
    (rows 61).val p = rowPoint 61 p := (rowPoint_eq 61 p).symm
    _ = rowForward 61 p := by fin_cases p <;> decide +kernel

private theorem transition_check_61 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 61) (generatorPermutation s p) =
      generatorPermutation s (rowForward 61 p) := by
  decide +kernel

private theorem code_encoding_61 :
    code 61 = ∑ p : Fin 12, (rowForward 61 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_61 : code 61 < code 62 := by
  decide +kernel

private theorem row_image_62 (p : Fin 12) :
    (rows 62).val p = rowForward 62 p := by
  calc
    (rows 62).val p = rowPoint 62 p := (rowPoint_eq 62 p).symm
    _ = rowForward 62 p := by fin_cases p <;> decide +kernel

private theorem transition_check_62 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 62) (generatorPermutation s p) =
      generatorPermutation s (rowForward 62 p) := by
  decide +kernel

private theorem code_encoding_62 :
    code 62 = ∑ p : Fin 12, (rowForward 62 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_62 : code 62 < code 63 := by
  decide +kernel

private theorem row_image_63 (p : Fin 12) :
    (rows 63).val p = rowForward 63 p := by
  calc
    (rows 63).val p = rowPoint 63 p := (rowPoint_eq 63 p).symm
    _ = rowForward 63 p := by fin_cases p <;> decide +kernel

private theorem transition_check_63 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 63) (generatorPermutation s p) =
      generatorPermutation s (rowForward 63 p) := by
  decide +kernel

private theorem code_encoding_63 :
    code 63 = ∑ p : Fin 12, (rowForward 63 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_63 : code 63 < code 64 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (32 : Fin 495) from rfl))
      (row_image_32 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (33 : Fin 495) from rfl))
      (row_image_33 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (34 : Fin 495) from rfl))
      (row_image_34 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (35 : Fin 495) from rfl))
      (row_image_35 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (36 : Fin 495) from rfl))
      (row_image_36 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (37 : Fin 495) from rfl))
      (row_image_37 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (38 : Fin 495) from rfl))
      (row_image_38 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (39 : Fin 495) from rfl))
      (row_image_39 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (40 : Fin 495) from rfl))
      (row_image_40 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (41 : Fin 495) from rfl))
      (row_image_41 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (42 : Fin 495) from rfl))
      (row_image_42 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (43 : Fin 495) from rfl))
      (row_image_43 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (44 : Fin 495) from rfl))
      (row_image_44 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (45 : Fin 495) from rfl))
      (row_image_45 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (46 : Fin 495) from rfl))
      (row_image_46 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (47 : Fin 495) from rfl))
      (row_image_47 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (48 : Fin 495) from rfl))
      (row_image_48 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (49 : Fin 495) from rfl))
      (row_image_49 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (50 : Fin 495) from rfl))
      (row_image_50 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (51 : Fin 495) from rfl))
      (row_image_51 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (52 : Fin 495) from rfl))
      (row_image_52 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (53 : Fin 495) from rfl))
      (row_image_53 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (54 : Fin 495) from rfl))
      (row_image_54 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (55 : Fin 495) from rfl))
      (row_image_55 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (56 : Fin 495) from rfl))
      (row_image_56 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (57 : Fin 495) from rfl))
      (row_image_57 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (58 : Fin 495) from rfl))
      (row_image_58 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (59 : Fin 495) from rfl))
      (row_image_59 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (60 : Fin 495) from rfl))
      (row_image_60 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (61 : Fin 495) from rfl))
      (row_image_61 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (62 : Fin 495) from rfl))
      (row_image_62 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (63 : Fin 495) from rfl))
      (row_image_63 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (32 : Fin 495) from rfl))
      (transition_check_32 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (33 : Fin 495) from rfl))
      (transition_check_33 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (34 : Fin 495) from rfl))
      (transition_check_34 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (35 : Fin 495) from rfl))
      (transition_check_35 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (36 : Fin 495) from rfl))
      (transition_check_36 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (37 : Fin 495) from rfl))
      (transition_check_37 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (38 : Fin 495) from rfl))
      (transition_check_38 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (39 : Fin 495) from rfl))
      (transition_check_39 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (40 : Fin 495) from rfl))
      (transition_check_40 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (41 : Fin 495) from rfl))
      (transition_check_41 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (42 : Fin 495) from rfl))
      (transition_check_42 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (43 : Fin 495) from rfl))
      (transition_check_43 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (44 : Fin 495) from rfl))
      (transition_check_44 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (45 : Fin 495) from rfl))
      (transition_check_45 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (46 : Fin 495) from rfl))
      (transition_check_46 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (47 : Fin 495) from rfl))
      (transition_check_47 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (48 : Fin 495) from rfl))
      (transition_check_48 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (49 : Fin 495) from rfl))
      (transition_check_49 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (50 : Fin 495) from rfl))
      (transition_check_50 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (51 : Fin 495) from rfl))
      (transition_check_51 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (52 : Fin 495) from rfl))
      (transition_check_52 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (53 : Fin 495) from rfl))
      (transition_check_53 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (54 : Fin 495) from rfl))
      (transition_check_54 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (55 : Fin 495) from rfl))
      (transition_check_55 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (56 : Fin 495) from rfl))
      (transition_check_56 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (57 : Fin 495) from rfl))
      (transition_check_57 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (58 : Fin 495) from rfl))
      (transition_check_58 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (59 : Fin 495) from rfl))
      (transition_check_59 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (60 : Fin 495) from rfl))
      (transition_check_60 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (61 : Fin 495) from rfl))
      (transition_check_61 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (62 : Fin 495) from rfl))
      (transition_check_62 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (63 : Fin 495) from rfl))
      (transition_check_63 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (32 : Fin 495) from rfl))
      code_encoding_32
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (33 : Fin 495) from rfl))
      code_encoding_33
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (34 : Fin 495) from rfl))
      code_encoding_34
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (35 : Fin 495) from rfl))
      code_encoding_35
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (36 : Fin 495) from rfl))
      code_encoding_36
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (37 : Fin 495) from rfl))
      code_encoding_37
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (38 : Fin 495) from rfl))
      code_encoding_38
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (39 : Fin 495) from rfl))
      code_encoding_39
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (40 : Fin 495) from rfl))
      code_encoding_40
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (41 : Fin 495) from rfl))
      code_encoding_41
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (42 : Fin 495) from rfl))
      code_encoding_42
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (43 : Fin 495) from rfl))
      code_encoding_43
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (44 : Fin 495) from rfl))
      code_encoding_44
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (45 : Fin 495) from rfl))
      code_encoding_45
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (46 : Fin 495) from rfl))
      code_encoding_46
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (47 : Fin 495) from rfl))
      code_encoding_47
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (48 : Fin 495) from rfl))
      code_encoding_48
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (49 : Fin 495) from rfl))
      code_encoding_49
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (50 : Fin 495) from rfl))
      code_encoding_50
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (51 : Fin 495) from rfl))
      code_encoding_51
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (52 : Fin 495) from rfl))
      code_encoding_52
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (53 : Fin 495) from rfl))
      code_encoding_53
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (54 : Fin 495) from rfl))
      code_encoding_54
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (55 : Fin 495) from rfl))
      code_encoding_55
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (56 : Fin 495) from rfl))
      code_encoding_56
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (57 : Fin 495) from rfl))
      code_encoding_57
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (58 : Fin 495) from rfl))
      code_encoding_58
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (59 : Fin 495) from rfl))
      code_encoding_59
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (60 : Fin 495) from rfl))
      code_encoding_60
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (61 : Fin 495) from rfl))
      code_encoding_61
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (62 : Fin 495) from rfl))
      code_encoding_62
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (63 : Fin 495) from rfl))
      code_encoding_63

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (32 : Fin 495) from rfl))
    intro h
    exact code_adjacent_32
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (33 : Fin 495) from rfl))
    intro h
    exact code_adjacent_33
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (34 : Fin 495) from rfl))
    intro h
    exact code_adjacent_34
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (35 : Fin 495) from rfl))
    intro h
    exact code_adjacent_35
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (36 : Fin 495) from rfl))
    intro h
    exact code_adjacent_36
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (37 : Fin 495) from rfl))
    intro h
    exact code_adjacent_37
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (38 : Fin 495) from rfl))
    intro h
    exact code_adjacent_38
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (39 : Fin 495) from rfl))
    intro h
    exact code_adjacent_39
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (40 : Fin 495) from rfl))
    intro h
    exact code_adjacent_40
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (41 : Fin 495) from rfl))
    intro h
    exact code_adjacent_41
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (42 : Fin 495) from rfl))
    intro h
    exact code_adjacent_42
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (43 : Fin 495) from rfl))
    intro h
    exact code_adjacent_43
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (44 : Fin 495) from rfl))
    intro h
    exact code_adjacent_44
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (45 : Fin 495) from rfl))
    intro h
    exact code_adjacent_45
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (46 : Fin 495) from rfl))
    intro h
    exact code_adjacent_46
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (47 : Fin 495) from rfl))
    intro h
    exact code_adjacent_47
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (48 : Fin 495) from rfl))
    intro h
    exact code_adjacent_48
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (49 : Fin 495) from rfl))
    intro h
    exact code_adjacent_49
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (50 : Fin 495) from rfl))
    intro h
    exact code_adjacent_50
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (51 : Fin 495) from rfl))
    intro h
    exact code_adjacent_51
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (52 : Fin 495) from rfl))
    intro h
    exact code_adjacent_52
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (53 : Fin 495) from rfl))
    intro h
    exact code_adjacent_53
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (54 : Fin 495) from rfl))
    intro h
    exact code_adjacent_54
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (55 : Fin 495) from rfl))
    intro h
    exact code_adjacent_55
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (56 : Fin 495) from rfl))
    intro h
    exact code_adjacent_56
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (57 : Fin 495) from rfl))
    intro h
    exact code_adjacent_57
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (58 : Fin 495) from rfl))
    intro h
    exact code_adjacent_58
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (59 : Fin 495) from rfl))
    intro h
    exact code_adjacent_59
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (60 : Fin 495) from rfl))
    intro h
    exact code_adjacent_60
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (61 : Fin 495) from rfl))
    intro h
    exact code_adjacent_61
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (62 : Fin 495) from rfl))
    intro h
    exact code_adjacent_62
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (63 : Fin 495) from rfl))
    intro h
    exact code_adjacent_63

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock01
