import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows64..95.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock02
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨64+i.val,by omega⟩

private theorem row_image_64 (p : Fin 12) :
    (rows 64).val p = rowForward 64 p := by
  calc
    (rows 64).val p = rowPoint 64 p := (rowPoint_eq 64 p).symm
    _ = rowForward 64 p := by fin_cases p <;> decide +kernel

private theorem transition_check_64 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 64) (generatorPermutation s p) =
      generatorPermutation s (rowForward 64 p) := by
  decide +kernel

private theorem code_encoding_64 :
    code 64 = ∑ p : Fin 12, (rowForward 64 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_64 : code 64 < code 65 := by
  decide +kernel

private theorem row_image_65 (p : Fin 12) :
    (rows 65).val p = rowForward 65 p := by
  calc
    (rows 65).val p = rowPoint 65 p := (rowPoint_eq 65 p).symm
    _ = rowForward 65 p := by fin_cases p <;> decide +kernel

private theorem transition_check_65 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 65) (generatorPermutation s p) =
      generatorPermutation s (rowForward 65 p) := by
  decide +kernel

private theorem code_encoding_65 :
    code 65 = ∑ p : Fin 12, (rowForward 65 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_65 : code 65 < code 66 := by
  decide +kernel

private theorem row_image_66 (p : Fin 12) :
    (rows 66).val p = rowForward 66 p := by
  calc
    (rows 66).val p = rowPoint 66 p := (rowPoint_eq 66 p).symm
    _ = rowForward 66 p := by fin_cases p <;> decide +kernel

private theorem transition_check_66 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 66) (generatorPermutation s p) =
      generatorPermutation s (rowForward 66 p) := by
  decide +kernel

private theorem code_encoding_66 :
    code 66 = ∑ p : Fin 12, (rowForward 66 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_66 : code 66 < code 67 := by
  decide +kernel

private theorem row_image_67 (p : Fin 12) :
    (rows 67).val p = rowForward 67 p := by
  calc
    (rows 67).val p = rowPoint 67 p := (rowPoint_eq 67 p).symm
    _ = rowForward 67 p := by fin_cases p <;> decide +kernel

private theorem transition_check_67 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 67) (generatorPermutation s p) =
      generatorPermutation s (rowForward 67 p) := by
  decide +kernel

private theorem code_encoding_67 :
    code 67 = ∑ p : Fin 12, (rowForward 67 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_67 : code 67 < code 68 := by
  decide +kernel

private theorem row_image_68 (p : Fin 12) :
    (rows 68).val p = rowForward 68 p := by
  calc
    (rows 68).val p = rowPoint 68 p := (rowPoint_eq 68 p).symm
    _ = rowForward 68 p := by fin_cases p <;> decide +kernel

private theorem transition_check_68 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 68) (generatorPermutation s p) =
      generatorPermutation s (rowForward 68 p) := by
  decide +kernel

private theorem code_encoding_68 :
    code 68 = ∑ p : Fin 12, (rowForward 68 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_68 : code 68 < code 69 := by
  decide +kernel

private theorem row_image_69 (p : Fin 12) :
    (rows 69).val p = rowForward 69 p := by
  calc
    (rows 69).val p = rowPoint 69 p := (rowPoint_eq 69 p).symm
    _ = rowForward 69 p := by fin_cases p <;> decide +kernel

private theorem transition_check_69 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 69) (generatorPermutation s p) =
      generatorPermutation s (rowForward 69 p) := by
  decide +kernel

private theorem code_encoding_69 :
    code 69 = ∑ p : Fin 12, (rowForward 69 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_69 : code 69 < code 70 := by
  decide +kernel

private theorem row_image_70 (p : Fin 12) :
    (rows 70).val p = rowForward 70 p := by
  calc
    (rows 70).val p = rowPoint 70 p := (rowPoint_eq 70 p).symm
    _ = rowForward 70 p := by fin_cases p <;> decide +kernel

private theorem transition_check_70 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 70) (generatorPermutation s p) =
      generatorPermutation s (rowForward 70 p) := by
  decide +kernel

private theorem code_encoding_70 :
    code 70 = ∑ p : Fin 12, (rowForward 70 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_70 : code 70 < code 71 := by
  decide +kernel

private theorem row_image_71 (p : Fin 12) :
    (rows 71).val p = rowForward 71 p := by
  calc
    (rows 71).val p = rowPoint 71 p := (rowPoint_eq 71 p).symm
    _ = rowForward 71 p := by fin_cases p <;> decide +kernel

private theorem transition_check_71 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 71) (generatorPermutation s p) =
      generatorPermutation s (rowForward 71 p) := by
  decide +kernel

private theorem code_encoding_71 :
    code 71 = ∑ p : Fin 12, (rowForward 71 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_71 : code 71 < code 72 := by
  decide +kernel

private theorem row_image_72 (p : Fin 12) :
    (rows 72).val p = rowForward 72 p := by
  calc
    (rows 72).val p = rowPoint 72 p := (rowPoint_eq 72 p).symm
    _ = rowForward 72 p := by fin_cases p <;> decide +kernel

private theorem transition_check_72 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 72) (generatorPermutation s p) =
      generatorPermutation s (rowForward 72 p) := by
  decide +kernel

private theorem code_encoding_72 :
    code 72 = ∑ p : Fin 12, (rowForward 72 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_72 : code 72 < code 73 := by
  decide +kernel

private theorem row_image_73 (p : Fin 12) :
    (rows 73).val p = rowForward 73 p := by
  calc
    (rows 73).val p = rowPoint 73 p := (rowPoint_eq 73 p).symm
    _ = rowForward 73 p := by fin_cases p <;> decide +kernel

private theorem transition_check_73 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 73) (generatorPermutation s p) =
      generatorPermutation s (rowForward 73 p) := by
  decide +kernel

private theorem code_encoding_73 :
    code 73 = ∑ p : Fin 12, (rowForward 73 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_73 : code 73 < code 74 := by
  decide +kernel

private theorem row_image_74 (p : Fin 12) :
    (rows 74).val p = rowForward 74 p := by
  calc
    (rows 74).val p = rowPoint 74 p := (rowPoint_eq 74 p).symm
    _ = rowForward 74 p := by fin_cases p <;> decide +kernel

private theorem transition_check_74 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 74) (generatorPermutation s p) =
      generatorPermutation s (rowForward 74 p) := by
  decide +kernel

private theorem code_encoding_74 :
    code 74 = ∑ p : Fin 12, (rowForward 74 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_74 : code 74 < code 75 := by
  decide +kernel

private theorem row_image_75 (p : Fin 12) :
    (rows 75).val p = rowForward 75 p := by
  calc
    (rows 75).val p = rowPoint 75 p := (rowPoint_eq 75 p).symm
    _ = rowForward 75 p := by fin_cases p <;> decide +kernel

private theorem transition_check_75 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 75) (generatorPermutation s p) =
      generatorPermutation s (rowForward 75 p) := by
  decide +kernel

private theorem code_encoding_75 :
    code 75 = ∑ p : Fin 12, (rowForward 75 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_75 : code 75 < code 76 := by
  decide +kernel

private theorem row_image_76 (p : Fin 12) :
    (rows 76).val p = rowForward 76 p := by
  calc
    (rows 76).val p = rowPoint 76 p := (rowPoint_eq 76 p).symm
    _ = rowForward 76 p := by fin_cases p <;> decide +kernel

private theorem transition_check_76 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 76) (generatorPermutation s p) =
      generatorPermutation s (rowForward 76 p) := by
  decide +kernel

private theorem code_encoding_76 :
    code 76 = ∑ p : Fin 12, (rowForward 76 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_76 : code 76 < code 77 := by
  decide +kernel

private theorem row_image_77 (p : Fin 12) :
    (rows 77).val p = rowForward 77 p := by
  calc
    (rows 77).val p = rowPoint 77 p := (rowPoint_eq 77 p).symm
    _ = rowForward 77 p := by fin_cases p <;> decide +kernel

private theorem transition_check_77 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 77) (generatorPermutation s p) =
      generatorPermutation s (rowForward 77 p) := by
  decide +kernel

private theorem code_encoding_77 :
    code 77 = ∑ p : Fin 12, (rowForward 77 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_77 : code 77 < code 78 := by
  decide +kernel

private theorem row_image_78 (p : Fin 12) :
    (rows 78).val p = rowForward 78 p := by
  calc
    (rows 78).val p = rowPoint 78 p := (rowPoint_eq 78 p).symm
    _ = rowForward 78 p := by fin_cases p <;> decide +kernel

private theorem transition_check_78 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 78) (generatorPermutation s p) =
      generatorPermutation s (rowForward 78 p) := by
  decide +kernel

private theorem code_encoding_78 :
    code 78 = ∑ p : Fin 12, (rowForward 78 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_78 : code 78 < code 79 := by
  decide +kernel

private theorem row_image_79 (p : Fin 12) :
    (rows 79).val p = rowForward 79 p := by
  calc
    (rows 79).val p = rowPoint 79 p := (rowPoint_eq 79 p).symm
    _ = rowForward 79 p := by fin_cases p <;> decide +kernel

private theorem transition_check_79 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 79) (generatorPermutation s p) =
      generatorPermutation s (rowForward 79 p) := by
  decide +kernel

private theorem code_encoding_79 :
    code 79 = ∑ p : Fin 12, (rowForward 79 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_79 : code 79 < code 80 := by
  decide +kernel

private theorem row_image_80 (p : Fin 12) :
    (rows 80).val p = rowForward 80 p := by
  calc
    (rows 80).val p = rowPoint 80 p := (rowPoint_eq 80 p).symm
    _ = rowForward 80 p := by fin_cases p <;> decide +kernel

private theorem transition_check_80 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 80) (generatorPermutation s p) =
      generatorPermutation s (rowForward 80 p) := by
  decide +kernel

private theorem code_encoding_80 :
    code 80 = ∑ p : Fin 12, (rowForward 80 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_80 : code 80 < code 81 := by
  decide +kernel

private theorem row_image_81 (p : Fin 12) :
    (rows 81).val p = rowForward 81 p := by
  calc
    (rows 81).val p = rowPoint 81 p := (rowPoint_eq 81 p).symm
    _ = rowForward 81 p := by fin_cases p <;> decide +kernel

private theorem transition_check_81 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 81) (generatorPermutation s p) =
      generatorPermutation s (rowForward 81 p) := by
  decide +kernel

private theorem code_encoding_81 :
    code 81 = ∑ p : Fin 12, (rowForward 81 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_81 : code 81 < code 82 := by
  decide +kernel

private theorem row_image_82 (p : Fin 12) :
    (rows 82).val p = rowForward 82 p := by
  calc
    (rows 82).val p = rowPoint 82 p := (rowPoint_eq 82 p).symm
    _ = rowForward 82 p := by fin_cases p <;> decide +kernel

private theorem transition_check_82 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 82) (generatorPermutation s p) =
      generatorPermutation s (rowForward 82 p) := by
  decide +kernel

private theorem code_encoding_82 :
    code 82 = ∑ p : Fin 12, (rowForward 82 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_82 : code 82 < code 83 := by
  decide +kernel

private theorem row_image_83 (p : Fin 12) :
    (rows 83).val p = rowForward 83 p := by
  calc
    (rows 83).val p = rowPoint 83 p := (rowPoint_eq 83 p).symm
    _ = rowForward 83 p := by fin_cases p <;> decide +kernel

private theorem transition_check_83 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 83) (generatorPermutation s p) =
      generatorPermutation s (rowForward 83 p) := by
  decide +kernel

private theorem code_encoding_83 :
    code 83 = ∑ p : Fin 12, (rowForward 83 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_83 : code 83 < code 84 := by
  decide +kernel

private theorem row_image_84 (p : Fin 12) :
    (rows 84).val p = rowForward 84 p := by
  calc
    (rows 84).val p = rowPoint 84 p := (rowPoint_eq 84 p).symm
    _ = rowForward 84 p := by fin_cases p <;> decide +kernel

private theorem transition_check_84 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 84) (generatorPermutation s p) =
      generatorPermutation s (rowForward 84 p) := by
  decide +kernel

private theorem code_encoding_84 :
    code 84 = ∑ p : Fin 12, (rowForward 84 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_84 : code 84 < code 85 := by
  decide +kernel

private theorem row_image_85 (p : Fin 12) :
    (rows 85).val p = rowForward 85 p := by
  calc
    (rows 85).val p = rowPoint 85 p := (rowPoint_eq 85 p).symm
    _ = rowForward 85 p := by fin_cases p <;> decide +kernel

private theorem transition_check_85 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 85) (generatorPermutation s p) =
      generatorPermutation s (rowForward 85 p) := by
  decide +kernel

private theorem code_encoding_85 :
    code 85 = ∑ p : Fin 12, (rowForward 85 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_85 : code 85 < code 86 := by
  decide +kernel

private theorem row_image_86 (p : Fin 12) :
    (rows 86).val p = rowForward 86 p := by
  calc
    (rows 86).val p = rowPoint 86 p := (rowPoint_eq 86 p).symm
    _ = rowForward 86 p := by fin_cases p <;> decide +kernel

private theorem transition_check_86 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 86) (generatorPermutation s p) =
      generatorPermutation s (rowForward 86 p) := by
  decide +kernel

private theorem code_encoding_86 :
    code 86 = ∑ p : Fin 12, (rowForward 86 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_86 : code 86 < code 87 := by
  decide +kernel

private theorem row_image_87 (p : Fin 12) :
    (rows 87).val p = rowForward 87 p := by
  calc
    (rows 87).val p = rowPoint 87 p := (rowPoint_eq 87 p).symm
    _ = rowForward 87 p := by fin_cases p <;> decide +kernel

private theorem transition_check_87 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 87) (generatorPermutation s p) =
      generatorPermutation s (rowForward 87 p) := by
  decide +kernel

private theorem code_encoding_87 :
    code 87 = ∑ p : Fin 12, (rowForward 87 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_87 : code 87 < code 88 := by
  decide +kernel

private theorem row_image_88 (p : Fin 12) :
    (rows 88).val p = rowForward 88 p := by
  calc
    (rows 88).val p = rowPoint 88 p := (rowPoint_eq 88 p).symm
    _ = rowForward 88 p := by fin_cases p <;> decide +kernel

private theorem transition_check_88 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 88) (generatorPermutation s p) =
      generatorPermutation s (rowForward 88 p) := by
  decide +kernel

private theorem code_encoding_88 :
    code 88 = ∑ p : Fin 12, (rowForward 88 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_88 : code 88 < code 89 := by
  decide +kernel

private theorem row_image_89 (p : Fin 12) :
    (rows 89).val p = rowForward 89 p := by
  calc
    (rows 89).val p = rowPoint 89 p := (rowPoint_eq 89 p).symm
    _ = rowForward 89 p := by fin_cases p <;> decide +kernel

private theorem transition_check_89 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 89) (generatorPermutation s p) =
      generatorPermutation s (rowForward 89 p) := by
  decide +kernel

private theorem code_encoding_89 :
    code 89 = ∑ p : Fin 12, (rowForward 89 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_89 : code 89 < code 90 := by
  decide +kernel

private theorem row_image_90 (p : Fin 12) :
    (rows 90).val p = rowForward 90 p := by
  calc
    (rows 90).val p = rowPoint 90 p := (rowPoint_eq 90 p).symm
    _ = rowForward 90 p := by fin_cases p <;> decide +kernel

private theorem transition_check_90 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 90) (generatorPermutation s p) =
      generatorPermutation s (rowForward 90 p) := by
  decide +kernel

private theorem code_encoding_90 :
    code 90 = ∑ p : Fin 12, (rowForward 90 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_90 : code 90 < code 91 := by
  decide +kernel

private theorem row_image_91 (p : Fin 12) :
    (rows 91).val p = rowForward 91 p := by
  calc
    (rows 91).val p = rowPoint 91 p := (rowPoint_eq 91 p).symm
    _ = rowForward 91 p := by fin_cases p <;> decide +kernel

private theorem transition_check_91 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 91) (generatorPermutation s p) =
      generatorPermutation s (rowForward 91 p) := by
  decide +kernel

private theorem code_encoding_91 :
    code 91 = ∑ p : Fin 12, (rowForward 91 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_91 : code 91 < code 92 := by
  decide +kernel

private theorem row_image_92 (p : Fin 12) :
    (rows 92).val p = rowForward 92 p := by
  calc
    (rows 92).val p = rowPoint 92 p := (rowPoint_eq 92 p).symm
    _ = rowForward 92 p := by fin_cases p <;> decide +kernel

private theorem transition_check_92 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 92) (generatorPermutation s p) =
      generatorPermutation s (rowForward 92 p) := by
  decide +kernel

private theorem code_encoding_92 :
    code 92 = ∑ p : Fin 12, (rowForward 92 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_92 : code 92 < code 93 := by
  decide +kernel

private theorem row_image_93 (p : Fin 12) :
    (rows 93).val p = rowForward 93 p := by
  calc
    (rows 93).val p = rowPoint 93 p := (rowPoint_eq 93 p).symm
    _ = rowForward 93 p := by fin_cases p <;> decide +kernel

private theorem transition_check_93 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 93) (generatorPermutation s p) =
      generatorPermutation s (rowForward 93 p) := by
  decide +kernel

private theorem code_encoding_93 :
    code 93 = ∑ p : Fin 12, (rowForward 93 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_93 : code 93 < code 94 := by
  decide +kernel

private theorem row_image_94 (p : Fin 12) :
    (rows 94).val p = rowForward 94 p := by
  calc
    (rows 94).val p = rowPoint 94 p := (rowPoint_eq 94 p).symm
    _ = rowForward 94 p := by fin_cases p <;> decide +kernel

private theorem transition_check_94 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 94) (generatorPermutation s p) =
      generatorPermutation s (rowForward 94 p) := by
  decide +kernel

private theorem code_encoding_94 :
    code 94 = ∑ p : Fin 12, (rowForward 94 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_94 : code 94 < code 95 := by
  decide +kernel

private theorem row_image_95 (p : Fin 12) :
    (rows 95).val p = rowForward 95 p := by
  calc
    (rows 95).val p = rowPoint 95 p := (rowPoint_eq 95 p).symm
    _ = rowForward 95 p := by fin_cases p <;> decide +kernel

private theorem transition_check_95 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 95) (generatorPermutation s p) =
      generatorPermutation s (rowForward 95 p) := by
  decide +kernel

private theorem code_encoding_95 :
    code 95 = ∑ p : Fin 12, (rowForward 95 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_95 : code 95 < code 96 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (64 : Fin 495) from rfl))
      (row_image_64 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (65 : Fin 495) from rfl))
      (row_image_65 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (66 : Fin 495) from rfl))
      (row_image_66 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (67 : Fin 495) from rfl))
      (row_image_67 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (68 : Fin 495) from rfl))
      (row_image_68 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (69 : Fin 495) from rfl))
      (row_image_69 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (70 : Fin 495) from rfl))
      (row_image_70 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (71 : Fin 495) from rfl))
      (row_image_71 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (72 : Fin 495) from rfl))
      (row_image_72 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (73 : Fin 495) from rfl))
      (row_image_73 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (74 : Fin 495) from rfl))
      (row_image_74 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (75 : Fin 495) from rfl))
      (row_image_75 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (76 : Fin 495) from rfl))
      (row_image_76 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (77 : Fin 495) from rfl))
      (row_image_77 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (78 : Fin 495) from rfl))
      (row_image_78 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (79 : Fin 495) from rfl))
      (row_image_79 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (80 : Fin 495) from rfl))
      (row_image_80 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (81 : Fin 495) from rfl))
      (row_image_81 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (82 : Fin 495) from rfl))
      (row_image_82 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (83 : Fin 495) from rfl))
      (row_image_83 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (84 : Fin 495) from rfl))
      (row_image_84 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (85 : Fin 495) from rfl))
      (row_image_85 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (86 : Fin 495) from rfl))
      (row_image_86 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (87 : Fin 495) from rfl))
      (row_image_87 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (88 : Fin 495) from rfl))
      (row_image_88 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (89 : Fin 495) from rfl))
      (row_image_89 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (90 : Fin 495) from rfl))
      (row_image_90 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (91 : Fin 495) from rfl))
      (row_image_91 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (92 : Fin 495) from rfl))
      (row_image_92 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (93 : Fin 495) from rfl))
      (row_image_93 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (94 : Fin 495) from rfl))
      (row_image_94 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (95 : Fin 495) from rfl))
      (row_image_95 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (64 : Fin 495) from rfl))
      (transition_check_64 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (65 : Fin 495) from rfl))
      (transition_check_65 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (66 : Fin 495) from rfl))
      (transition_check_66 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (67 : Fin 495) from rfl))
      (transition_check_67 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (68 : Fin 495) from rfl))
      (transition_check_68 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (69 : Fin 495) from rfl))
      (transition_check_69 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (70 : Fin 495) from rfl))
      (transition_check_70 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (71 : Fin 495) from rfl))
      (transition_check_71 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (72 : Fin 495) from rfl))
      (transition_check_72 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (73 : Fin 495) from rfl))
      (transition_check_73 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (74 : Fin 495) from rfl))
      (transition_check_74 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (75 : Fin 495) from rfl))
      (transition_check_75 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (76 : Fin 495) from rfl))
      (transition_check_76 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (77 : Fin 495) from rfl))
      (transition_check_77 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (78 : Fin 495) from rfl))
      (transition_check_78 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (79 : Fin 495) from rfl))
      (transition_check_79 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (80 : Fin 495) from rfl))
      (transition_check_80 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (81 : Fin 495) from rfl))
      (transition_check_81 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (82 : Fin 495) from rfl))
      (transition_check_82 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (83 : Fin 495) from rfl))
      (transition_check_83 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (84 : Fin 495) from rfl))
      (transition_check_84 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (85 : Fin 495) from rfl))
      (transition_check_85 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (86 : Fin 495) from rfl))
      (transition_check_86 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (87 : Fin 495) from rfl))
      (transition_check_87 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (88 : Fin 495) from rfl))
      (transition_check_88 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (89 : Fin 495) from rfl))
      (transition_check_89 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (90 : Fin 495) from rfl))
      (transition_check_90 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (91 : Fin 495) from rfl))
      (transition_check_91 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (92 : Fin 495) from rfl))
      (transition_check_92 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (93 : Fin 495) from rfl))
      (transition_check_93 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (94 : Fin 495) from rfl))
      (transition_check_94 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (95 : Fin 495) from rfl))
      (transition_check_95 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (64 : Fin 495) from rfl))
      code_encoding_64
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (65 : Fin 495) from rfl))
      code_encoding_65
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (66 : Fin 495) from rfl))
      code_encoding_66
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (67 : Fin 495) from rfl))
      code_encoding_67
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (68 : Fin 495) from rfl))
      code_encoding_68
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (69 : Fin 495) from rfl))
      code_encoding_69
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (70 : Fin 495) from rfl))
      code_encoding_70
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (71 : Fin 495) from rfl))
      code_encoding_71
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (72 : Fin 495) from rfl))
      code_encoding_72
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (73 : Fin 495) from rfl))
      code_encoding_73
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (74 : Fin 495) from rfl))
      code_encoding_74
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (75 : Fin 495) from rfl))
      code_encoding_75
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (76 : Fin 495) from rfl))
      code_encoding_76
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (77 : Fin 495) from rfl))
      code_encoding_77
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (78 : Fin 495) from rfl))
      code_encoding_78
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (79 : Fin 495) from rfl))
      code_encoding_79
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (80 : Fin 495) from rfl))
      code_encoding_80
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (81 : Fin 495) from rfl))
      code_encoding_81
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (82 : Fin 495) from rfl))
      code_encoding_82
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (83 : Fin 495) from rfl))
      code_encoding_83
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (84 : Fin 495) from rfl))
      code_encoding_84
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (85 : Fin 495) from rfl))
      code_encoding_85
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (86 : Fin 495) from rfl))
      code_encoding_86
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (87 : Fin 495) from rfl))
      code_encoding_87
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (88 : Fin 495) from rfl))
      code_encoding_88
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (89 : Fin 495) from rfl))
      code_encoding_89
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (90 : Fin 495) from rfl))
      code_encoding_90
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (91 : Fin 495) from rfl))
      code_encoding_91
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (92 : Fin 495) from rfl))
      code_encoding_92
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (93 : Fin 495) from rfl))
      code_encoding_93
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (94 : Fin 495) from rfl))
      code_encoding_94
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (95 : Fin 495) from rfl))
      code_encoding_95

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (64 : Fin 495) from rfl))
    intro h
    exact code_adjacent_64
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (65 : Fin 495) from rfl))
    intro h
    exact code_adjacent_65
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (66 : Fin 495) from rfl))
    intro h
    exact code_adjacent_66
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (67 : Fin 495) from rfl))
    intro h
    exact code_adjacent_67
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (68 : Fin 495) from rfl))
    intro h
    exact code_adjacent_68
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (69 : Fin 495) from rfl))
    intro h
    exact code_adjacent_69
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (70 : Fin 495) from rfl))
    intro h
    exact code_adjacent_70
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (71 : Fin 495) from rfl))
    intro h
    exact code_adjacent_71
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (72 : Fin 495) from rfl))
    intro h
    exact code_adjacent_72
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (73 : Fin 495) from rfl))
    intro h
    exact code_adjacent_73
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (74 : Fin 495) from rfl))
    intro h
    exact code_adjacent_74
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (75 : Fin 495) from rfl))
    intro h
    exact code_adjacent_75
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (76 : Fin 495) from rfl))
    intro h
    exact code_adjacent_76
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (77 : Fin 495) from rfl))
    intro h
    exact code_adjacent_77
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (78 : Fin 495) from rfl))
    intro h
    exact code_adjacent_78
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (79 : Fin 495) from rfl))
    intro h
    exact code_adjacent_79
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (80 : Fin 495) from rfl))
    intro h
    exact code_adjacent_80
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (81 : Fin 495) from rfl))
    intro h
    exact code_adjacent_81
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (82 : Fin 495) from rfl))
    intro h
    exact code_adjacent_82
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (83 : Fin 495) from rfl))
    intro h
    exact code_adjacent_83
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (84 : Fin 495) from rfl))
    intro h
    exact code_adjacent_84
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (85 : Fin 495) from rfl))
    intro h
    exact code_adjacent_85
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (86 : Fin 495) from rfl))
    intro h
    exact code_adjacent_86
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (87 : Fin 495) from rfl))
    intro h
    exact code_adjacent_87
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (88 : Fin 495) from rfl))
    intro h
    exact code_adjacent_88
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (89 : Fin 495) from rfl))
    intro h
    exact code_adjacent_89
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (90 : Fin 495) from rfl))
    intro h
    exact code_adjacent_90
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (91 : Fin 495) from rfl))
    intro h
    exact code_adjacent_91
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (92 : Fin 495) from rfl))
    intro h
    exact code_adjacent_92
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (93 : Fin 495) from rfl))
    intro h
    exact code_adjacent_93
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (94 : Fin 495) from rfl))
    intro h
    exact code_adjacent_94
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (95 : Fin 495) from rfl))
    intro h
    exact code_adjacent_95

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock02
