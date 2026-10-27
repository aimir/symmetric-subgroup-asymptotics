import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows96..127.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock03
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨96+i.val,by omega⟩

private theorem row_image_96 (p : Fin 12) :
    (rows 96).val p = rowForward 96 p := by
  calc
    (rows 96).val p = rowPoint 96 p := (rowPoint_eq 96 p).symm
    _ = rowForward 96 p := by fin_cases p <;> decide +kernel

private theorem transition_check_96 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 96) (generatorPermutation s p) =
      generatorPermutation s (rowForward 96 p) := by
  decide +kernel

private theorem code_encoding_96 :
    code 96 = ∑ p : Fin 12, (rowForward 96 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_96 : code 96 < code 97 := by
  decide +kernel

private theorem row_image_97 (p : Fin 12) :
    (rows 97).val p = rowForward 97 p := by
  calc
    (rows 97).val p = rowPoint 97 p := (rowPoint_eq 97 p).symm
    _ = rowForward 97 p := by fin_cases p <;> decide +kernel

private theorem transition_check_97 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 97) (generatorPermutation s p) =
      generatorPermutation s (rowForward 97 p) := by
  decide +kernel

private theorem code_encoding_97 :
    code 97 = ∑ p : Fin 12, (rowForward 97 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_97 : code 97 < code 98 := by
  decide +kernel

private theorem row_image_98 (p : Fin 12) :
    (rows 98).val p = rowForward 98 p := by
  calc
    (rows 98).val p = rowPoint 98 p := (rowPoint_eq 98 p).symm
    _ = rowForward 98 p := by fin_cases p <;> decide +kernel

private theorem transition_check_98 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 98) (generatorPermutation s p) =
      generatorPermutation s (rowForward 98 p) := by
  decide +kernel

private theorem code_encoding_98 :
    code 98 = ∑ p : Fin 12, (rowForward 98 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_98 : code 98 < code 99 := by
  decide +kernel

private theorem row_image_99 (p : Fin 12) :
    (rows 99).val p = rowForward 99 p := by
  calc
    (rows 99).val p = rowPoint 99 p := (rowPoint_eq 99 p).symm
    _ = rowForward 99 p := by fin_cases p <;> decide +kernel

private theorem transition_check_99 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 99) (generatorPermutation s p) =
      generatorPermutation s (rowForward 99 p) := by
  decide +kernel

private theorem code_encoding_99 :
    code 99 = ∑ p : Fin 12, (rowForward 99 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_99 : code 99 < code 100 := by
  decide +kernel

private theorem row_image_100 (p : Fin 12) :
    (rows 100).val p = rowForward 100 p := by
  calc
    (rows 100).val p = rowPoint 100 p := (rowPoint_eq 100 p).symm
    _ = rowForward 100 p := by fin_cases p <;> decide +kernel

private theorem transition_check_100 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 100) (generatorPermutation s p) =
      generatorPermutation s (rowForward 100 p) := by
  decide +kernel

private theorem code_encoding_100 :
    code 100 = ∑ p : Fin 12, (rowForward 100 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_100 : code 100 < code 101 := by
  decide +kernel

private theorem row_image_101 (p : Fin 12) :
    (rows 101).val p = rowForward 101 p := by
  calc
    (rows 101).val p = rowPoint 101 p := (rowPoint_eq 101 p).symm
    _ = rowForward 101 p := by fin_cases p <;> decide +kernel

private theorem transition_check_101 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 101) (generatorPermutation s p) =
      generatorPermutation s (rowForward 101 p) := by
  decide +kernel

private theorem code_encoding_101 :
    code 101 = ∑ p : Fin 12, (rowForward 101 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_101 : code 101 < code 102 := by
  decide +kernel

private theorem row_image_102 (p : Fin 12) :
    (rows 102).val p = rowForward 102 p := by
  calc
    (rows 102).val p = rowPoint 102 p := (rowPoint_eq 102 p).symm
    _ = rowForward 102 p := by fin_cases p <;> decide +kernel

private theorem transition_check_102 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 102) (generatorPermutation s p) =
      generatorPermutation s (rowForward 102 p) := by
  decide +kernel

private theorem code_encoding_102 :
    code 102 = ∑ p : Fin 12, (rowForward 102 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_102 : code 102 < code 103 := by
  decide +kernel

private theorem row_image_103 (p : Fin 12) :
    (rows 103).val p = rowForward 103 p := by
  calc
    (rows 103).val p = rowPoint 103 p := (rowPoint_eq 103 p).symm
    _ = rowForward 103 p := by fin_cases p <;> decide +kernel

private theorem transition_check_103 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 103) (generatorPermutation s p) =
      generatorPermutation s (rowForward 103 p) := by
  decide +kernel

private theorem code_encoding_103 :
    code 103 = ∑ p : Fin 12, (rowForward 103 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_103 : code 103 < code 104 := by
  decide +kernel

private theorem row_image_104 (p : Fin 12) :
    (rows 104).val p = rowForward 104 p := by
  calc
    (rows 104).val p = rowPoint 104 p := (rowPoint_eq 104 p).symm
    _ = rowForward 104 p := by fin_cases p <;> decide +kernel

private theorem transition_check_104 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 104) (generatorPermutation s p) =
      generatorPermutation s (rowForward 104 p) := by
  decide +kernel

private theorem code_encoding_104 :
    code 104 = ∑ p : Fin 12, (rowForward 104 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_104 : code 104 < code 105 := by
  decide +kernel

private theorem row_image_105 (p : Fin 12) :
    (rows 105).val p = rowForward 105 p := by
  calc
    (rows 105).val p = rowPoint 105 p := (rowPoint_eq 105 p).symm
    _ = rowForward 105 p := by fin_cases p <;> decide +kernel

private theorem transition_check_105 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 105) (generatorPermutation s p) =
      generatorPermutation s (rowForward 105 p) := by
  decide +kernel

private theorem code_encoding_105 :
    code 105 = ∑ p : Fin 12, (rowForward 105 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_105 : code 105 < code 106 := by
  decide +kernel

private theorem row_image_106 (p : Fin 12) :
    (rows 106).val p = rowForward 106 p := by
  calc
    (rows 106).val p = rowPoint 106 p := (rowPoint_eq 106 p).symm
    _ = rowForward 106 p := by fin_cases p <;> decide +kernel

private theorem transition_check_106 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 106) (generatorPermutation s p) =
      generatorPermutation s (rowForward 106 p) := by
  decide +kernel

private theorem code_encoding_106 :
    code 106 = ∑ p : Fin 12, (rowForward 106 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_106 : code 106 < code 107 := by
  decide +kernel

private theorem row_image_107 (p : Fin 12) :
    (rows 107).val p = rowForward 107 p := by
  calc
    (rows 107).val p = rowPoint 107 p := (rowPoint_eq 107 p).symm
    _ = rowForward 107 p := by fin_cases p <;> decide +kernel

private theorem transition_check_107 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 107) (generatorPermutation s p) =
      generatorPermutation s (rowForward 107 p) := by
  decide +kernel

private theorem code_encoding_107 :
    code 107 = ∑ p : Fin 12, (rowForward 107 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_107 : code 107 < code 108 := by
  decide +kernel

private theorem row_image_108 (p : Fin 12) :
    (rows 108).val p = rowForward 108 p := by
  calc
    (rows 108).val p = rowPoint 108 p := (rowPoint_eq 108 p).symm
    _ = rowForward 108 p := by fin_cases p <;> decide +kernel

private theorem transition_check_108 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 108) (generatorPermutation s p) =
      generatorPermutation s (rowForward 108 p) := by
  decide +kernel

private theorem code_encoding_108 :
    code 108 = ∑ p : Fin 12, (rowForward 108 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_108 : code 108 < code 109 := by
  decide +kernel

private theorem row_image_109 (p : Fin 12) :
    (rows 109).val p = rowForward 109 p := by
  calc
    (rows 109).val p = rowPoint 109 p := (rowPoint_eq 109 p).symm
    _ = rowForward 109 p := by fin_cases p <;> decide +kernel

private theorem transition_check_109 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 109) (generatorPermutation s p) =
      generatorPermutation s (rowForward 109 p) := by
  decide +kernel

private theorem code_encoding_109 :
    code 109 = ∑ p : Fin 12, (rowForward 109 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_109 : code 109 < code 110 := by
  decide +kernel

private theorem row_image_110 (p : Fin 12) :
    (rows 110).val p = rowForward 110 p := by
  calc
    (rows 110).val p = rowPoint 110 p := (rowPoint_eq 110 p).symm
    _ = rowForward 110 p := by fin_cases p <;> decide +kernel

private theorem transition_check_110 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 110) (generatorPermutation s p) =
      generatorPermutation s (rowForward 110 p) := by
  decide +kernel

private theorem code_encoding_110 :
    code 110 = ∑ p : Fin 12, (rowForward 110 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_110 : code 110 < code 111 := by
  decide +kernel

private theorem row_image_111 (p : Fin 12) :
    (rows 111).val p = rowForward 111 p := by
  calc
    (rows 111).val p = rowPoint 111 p := (rowPoint_eq 111 p).symm
    _ = rowForward 111 p := by fin_cases p <;> decide +kernel

private theorem transition_check_111 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 111) (generatorPermutation s p) =
      generatorPermutation s (rowForward 111 p) := by
  decide +kernel

private theorem code_encoding_111 :
    code 111 = ∑ p : Fin 12, (rowForward 111 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_111 : code 111 < code 112 := by
  decide +kernel

private theorem row_image_112 (p : Fin 12) :
    (rows 112).val p = rowForward 112 p := by
  calc
    (rows 112).val p = rowPoint 112 p := (rowPoint_eq 112 p).symm
    _ = rowForward 112 p := by fin_cases p <;> decide +kernel

private theorem transition_check_112 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 112) (generatorPermutation s p) =
      generatorPermutation s (rowForward 112 p) := by
  decide +kernel

private theorem code_encoding_112 :
    code 112 = ∑ p : Fin 12, (rowForward 112 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_112 : code 112 < code 113 := by
  decide +kernel

private theorem row_image_113 (p : Fin 12) :
    (rows 113).val p = rowForward 113 p := by
  calc
    (rows 113).val p = rowPoint 113 p := (rowPoint_eq 113 p).symm
    _ = rowForward 113 p := by fin_cases p <;> decide +kernel

private theorem transition_check_113 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 113) (generatorPermutation s p) =
      generatorPermutation s (rowForward 113 p) := by
  decide +kernel

private theorem code_encoding_113 :
    code 113 = ∑ p : Fin 12, (rowForward 113 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_113 : code 113 < code 114 := by
  decide +kernel

private theorem row_image_114 (p : Fin 12) :
    (rows 114).val p = rowForward 114 p := by
  calc
    (rows 114).val p = rowPoint 114 p := (rowPoint_eq 114 p).symm
    _ = rowForward 114 p := by fin_cases p <;> decide +kernel

private theorem transition_check_114 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 114) (generatorPermutation s p) =
      generatorPermutation s (rowForward 114 p) := by
  decide +kernel

private theorem code_encoding_114 :
    code 114 = ∑ p : Fin 12, (rowForward 114 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_114 : code 114 < code 115 := by
  decide +kernel

private theorem row_image_115 (p : Fin 12) :
    (rows 115).val p = rowForward 115 p := by
  calc
    (rows 115).val p = rowPoint 115 p := (rowPoint_eq 115 p).symm
    _ = rowForward 115 p := by fin_cases p <;> decide +kernel

private theorem transition_check_115 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 115) (generatorPermutation s p) =
      generatorPermutation s (rowForward 115 p) := by
  decide +kernel

private theorem code_encoding_115 :
    code 115 = ∑ p : Fin 12, (rowForward 115 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_115 : code 115 < code 116 := by
  decide +kernel

private theorem row_image_116 (p : Fin 12) :
    (rows 116).val p = rowForward 116 p := by
  calc
    (rows 116).val p = rowPoint 116 p := (rowPoint_eq 116 p).symm
    _ = rowForward 116 p := by fin_cases p <;> decide +kernel

private theorem transition_check_116 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 116) (generatorPermutation s p) =
      generatorPermutation s (rowForward 116 p) := by
  decide +kernel

private theorem code_encoding_116 :
    code 116 = ∑ p : Fin 12, (rowForward 116 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_116 : code 116 < code 117 := by
  decide +kernel

private theorem row_image_117 (p : Fin 12) :
    (rows 117).val p = rowForward 117 p := by
  calc
    (rows 117).val p = rowPoint 117 p := (rowPoint_eq 117 p).symm
    _ = rowForward 117 p := by fin_cases p <;> decide +kernel

private theorem transition_check_117 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 117) (generatorPermutation s p) =
      generatorPermutation s (rowForward 117 p) := by
  decide +kernel

private theorem code_encoding_117 :
    code 117 = ∑ p : Fin 12, (rowForward 117 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_117 : code 117 < code 118 := by
  decide +kernel

private theorem row_image_118 (p : Fin 12) :
    (rows 118).val p = rowForward 118 p := by
  calc
    (rows 118).val p = rowPoint 118 p := (rowPoint_eq 118 p).symm
    _ = rowForward 118 p := by fin_cases p <;> decide +kernel

private theorem transition_check_118 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 118) (generatorPermutation s p) =
      generatorPermutation s (rowForward 118 p) := by
  decide +kernel

private theorem code_encoding_118 :
    code 118 = ∑ p : Fin 12, (rowForward 118 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_118 : code 118 < code 119 := by
  decide +kernel

private theorem row_image_119 (p : Fin 12) :
    (rows 119).val p = rowForward 119 p := by
  calc
    (rows 119).val p = rowPoint 119 p := (rowPoint_eq 119 p).symm
    _ = rowForward 119 p := by fin_cases p <;> decide +kernel

private theorem transition_check_119 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 119) (generatorPermutation s p) =
      generatorPermutation s (rowForward 119 p) := by
  decide +kernel

private theorem code_encoding_119 :
    code 119 = ∑ p : Fin 12, (rowForward 119 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_119 : code 119 < code 120 := by
  decide +kernel

private theorem row_image_120 (p : Fin 12) :
    (rows 120).val p = rowForward 120 p := by
  calc
    (rows 120).val p = rowPoint 120 p := (rowPoint_eq 120 p).symm
    _ = rowForward 120 p := by fin_cases p <;> decide +kernel

private theorem transition_check_120 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 120) (generatorPermutation s p) =
      generatorPermutation s (rowForward 120 p) := by
  decide +kernel

private theorem code_encoding_120 :
    code 120 = ∑ p : Fin 12, (rowForward 120 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_120 : code 120 < code 121 := by
  decide +kernel

private theorem row_image_121 (p : Fin 12) :
    (rows 121).val p = rowForward 121 p := by
  calc
    (rows 121).val p = rowPoint 121 p := (rowPoint_eq 121 p).symm
    _ = rowForward 121 p := by fin_cases p <;> decide +kernel

private theorem transition_check_121 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 121) (generatorPermutation s p) =
      generatorPermutation s (rowForward 121 p) := by
  decide +kernel

private theorem code_encoding_121 :
    code 121 = ∑ p : Fin 12, (rowForward 121 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_121 : code 121 < code 122 := by
  decide +kernel

private theorem row_image_122 (p : Fin 12) :
    (rows 122).val p = rowForward 122 p := by
  calc
    (rows 122).val p = rowPoint 122 p := (rowPoint_eq 122 p).symm
    _ = rowForward 122 p := by fin_cases p <;> decide +kernel

private theorem transition_check_122 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 122) (generatorPermutation s p) =
      generatorPermutation s (rowForward 122 p) := by
  decide +kernel

private theorem code_encoding_122 :
    code 122 = ∑ p : Fin 12, (rowForward 122 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_122 : code 122 < code 123 := by
  decide +kernel

private theorem row_image_123 (p : Fin 12) :
    (rows 123).val p = rowForward 123 p := by
  calc
    (rows 123).val p = rowPoint 123 p := (rowPoint_eq 123 p).symm
    _ = rowForward 123 p := by fin_cases p <;> decide +kernel

private theorem transition_check_123 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 123) (generatorPermutation s p) =
      generatorPermutation s (rowForward 123 p) := by
  decide +kernel

private theorem code_encoding_123 :
    code 123 = ∑ p : Fin 12, (rowForward 123 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_123 : code 123 < code 124 := by
  decide +kernel

private theorem row_image_124 (p : Fin 12) :
    (rows 124).val p = rowForward 124 p := by
  calc
    (rows 124).val p = rowPoint 124 p := (rowPoint_eq 124 p).symm
    _ = rowForward 124 p := by fin_cases p <;> decide +kernel

private theorem transition_check_124 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 124) (generatorPermutation s p) =
      generatorPermutation s (rowForward 124 p) := by
  decide +kernel

private theorem code_encoding_124 :
    code 124 = ∑ p : Fin 12, (rowForward 124 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_124 : code 124 < code 125 := by
  decide +kernel

private theorem row_image_125 (p : Fin 12) :
    (rows 125).val p = rowForward 125 p := by
  calc
    (rows 125).val p = rowPoint 125 p := (rowPoint_eq 125 p).symm
    _ = rowForward 125 p := by fin_cases p <;> decide +kernel

private theorem transition_check_125 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 125) (generatorPermutation s p) =
      generatorPermutation s (rowForward 125 p) := by
  decide +kernel

private theorem code_encoding_125 :
    code 125 = ∑ p : Fin 12, (rowForward 125 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_125 : code 125 < code 126 := by
  decide +kernel

private theorem row_image_126 (p : Fin 12) :
    (rows 126).val p = rowForward 126 p := by
  calc
    (rows 126).val p = rowPoint 126 p := (rowPoint_eq 126 p).symm
    _ = rowForward 126 p := by fin_cases p <;> decide +kernel

private theorem transition_check_126 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 126) (generatorPermutation s p) =
      generatorPermutation s (rowForward 126 p) := by
  decide +kernel

private theorem code_encoding_126 :
    code 126 = ∑ p : Fin 12, (rowForward 126 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_126 : code 126 < code 127 := by
  decide +kernel

private theorem row_image_127 (p : Fin 12) :
    (rows 127).val p = rowForward 127 p := by
  calc
    (rows 127).val p = rowPoint 127 p := (rowPoint_eq 127 p).symm
    _ = rowForward 127 p := by fin_cases p <;> decide +kernel

private theorem transition_check_127 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 127) (generatorPermutation s p) =
      generatorPermutation s (rowForward 127 p) := by
  decide +kernel

private theorem code_encoding_127 :
    code 127 = ∑ p : Fin 12, (rowForward 127 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_127 : code 127 < code 128 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (96 : Fin 495) from rfl))
      (row_image_96 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (97 : Fin 495) from rfl))
      (row_image_97 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (98 : Fin 495) from rfl))
      (row_image_98 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (99 : Fin 495) from rfl))
      (row_image_99 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (100 : Fin 495) from rfl))
      (row_image_100 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (101 : Fin 495) from rfl))
      (row_image_101 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (102 : Fin 495) from rfl))
      (row_image_102 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (103 : Fin 495) from rfl))
      (row_image_103 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (104 : Fin 495) from rfl))
      (row_image_104 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (105 : Fin 495) from rfl))
      (row_image_105 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (106 : Fin 495) from rfl))
      (row_image_106 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (107 : Fin 495) from rfl))
      (row_image_107 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (108 : Fin 495) from rfl))
      (row_image_108 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (109 : Fin 495) from rfl))
      (row_image_109 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (110 : Fin 495) from rfl))
      (row_image_110 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (111 : Fin 495) from rfl))
      (row_image_111 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (112 : Fin 495) from rfl))
      (row_image_112 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (113 : Fin 495) from rfl))
      (row_image_113 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (114 : Fin 495) from rfl))
      (row_image_114 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (115 : Fin 495) from rfl))
      (row_image_115 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (116 : Fin 495) from rfl))
      (row_image_116 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (117 : Fin 495) from rfl))
      (row_image_117 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (118 : Fin 495) from rfl))
      (row_image_118 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (119 : Fin 495) from rfl))
      (row_image_119 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (120 : Fin 495) from rfl))
      (row_image_120 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (121 : Fin 495) from rfl))
      (row_image_121 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (122 : Fin 495) from rfl))
      (row_image_122 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (123 : Fin 495) from rfl))
      (row_image_123 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (124 : Fin 495) from rfl))
      (row_image_124 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (125 : Fin 495) from rfl))
      (row_image_125 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (126 : Fin 495) from rfl))
      (row_image_126 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (127 : Fin 495) from rfl))
      (row_image_127 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (96 : Fin 495) from rfl))
      (transition_check_96 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (97 : Fin 495) from rfl))
      (transition_check_97 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (98 : Fin 495) from rfl))
      (transition_check_98 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (99 : Fin 495) from rfl))
      (transition_check_99 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (100 : Fin 495) from rfl))
      (transition_check_100 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (101 : Fin 495) from rfl))
      (transition_check_101 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (102 : Fin 495) from rfl))
      (transition_check_102 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (103 : Fin 495) from rfl))
      (transition_check_103 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (104 : Fin 495) from rfl))
      (transition_check_104 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (105 : Fin 495) from rfl))
      (transition_check_105 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (106 : Fin 495) from rfl))
      (transition_check_106 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (107 : Fin 495) from rfl))
      (transition_check_107 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (108 : Fin 495) from rfl))
      (transition_check_108 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (109 : Fin 495) from rfl))
      (transition_check_109 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (110 : Fin 495) from rfl))
      (transition_check_110 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (111 : Fin 495) from rfl))
      (transition_check_111 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (112 : Fin 495) from rfl))
      (transition_check_112 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (113 : Fin 495) from rfl))
      (transition_check_113 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (114 : Fin 495) from rfl))
      (transition_check_114 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (115 : Fin 495) from rfl))
      (transition_check_115 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (116 : Fin 495) from rfl))
      (transition_check_116 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (117 : Fin 495) from rfl))
      (transition_check_117 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (118 : Fin 495) from rfl))
      (transition_check_118 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (119 : Fin 495) from rfl))
      (transition_check_119 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (120 : Fin 495) from rfl))
      (transition_check_120 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (121 : Fin 495) from rfl))
      (transition_check_121 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (122 : Fin 495) from rfl))
      (transition_check_122 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (123 : Fin 495) from rfl))
      (transition_check_123 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (124 : Fin 495) from rfl))
      (transition_check_124 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (125 : Fin 495) from rfl))
      (transition_check_125 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (126 : Fin 495) from rfl))
      (transition_check_126 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (127 : Fin 495) from rfl))
      (transition_check_127 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (96 : Fin 495) from rfl))
      code_encoding_96
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (97 : Fin 495) from rfl))
      code_encoding_97
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (98 : Fin 495) from rfl))
      code_encoding_98
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (99 : Fin 495) from rfl))
      code_encoding_99
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (100 : Fin 495) from rfl))
      code_encoding_100
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (101 : Fin 495) from rfl))
      code_encoding_101
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (102 : Fin 495) from rfl))
      code_encoding_102
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (103 : Fin 495) from rfl))
      code_encoding_103
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (104 : Fin 495) from rfl))
      code_encoding_104
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (105 : Fin 495) from rfl))
      code_encoding_105
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (106 : Fin 495) from rfl))
      code_encoding_106
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (107 : Fin 495) from rfl))
      code_encoding_107
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (108 : Fin 495) from rfl))
      code_encoding_108
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (109 : Fin 495) from rfl))
      code_encoding_109
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (110 : Fin 495) from rfl))
      code_encoding_110
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (111 : Fin 495) from rfl))
      code_encoding_111
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (112 : Fin 495) from rfl))
      code_encoding_112
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (113 : Fin 495) from rfl))
      code_encoding_113
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (114 : Fin 495) from rfl))
      code_encoding_114
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (115 : Fin 495) from rfl))
      code_encoding_115
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (116 : Fin 495) from rfl))
      code_encoding_116
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (117 : Fin 495) from rfl))
      code_encoding_117
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (118 : Fin 495) from rfl))
      code_encoding_118
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (119 : Fin 495) from rfl))
      code_encoding_119
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (120 : Fin 495) from rfl))
      code_encoding_120
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (121 : Fin 495) from rfl))
      code_encoding_121
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (122 : Fin 495) from rfl))
      code_encoding_122
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (123 : Fin 495) from rfl))
      code_encoding_123
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (124 : Fin 495) from rfl))
      code_encoding_124
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (125 : Fin 495) from rfl))
      code_encoding_125
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (126 : Fin 495) from rfl))
      code_encoding_126
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (127 : Fin 495) from rfl))
      code_encoding_127

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (96 : Fin 495) from rfl))
    intro h
    exact code_adjacent_96
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (97 : Fin 495) from rfl))
    intro h
    exact code_adjacent_97
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (98 : Fin 495) from rfl))
    intro h
    exact code_adjacent_98
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (99 : Fin 495) from rfl))
    intro h
    exact code_adjacent_99
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (100 : Fin 495) from rfl))
    intro h
    exact code_adjacent_100
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (101 : Fin 495) from rfl))
    intro h
    exact code_adjacent_101
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (102 : Fin 495) from rfl))
    intro h
    exact code_adjacent_102
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (103 : Fin 495) from rfl))
    intro h
    exact code_adjacent_103
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (104 : Fin 495) from rfl))
    intro h
    exact code_adjacent_104
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (105 : Fin 495) from rfl))
    intro h
    exact code_adjacent_105
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (106 : Fin 495) from rfl))
    intro h
    exact code_adjacent_106
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (107 : Fin 495) from rfl))
    intro h
    exact code_adjacent_107
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (108 : Fin 495) from rfl))
    intro h
    exact code_adjacent_108
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (109 : Fin 495) from rfl))
    intro h
    exact code_adjacent_109
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (110 : Fin 495) from rfl))
    intro h
    exact code_adjacent_110
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (111 : Fin 495) from rfl))
    intro h
    exact code_adjacent_111
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (112 : Fin 495) from rfl))
    intro h
    exact code_adjacent_112
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (113 : Fin 495) from rfl))
    intro h
    exact code_adjacent_113
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (114 : Fin 495) from rfl))
    intro h
    exact code_adjacent_114
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (115 : Fin 495) from rfl))
    intro h
    exact code_adjacent_115
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (116 : Fin 495) from rfl))
    intro h
    exact code_adjacent_116
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (117 : Fin 495) from rfl))
    intro h
    exact code_adjacent_117
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (118 : Fin 495) from rfl))
    intro h
    exact code_adjacent_118
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (119 : Fin 495) from rfl))
    intro h
    exact code_adjacent_119
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (120 : Fin 495) from rfl))
    intro h
    exact code_adjacent_120
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (121 : Fin 495) from rfl))
    intro h
    exact code_adjacent_121
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (122 : Fin 495) from rfl))
    intro h
    exact code_adjacent_122
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (123 : Fin 495) from rfl))
    intro h
    exact code_adjacent_123
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (124 : Fin 495) from rfl))
    intro h
    exact code_adjacent_124
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (125 : Fin 495) from rfl))
    intro h
    exact code_adjacent_125
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (126 : Fin 495) from rfl))
    intro h
    exact code_adjacent_126
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (127 : Fin 495) from rfl))
    intro h
    exact code_adjacent_127

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock03
