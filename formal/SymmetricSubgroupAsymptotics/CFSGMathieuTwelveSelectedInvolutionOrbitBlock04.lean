import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows128..159.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock04
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨128+i.val,by omega⟩

private theorem row_image_128 (p : Fin 12) :
    (rows 128).val p = rowForward 128 p := by
  calc
    (rows 128).val p = rowPoint 128 p := (rowPoint_eq 128 p).symm
    _ = rowForward 128 p := by fin_cases p <;> decide +kernel

private theorem transition_check_128 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 128) (generatorPermutation s p) =
      generatorPermutation s (rowForward 128 p) := by
  decide +kernel

private theorem code_encoding_128 :
    code 128 = ∑ p : Fin 12, (rowForward 128 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_128 : code 128 < code 129 := by
  decide +kernel

private theorem row_image_129 (p : Fin 12) :
    (rows 129).val p = rowForward 129 p := by
  calc
    (rows 129).val p = rowPoint 129 p := (rowPoint_eq 129 p).symm
    _ = rowForward 129 p := by fin_cases p <;> decide +kernel

private theorem transition_check_129 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 129) (generatorPermutation s p) =
      generatorPermutation s (rowForward 129 p) := by
  decide +kernel

private theorem code_encoding_129 :
    code 129 = ∑ p : Fin 12, (rowForward 129 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_129 : code 129 < code 130 := by
  decide +kernel

private theorem row_image_130 (p : Fin 12) :
    (rows 130).val p = rowForward 130 p := by
  calc
    (rows 130).val p = rowPoint 130 p := (rowPoint_eq 130 p).symm
    _ = rowForward 130 p := by fin_cases p <;> decide +kernel

private theorem transition_check_130 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 130) (generatorPermutation s p) =
      generatorPermutation s (rowForward 130 p) := by
  decide +kernel

private theorem code_encoding_130 :
    code 130 = ∑ p : Fin 12, (rowForward 130 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_130 : code 130 < code 131 := by
  decide +kernel

private theorem row_image_131 (p : Fin 12) :
    (rows 131).val p = rowForward 131 p := by
  calc
    (rows 131).val p = rowPoint 131 p := (rowPoint_eq 131 p).symm
    _ = rowForward 131 p := by fin_cases p <;> decide +kernel

private theorem transition_check_131 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 131) (generatorPermutation s p) =
      generatorPermutation s (rowForward 131 p) := by
  decide +kernel

private theorem code_encoding_131 :
    code 131 = ∑ p : Fin 12, (rowForward 131 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_131 : code 131 < code 132 := by
  decide +kernel

private theorem row_image_132 (p : Fin 12) :
    (rows 132).val p = rowForward 132 p := by
  calc
    (rows 132).val p = rowPoint 132 p := (rowPoint_eq 132 p).symm
    _ = rowForward 132 p := by fin_cases p <;> decide +kernel

private theorem transition_check_132 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 132) (generatorPermutation s p) =
      generatorPermutation s (rowForward 132 p) := by
  decide +kernel

private theorem code_encoding_132 :
    code 132 = ∑ p : Fin 12, (rowForward 132 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_132 : code 132 < code 133 := by
  decide +kernel

private theorem row_image_133 (p : Fin 12) :
    (rows 133).val p = rowForward 133 p := by
  calc
    (rows 133).val p = rowPoint 133 p := (rowPoint_eq 133 p).symm
    _ = rowForward 133 p := by fin_cases p <;> decide +kernel

private theorem transition_check_133 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 133) (generatorPermutation s p) =
      generatorPermutation s (rowForward 133 p) := by
  decide +kernel

private theorem code_encoding_133 :
    code 133 = ∑ p : Fin 12, (rowForward 133 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_133 : code 133 < code 134 := by
  decide +kernel

private theorem row_image_134 (p : Fin 12) :
    (rows 134).val p = rowForward 134 p := by
  calc
    (rows 134).val p = rowPoint 134 p := (rowPoint_eq 134 p).symm
    _ = rowForward 134 p := by fin_cases p <;> decide +kernel

private theorem transition_check_134 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 134) (generatorPermutation s p) =
      generatorPermutation s (rowForward 134 p) := by
  decide +kernel

private theorem code_encoding_134 :
    code 134 = ∑ p : Fin 12, (rowForward 134 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_134 : code 134 < code 135 := by
  decide +kernel

private theorem row_image_135 (p : Fin 12) :
    (rows 135).val p = rowForward 135 p := by
  calc
    (rows 135).val p = rowPoint 135 p := (rowPoint_eq 135 p).symm
    _ = rowForward 135 p := by fin_cases p <;> decide +kernel

private theorem transition_check_135 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 135) (generatorPermutation s p) =
      generatorPermutation s (rowForward 135 p) := by
  decide +kernel

private theorem code_encoding_135 :
    code 135 = ∑ p : Fin 12, (rowForward 135 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_135 : code 135 < code 136 := by
  decide +kernel

private theorem row_image_136 (p : Fin 12) :
    (rows 136).val p = rowForward 136 p := by
  calc
    (rows 136).val p = rowPoint 136 p := (rowPoint_eq 136 p).symm
    _ = rowForward 136 p := by fin_cases p <;> decide +kernel

private theorem transition_check_136 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 136) (generatorPermutation s p) =
      generatorPermutation s (rowForward 136 p) := by
  decide +kernel

private theorem code_encoding_136 :
    code 136 = ∑ p : Fin 12, (rowForward 136 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_136 : code 136 < code 137 := by
  decide +kernel

private theorem row_image_137 (p : Fin 12) :
    (rows 137).val p = rowForward 137 p := by
  calc
    (rows 137).val p = rowPoint 137 p := (rowPoint_eq 137 p).symm
    _ = rowForward 137 p := by fin_cases p <;> decide +kernel

private theorem transition_check_137 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 137) (generatorPermutation s p) =
      generatorPermutation s (rowForward 137 p) := by
  decide +kernel

private theorem code_encoding_137 :
    code 137 = ∑ p : Fin 12, (rowForward 137 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_137 : code 137 < code 138 := by
  decide +kernel

private theorem row_image_138 (p : Fin 12) :
    (rows 138).val p = rowForward 138 p := by
  calc
    (rows 138).val p = rowPoint 138 p := (rowPoint_eq 138 p).symm
    _ = rowForward 138 p := by fin_cases p <;> decide +kernel

private theorem transition_check_138 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 138) (generatorPermutation s p) =
      generatorPermutation s (rowForward 138 p) := by
  decide +kernel

private theorem code_encoding_138 :
    code 138 = ∑ p : Fin 12, (rowForward 138 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_138 : code 138 < code 139 := by
  decide +kernel

private theorem row_image_139 (p : Fin 12) :
    (rows 139).val p = rowForward 139 p := by
  calc
    (rows 139).val p = rowPoint 139 p := (rowPoint_eq 139 p).symm
    _ = rowForward 139 p := by fin_cases p <;> decide +kernel

private theorem transition_check_139 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 139) (generatorPermutation s p) =
      generatorPermutation s (rowForward 139 p) := by
  decide +kernel

private theorem code_encoding_139 :
    code 139 = ∑ p : Fin 12, (rowForward 139 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_139 : code 139 < code 140 := by
  decide +kernel

private theorem row_image_140 (p : Fin 12) :
    (rows 140).val p = rowForward 140 p := by
  calc
    (rows 140).val p = rowPoint 140 p := (rowPoint_eq 140 p).symm
    _ = rowForward 140 p := by fin_cases p <;> decide +kernel

private theorem transition_check_140 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 140) (generatorPermutation s p) =
      generatorPermutation s (rowForward 140 p) := by
  decide +kernel

private theorem code_encoding_140 :
    code 140 = ∑ p : Fin 12, (rowForward 140 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_140 : code 140 < code 141 := by
  decide +kernel

private theorem row_image_141 (p : Fin 12) :
    (rows 141).val p = rowForward 141 p := by
  calc
    (rows 141).val p = rowPoint 141 p := (rowPoint_eq 141 p).symm
    _ = rowForward 141 p := by fin_cases p <;> decide +kernel

private theorem transition_check_141 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 141) (generatorPermutation s p) =
      generatorPermutation s (rowForward 141 p) := by
  decide +kernel

private theorem code_encoding_141 :
    code 141 = ∑ p : Fin 12, (rowForward 141 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_141 : code 141 < code 142 := by
  decide +kernel

private theorem row_image_142 (p : Fin 12) :
    (rows 142).val p = rowForward 142 p := by
  calc
    (rows 142).val p = rowPoint 142 p := (rowPoint_eq 142 p).symm
    _ = rowForward 142 p := by fin_cases p <;> decide +kernel

private theorem transition_check_142 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 142) (generatorPermutation s p) =
      generatorPermutation s (rowForward 142 p) := by
  decide +kernel

private theorem code_encoding_142 :
    code 142 = ∑ p : Fin 12, (rowForward 142 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_142 : code 142 < code 143 := by
  decide +kernel

private theorem row_image_143 (p : Fin 12) :
    (rows 143).val p = rowForward 143 p := by
  calc
    (rows 143).val p = rowPoint 143 p := (rowPoint_eq 143 p).symm
    _ = rowForward 143 p := by fin_cases p <;> decide +kernel

private theorem transition_check_143 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 143) (generatorPermutation s p) =
      generatorPermutation s (rowForward 143 p) := by
  decide +kernel

private theorem code_encoding_143 :
    code 143 = ∑ p : Fin 12, (rowForward 143 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_143 : code 143 < code 144 := by
  decide +kernel

private theorem row_image_144 (p : Fin 12) :
    (rows 144).val p = rowForward 144 p := by
  calc
    (rows 144).val p = rowPoint 144 p := (rowPoint_eq 144 p).symm
    _ = rowForward 144 p := by fin_cases p <;> decide +kernel

private theorem transition_check_144 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 144) (generatorPermutation s p) =
      generatorPermutation s (rowForward 144 p) := by
  decide +kernel

private theorem code_encoding_144 :
    code 144 = ∑ p : Fin 12, (rowForward 144 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_144 : code 144 < code 145 := by
  decide +kernel

private theorem row_image_145 (p : Fin 12) :
    (rows 145).val p = rowForward 145 p := by
  calc
    (rows 145).val p = rowPoint 145 p := (rowPoint_eq 145 p).symm
    _ = rowForward 145 p := by fin_cases p <;> decide +kernel

private theorem transition_check_145 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 145) (generatorPermutation s p) =
      generatorPermutation s (rowForward 145 p) := by
  decide +kernel

private theorem code_encoding_145 :
    code 145 = ∑ p : Fin 12, (rowForward 145 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_145 : code 145 < code 146 := by
  decide +kernel

private theorem row_image_146 (p : Fin 12) :
    (rows 146).val p = rowForward 146 p := by
  calc
    (rows 146).val p = rowPoint 146 p := (rowPoint_eq 146 p).symm
    _ = rowForward 146 p := by fin_cases p <;> decide +kernel

private theorem transition_check_146 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 146) (generatorPermutation s p) =
      generatorPermutation s (rowForward 146 p) := by
  decide +kernel

private theorem code_encoding_146 :
    code 146 = ∑ p : Fin 12, (rowForward 146 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_146 : code 146 < code 147 := by
  decide +kernel

private theorem row_image_147 (p : Fin 12) :
    (rows 147).val p = rowForward 147 p := by
  calc
    (rows 147).val p = rowPoint 147 p := (rowPoint_eq 147 p).symm
    _ = rowForward 147 p := by fin_cases p <;> decide +kernel

private theorem transition_check_147 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 147) (generatorPermutation s p) =
      generatorPermutation s (rowForward 147 p) := by
  decide +kernel

private theorem code_encoding_147 :
    code 147 = ∑ p : Fin 12, (rowForward 147 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_147 : code 147 < code 148 := by
  decide +kernel

private theorem row_image_148 (p : Fin 12) :
    (rows 148).val p = rowForward 148 p := by
  calc
    (rows 148).val p = rowPoint 148 p := (rowPoint_eq 148 p).symm
    _ = rowForward 148 p := by fin_cases p <;> decide +kernel

private theorem transition_check_148 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 148) (generatorPermutation s p) =
      generatorPermutation s (rowForward 148 p) := by
  decide +kernel

private theorem code_encoding_148 :
    code 148 = ∑ p : Fin 12, (rowForward 148 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_148 : code 148 < code 149 := by
  decide +kernel

private theorem row_image_149 (p : Fin 12) :
    (rows 149).val p = rowForward 149 p := by
  calc
    (rows 149).val p = rowPoint 149 p := (rowPoint_eq 149 p).symm
    _ = rowForward 149 p := by fin_cases p <;> decide +kernel

private theorem transition_check_149 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 149) (generatorPermutation s p) =
      generatorPermutation s (rowForward 149 p) := by
  decide +kernel

private theorem code_encoding_149 :
    code 149 = ∑ p : Fin 12, (rowForward 149 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_149 : code 149 < code 150 := by
  decide +kernel

private theorem row_image_150 (p : Fin 12) :
    (rows 150).val p = rowForward 150 p := by
  calc
    (rows 150).val p = rowPoint 150 p := (rowPoint_eq 150 p).symm
    _ = rowForward 150 p := by fin_cases p <;> decide +kernel

private theorem transition_check_150 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 150) (generatorPermutation s p) =
      generatorPermutation s (rowForward 150 p) := by
  decide +kernel

private theorem code_encoding_150 :
    code 150 = ∑ p : Fin 12, (rowForward 150 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_150 : code 150 < code 151 := by
  decide +kernel

private theorem row_image_151 (p : Fin 12) :
    (rows 151).val p = rowForward 151 p := by
  calc
    (rows 151).val p = rowPoint 151 p := (rowPoint_eq 151 p).symm
    _ = rowForward 151 p := by fin_cases p <;> decide +kernel

private theorem transition_check_151 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 151) (generatorPermutation s p) =
      generatorPermutation s (rowForward 151 p) := by
  decide +kernel

private theorem code_encoding_151 :
    code 151 = ∑ p : Fin 12, (rowForward 151 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_151 : code 151 < code 152 := by
  decide +kernel

private theorem row_image_152 (p : Fin 12) :
    (rows 152).val p = rowForward 152 p := by
  calc
    (rows 152).val p = rowPoint 152 p := (rowPoint_eq 152 p).symm
    _ = rowForward 152 p := by fin_cases p <;> decide +kernel

private theorem transition_check_152 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 152) (generatorPermutation s p) =
      generatorPermutation s (rowForward 152 p) := by
  decide +kernel

private theorem code_encoding_152 :
    code 152 = ∑ p : Fin 12, (rowForward 152 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_152 : code 152 < code 153 := by
  decide +kernel

private theorem row_image_153 (p : Fin 12) :
    (rows 153).val p = rowForward 153 p := by
  calc
    (rows 153).val p = rowPoint 153 p := (rowPoint_eq 153 p).symm
    _ = rowForward 153 p := by fin_cases p <;> decide +kernel

private theorem transition_check_153 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 153) (generatorPermutation s p) =
      generatorPermutation s (rowForward 153 p) := by
  decide +kernel

private theorem code_encoding_153 :
    code 153 = ∑ p : Fin 12, (rowForward 153 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_153 : code 153 < code 154 := by
  decide +kernel

private theorem row_image_154 (p : Fin 12) :
    (rows 154).val p = rowForward 154 p := by
  calc
    (rows 154).val p = rowPoint 154 p := (rowPoint_eq 154 p).symm
    _ = rowForward 154 p := by fin_cases p <;> decide +kernel

private theorem transition_check_154 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 154) (generatorPermutation s p) =
      generatorPermutation s (rowForward 154 p) := by
  decide +kernel

private theorem code_encoding_154 :
    code 154 = ∑ p : Fin 12, (rowForward 154 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_154 : code 154 < code 155 := by
  decide +kernel

private theorem row_image_155 (p : Fin 12) :
    (rows 155).val p = rowForward 155 p := by
  calc
    (rows 155).val p = rowPoint 155 p := (rowPoint_eq 155 p).symm
    _ = rowForward 155 p := by fin_cases p <;> decide +kernel

private theorem transition_check_155 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 155) (generatorPermutation s p) =
      generatorPermutation s (rowForward 155 p) := by
  decide +kernel

private theorem code_encoding_155 :
    code 155 = ∑ p : Fin 12, (rowForward 155 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_155 : code 155 < code 156 := by
  decide +kernel

private theorem row_image_156 (p : Fin 12) :
    (rows 156).val p = rowForward 156 p := by
  calc
    (rows 156).val p = rowPoint 156 p := (rowPoint_eq 156 p).symm
    _ = rowForward 156 p := by fin_cases p <;> decide +kernel

private theorem transition_check_156 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 156) (generatorPermutation s p) =
      generatorPermutation s (rowForward 156 p) := by
  decide +kernel

private theorem code_encoding_156 :
    code 156 = ∑ p : Fin 12, (rowForward 156 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_156 : code 156 < code 157 := by
  decide +kernel

private theorem row_image_157 (p : Fin 12) :
    (rows 157).val p = rowForward 157 p := by
  calc
    (rows 157).val p = rowPoint 157 p := (rowPoint_eq 157 p).symm
    _ = rowForward 157 p := by fin_cases p <;> decide +kernel

private theorem transition_check_157 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 157) (generatorPermutation s p) =
      generatorPermutation s (rowForward 157 p) := by
  decide +kernel

private theorem code_encoding_157 :
    code 157 = ∑ p : Fin 12, (rowForward 157 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_157 : code 157 < code 158 := by
  decide +kernel

private theorem row_image_158 (p : Fin 12) :
    (rows 158).val p = rowForward 158 p := by
  calc
    (rows 158).val p = rowPoint 158 p := (rowPoint_eq 158 p).symm
    _ = rowForward 158 p := by fin_cases p <;> decide +kernel

private theorem transition_check_158 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 158) (generatorPermutation s p) =
      generatorPermutation s (rowForward 158 p) := by
  decide +kernel

private theorem code_encoding_158 :
    code 158 = ∑ p : Fin 12, (rowForward 158 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_158 : code 158 < code 159 := by
  decide +kernel

private theorem row_image_159 (p : Fin 12) :
    (rows 159).val p = rowForward 159 p := by
  calc
    (rows 159).val p = rowPoint 159 p := (rowPoint_eq 159 p).symm
    _ = rowForward 159 p := by fin_cases p <;> decide +kernel

private theorem transition_check_159 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 159) (generatorPermutation s p) =
      generatorPermutation s (rowForward 159 p) := by
  decide +kernel

private theorem code_encoding_159 :
    code 159 = ∑ p : Fin 12, (rowForward 159 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_159 : code 159 < code 160 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (128 : Fin 495) from rfl))
      (row_image_128 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (129 : Fin 495) from rfl))
      (row_image_129 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (130 : Fin 495) from rfl))
      (row_image_130 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (131 : Fin 495) from rfl))
      (row_image_131 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (132 : Fin 495) from rfl))
      (row_image_132 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (133 : Fin 495) from rfl))
      (row_image_133 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (134 : Fin 495) from rfl))
      (row_image_134 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (135 : Fin 495) from rfl))
      (row_image_135 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (136 : Fin 495) from rfl))
      (row_image_136 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (137 : Fin 495) from rfl))
      (row_image_137 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (138 : Fin 495) from rfl))
      (row_image_138 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (139 : Fin 495) from rfl))
      (row_image_139 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (140 : Fin 495) from rfl))
      (row_image_140 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (141 : Fin 495) from rfl))
      (row_image_141 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (142 : Fin 495) from rfl))
      (row_image_142 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (143 : Fin 495) from rfl))
      (row_image_143 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (144 : Fin 495) from rfl))
      (row_image_144 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (145 : Fin 495) from rfl))
      (row_image_145 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (146 : Fin 495) from rfl))
      (row_image_146 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (147 : Fin 495) from rfl))
      (row_image_147 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (148 : Fin 495) from rfl))
      (row_image_148 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (149 : Fin 495) from rfl))
      (row_image_149 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (150 : Fin 495) from rfl))
      (row_image_150 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (151 : Fin 495) from rfl))
      (row_image_151 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (152 : Fin 495) from rfl))
      (row_image_152 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (153 : Fin 495) from rfl))
      (row_image_153 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (154 : Fin 495) from rfl))
      (row_image_154 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (155 : Fin 495) from rfl))
      (row_image_155 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (156 : Fin 495) from rfl))
      (row_image_156 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (157 : Fin 495) from rfl))
      (row_image_157 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (158 : Fin 495) from rfl))
      (row_image_158 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (159 : Fin 495) from rfl))
      (row_image_159 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (128 : Fin 495) from rfl))
      (transition_check_128 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (129 : Fin 495) from rfl))
      (transition_check_129 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (130 : Fin 495) from rfl))
      (transition_check_130 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (131 : Fin 495) from rfl))
      (transition_check_131 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (132 : Fin 495) from rfl))
      (transition_check_132 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (133 : Fin 495) from rfl))
      (transition_check_133 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (134 : Fin 495) from rfl))
      (transition_check_134 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (135 : Fin 495) from rfl))
      (transition_check_135 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (136 : Fin 495) from rfl))
      (transition_check_136 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (137 : Fin 495) from rfl))
      (transition_check_137 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (138 : Fin 495) from rfl))
      (transition_check_138 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (139 : Fin 495) from rfl))
      (transition_check_139 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (140 : Fin 495) from rfl))
      (transition_check_140 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (141 : Fin 495) from rfl))
      (transition_check_141 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (142 : Fin 495) from rfl))
      (transition_check_142 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (143 : Fin 495) from rfl))
      (transition_check_143 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (144 : Fin 495) from rfl))
      (transition_check_144 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (145 : Fin 495) from rfl))
      (transition_check_145 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (146 : Fin 495) from rfl))
      (transition_check_146 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (147 : Fin 495) from rfl))
      (transition_check_147 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (148 : Fin 495) from rfl))
      (transition_check_148 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (149 : Fin 495) from rfl))
      (transition_check_149 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (150 : Fin 495) from rfl))
      (transition_check_150 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (151 : Fin 495) from rfl))
      (transition_check_151 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (152 : Fin 495) from rfl))
      (transition_check_152 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (153 : Fin 495) from rfl))
      (transition_check_153 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (154 : Fin 495) from rfl))
      (transition_check_154 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (155 : Fin 495) from rfl))
      (transition_check_155 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (156 : Fin 495) from rfl))
      (transition_check_156 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (157 : Fin 495) from rfl))
      (transition_check_157 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (158 : Fin 495) from rfl))
      (transition_check_158 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (159 : Fin 495) from rfl))
      (transition_check_159 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (128 : Fin 495) from rfl))
      code_encoding_128
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (129 : Fin 495) from rfl))
      code_encoding_129
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (130 : Fin 495) from rfl))
      code_encoding_130
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (131 : Fin 495) from rfl))
      code_encoding_131
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (132 : Fin 495) from rfl))
      code_encoding_132
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (133 : Fin 495) from rfl))
      code_encoding_133
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (134 : Fin 495) from rfl))
      code_encoding_134
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (135 : Fin 495) from rfl))
      code_encoding_135
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (136 : Fin 495) from rfl))
      code_encoding_136
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (137 : Fin 495) from rfl))
      code_encoding_137
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (138 : Fin 495) from rfl))
      code_encoding_138
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (139 : Fin 495) from rfl))
      code_encoding_139
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (140 : Fin 495) from rfl))
      code_encoding_140
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (141 : Fin 495) from rfl))
      code_encoding_141
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (142 : Fin 495) from rfl))
      code_encoding_142
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (143 : Fin 495) from rfl))
      code_encoding_143
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (144 : Fin 495) from rfl))
      code_encoding_144
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (145 : Fin 495) from rfl))
      code_encoding_145
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (146 : Fin 495) from rfl))
      code_encoding_146
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (147 : Fin 495) from rfl))
      code_encoding_147
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (148 : Fin 495) from rfl))
      code_encoding_148
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (149 : Fin 495) from rfl))
      code_encoding_149
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (150 : Fin 495) from rfl))
      code_encoding_150
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (151 : Fin 495) from rfl))
      code_encoding_151
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (152 : Fin 495) from rfl))
      code_encoding_152
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (153 : Fin 495) from rfl))
      code_encoding_153
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (154 : Fin 495) from rfl))
      code_encoding_154
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (155 : Fin 495) from rfl))
      code_encoding_155
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (156 : Fin 495) from rfl))
      code_encoding_156
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (157 : Fin 495) from rfl))
      code_encoding_157
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (158 : Fin 495) from rfl))
      code_encoding_158
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (159 : Fin 495) from rfl))
      code_encoding_159

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (128 : Fin 495) from rfl))
    intro h
    exact code_adjacent_128
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (129 : Fin 495) from rfl))
    intro h
    exact code_adjacent_129
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (130 : Fin 495) from rfl))
    intro h
    exact code_adjacent_130
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (131 : Fin 495) from rfl))
    intro h
    exact code_adjacent_131
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (132 : Fin 495) from rfl))
    intro h
    exact code_adjacent_132
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (133 : Fin 495) from rfl))
    intro h
    exact code_adjacent_133
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (134 : Fin 495) from rfl))
    intro h
    exact code_adjacent_134
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (135 : Fin 495) from rfl))
    intro h
    exact code_adjacent_135
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (136 : Fin 495) from rfl))
    intro h
    exact code_adjacent_136
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (137 : Fin 495) from rfl))
    intro h
    exact code_adjacent_137
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (138 : Fin 495) from rfl))
    intro h
    exact code_adjacent_138
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (139 : Fin 495) from rfl))
    intro h
    exact code_adjacent_139
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (140 : Fin 495) from rfl))
    intro h
    exact code_adjacent_140
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (141 : Fin 495) from rfl))
    intro h
    exact code_adjacent_141
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (142 : Fin 495) from rfl))
    intro h
    exact code_adjacent_142
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (143 : Fin 495) from rfl))
    intro h
    exact code_adjacent_143
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (144 : Fin 495) from rfl))
    intro h
    exact code_adjacent_144
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (145 : Fin 495) from rfl))
    intro h
    exact code_adjacent_145
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (146 : Fin 495) from rfl))
    intro h
    exact code_adjacent_146
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (147 : Fin 495) from rfl))
    intro h
    exact code_adjacent_147
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (148 : Fin 495) from rfl))
    intro h
    exact code_adjacent_148
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (149 : Fin 495) from rfl))
    intro h
    exact code_adjacent_149
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (150 : Fin 495) from rfl))
    intro h
    exact code_adjacent_150
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (151 : Fin 495) from rfl))
    intro h
    exact code_adjacent_151
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (152 : Fin 495) from rfl))
    intro h
    exact code_adjacent_152
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (153 : Fin 495) from rfl))
    intro h
    exact code_adjacent_153
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (154 : Fin 495) from rfl))
    intro h
    exact code_adjacent_154
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (155 : Fin 495) from rfl))
    intro h
    exact code_adjacent_155
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (156 : Fin 495) from rfl))
    intro h
    exact code_adjacent_156
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (157 : Fin 495) from rfl))
    intro h
    exact code_adjacent_157
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (158 : Fin 495) from rfl))
    intro h
    exact code_adjacent_158
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (159 : Fin 495) from rfl))
    intro h
    exact code_adjacent_159

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock04
