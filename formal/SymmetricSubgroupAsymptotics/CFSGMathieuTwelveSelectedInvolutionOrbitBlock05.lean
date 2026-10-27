import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows160..191.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock05
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨160+i.val,by omega⟩

private theorem row_image_160 (p : Fin 12) :
    (rows 160).val p = rowForward 160 p := by
  calc
    (rows 160).val p = rowPoint 160 p := (rowPoint_eq 160 p).symm
    _ = rowForward 160 p := by fin_cases p <;> decide +kernel

private theorem transition_check_160 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 160) (generatorPermutation s p) =
      generatorPermutation s (rowForward 160 p) := by
  decide +kernel

private theorem code_encoding_160 :
    code 160 = ∑ p : Fin 12, (rowForward 160 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_160 : code 160 < code 161 := by
  decide +kernel

private theorem row_image_161 (p : Fin 12) :
    (rows 161).val p = rowForward 161 p := by
  calc
    (rows 161).val p = rowPoint 161 p := (rowPoint_eq 161 p).symm
    _ = rowForward 161 p := by fin_cases p <;> decide +kernel

private theorem transition_check_161 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 161) (generatorPermutation s p) =
      generatorPermutation s (rowForward 161 p) := by
  decide +kernel

private theorem code_encoding_161 :
    code 161 = ∑ p : Fin 12, (rowForward 161 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_161 : code 161 < code 162 := by
  decide +kernel

private theorem row_image_162 (p : Fin 12) :
    (rows 162).val p = rowForward 162 p := by
  calc
    (rows 162).val p = rowPoint 162 p := (rowPoint_eq 162 p).symm
    _ = rowForward 162 p := by fin_cases p <;> decide +kernel

private theorem transition_check_162 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 162) (generatorPermutation s p) =
      generatorPermutation s (rowForward 162 p) := by
  decide +kernel

private theorem code_encoding_162 :
    code 162 = ∑ p : Fin 12, (rowForward 162 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_162 : code 162 < code 163 := by
  decide +kernel

private theorem row_image_163 (p : Fin 12) :
    (rows 163).val p = rowForward 163 p := by
  calc
    (rows 163).val p = rowPoint 163 p := (rowPoint_eq 163 p).symm
    _ = rowForward 163 p := by fin_cases p <;> decide +kernel

private theorem transition_check_163 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 163) (generatorPermutation s p) =
      generatorPermutation s (rowForward 163 p) := by
  decide +kernel

private theorem code_encoding_163 :
    code 163 = ∑ p : Fin 12, (rowForward 163 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_163 : code 163 < code 164 := by
  decide +kernel

private theorem row_image_164 (p : Fin 12) :
    (rows 164).val p = rowForward 164 p := by
  calc
    (rows 164).val p = rowPoint 164 p := (rowPoint_eq 164 p).symm
    _ = rowForward 164 p := by fin_cases p <;> decide +kernel

private theorem transition_check_164 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 164) (generatorPermutation s p) =
      generatorPermutation s (rowForward 164 p) := by
  decide +kernel

private theorem code_encoding_164 :
    code 164 = ∑ p : Fin 12, (rowForward 164 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_164 : code 164 < code 165 := by
  decide +kernel

private theorem row_image_165 (p : Fin 12) :
    (rows 165).val p = rowForward 165 p := by
  calc
    (rows 165).val p = rowPoint 165 p := (rowPoint_eq 165 p).symm
    _ = rowForward 165 p := by fin_cases p <;> decide +kernel

private theorem transition_check_165 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 165) (generatorPermutation s p) =
      generatorPermutation s (rowForward 165 p) := by
  decide +kernel

private theorem code_encoding_165 :
    code 165 = ∑ p : Fin 12, (rowForward 165 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_165 : code 165 < code 166 := by
  decide +kernel

private theorem row_image_166 (p : Fin 12) :
    (rows 166).val p = rowForward 166 p := by
  calc
    (rows 166).val p = rowPoint 166 p := (rowPoint_eq 166 p).symm
    _ = rowForward 166 p := by fin_cases p <;> decide +kernel

private theorem transition_check_166 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 166) (generatorPermutation s p) =
      generatorPermutation s (rowForward 166 p) := by
  decide +kernel

private theorem code_encoding_166 :
    code 166 = ∑ p : Fin 12, (rowForward 166 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_166 : code 166 < code 167 := by
  decide +kernel

private theorem row_image_167 (p : Fin 12) :
    (rows 167).val p = rowForward 167 p := by
  calc
    (rows 167).val p = rowPoint 167 p := (rowPoint_eq 167 p).symm
    _ = rowForward 167 p := by fin_cases p <;> decide +kernel

private theorem transition_check_167 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 167) (generatorPermutation s p) =
      generatorPermutation s (rowForward 167 p) := by
  decide +kernel

private theorem code_encoding_167 :
    code 167 = ∑ p : Fin 12, (rowForward 167 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_167 : code 167 < code 168 := by
  decide +kernel

private theorem row_image_168 (p : Fin 12) :
    (rows 168).val p = rowForward 168 p := by
  calc
    (rows 168).val p = rowPoint 168 p := (rowPoint_eq 168 p).symm
    _ = rowForward 168 p := by fin_cases p <;> decide +kernel

private theorem transition_check_168 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 168) (generatorPermutation s p) =
      generatorPermutation s (rowForward 168 p) := by
  decide +kernel

private theorem code_encoding_168 :
    code 168 = ∑ p : Fin 12, (rowForward 168 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_168 : code 168 < code 169 := by
  decide +kernel

private theorem row_image_169 (p : Fin 12) :
    (rows 169).val p = rowForward 169 p := by
  calc
    (rows 169).val p = rowPoint 169 p := (rowPoint_eq 169 p).symm
    _ = rowForward 169 p := by fin_cases p <;> decide +kernel

private theorem transition_check_169 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 169) (generatorPermutation s p) =
      generatorPermutation s (rowForward 169 p) := by
  decide +kernel

private theorem code_encoding_169 :
    code 169 = ∑ p : Fin 12, (rowForward 169 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_169 : code 169 < code 170 := by
  decide +kernel

private theorem row_image_170 (p : Fin 12) :
    (rows 170).val p = rowForward 170 p := by
  calc
    (rows 170).val p = rowPoint 170 p := (rowPoint_eq 170 p).symm
    _ = rowForward 170 p := by fin_cases p <;> decide +kernel

private theorem transition_check_170 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 170) (generatorPermutation s p) =
      generatorPermutation s (rowForward 170 p) := by
  decide +kernel

private theorem code_encoding_170 :
    code 170 = ∑ p : Fin 12, (rowForward 170 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_170 : code 170 < code 171 := by
  decide +kernel

private theorem row_image_171 (p : Fin 12) :
    (rows 171).val p = rowForward 171 p := by
  calc
    (rows 171).val p = rowPoint 171 p := (rowPoint_eq 171 p).symm
    _ = rowForward 171 p := by fin_cases p <;> decide +kernel

private theorem transition_check_171 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 171) (generatorPermutation s p) =
      generatorPermutation s (rowForward 171 p) := by
  decide +kernel

private theorem code_encoding_171 :
    code 171 = ∑ p : Fin 12, (rowForward 171 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_171 : code 171 < code 172 := by
  decide +kernel

private theorem row_image_172 (p : Fin 12) :
    (rows 172).val p = rowForward 172 p := by
  calc
    (rows 172).val p = rowPoint 172 p := (rowPoint_eq 172 p).symm
    _ = rowForward 172 p := by fin_cases p <;> decide +kernel

private theorem transition_check_172 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 172) (generatorPermutation s p) =
      generatorPermutation s (rowForward 172 p) := by
  decide +kernel

private theorem code_encoding_172 :
    code 172 = ∑ p : Fin 12, (rowForward 172 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_172 : code 172 < code 173 := by
  decide +kernel

private theorem row_image_173 (p : Fin 12) :
    (rows 173).val p = rowForward 173 p := by
  calc
    (rows 173).val p = rowPoint 173 p := (rowPoint_eq 173 p).symm
    _ = rowForward 173 p := by fin_cases p <;> decide +kernel

private theorem transition_check_173 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 173) (generatorPermutation s p) =
      generatorPermutation s (rowForward 173 p) := by
  decide +kernel

private theorem code_encoding_173 :
    code 173 = ∑ p : Fin 12, (rowForward 173 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_173 : code 173 < code 174 := by
  decide +kernel

private theorem row_image_174 (p : Fin 12) :
    (rows 174).val p = rowForward 174 p := by
  calc
    (rows 174).val p = rowPoint 174 p := (rowPoint_eq 174 p).symm
    _ = rowForward 174 p := by fin_cases p <;> decide +kernel

private theorem transition_check_174 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 174) (generatorPermutation s p) =
      generatorPermutation s (rowForward 174 p) := by
  decide +kernel

private theorem code_encoding_174 :
    code 174 = ∑ p : Fin 12, (rowForward 174 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_174 : code 174 < code 175 := by
  decide +kernel

private theorem row_image_175 (p : Fin 12) :
    (rows 175).val p = rowForward 175 p := by
  calc
    (rows 175).val p = rowPoint 175 p := (rowPoint_eq 175 p).symm
    _ = rowForward 175 p := by fin_cases p <;> decide +kernel

private theorem transition_check_175 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 175) (generatorPermutation s p) =
      generatorPermutation s (rowForward 175 p) := by
  decide +kernel

private theorem code_encoding_175 :
    code 175 = ∑ p : Fin 12, (rowForward 175 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_175 : code 175 < code 176 := by
  decide +kernel

private theorem row_image_176 (p : Fin 12) :
    (rows 176).val p = rowForward 176 p := by
  calc
    (rows 176).val p = rowPoint 176 p := (rowPoint_eq 176 p).symm
    _ = rowForward 176 p := by fin_cases p <;> decide +kernel

private theorem transition_check_176 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 176) (generatorPermutation s p) =
      generatorPermutation s (rowForward 176 p) := by
  decide +kernel

private theorem code_encoding_176 :
    code 176 = ∑ p : Fin 12, (rowForward 176 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_176 : code 176 < code 177 := by
  decide +kernel

private theorem row_image_177 (p : Fin 12) :
    (rows 177).val p = rowForward 177 p := by
  calc
    (rows 177).val p = rowPoint 177 p := (rowPoint_eq 177 p).symm
    _ = rowForward 177 p := by fin_cases p <;> decide +kernel

private theorem transition_check_177 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 177) (generatorPermutation s p) =
      generatorPermutation s (rowForward 177 p) := by
  decide +kernel

private theorem code_encoding_177 :
    code 177 = ∑ p : Fin 12, (rowForward 177 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_177 : code 177 < code 178 := by
  decide +kernel

private theorem row_image_178 (p : Fin 12) :
    (rows 178).val p = rowForward 178 p := by
  calc
    (rows 178).val p = rowPoint 178 p := (rowPoint_eq 178 p).symm
    _ = rowForward 178 p := by fin_cases p <;> decide +kernel

private theorem transition_check_178 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 178) (generatorPermutation s p) =
      generatorPermutation s (rowForward 178 p) := by
  decide +kernel

private theorem code_encoding_178 :
    code 178 = ∑ p : Fin 12, (rowForward 178 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_178 : code 178 < code 179 := by
  decide +kernel

private theorem row_image_179 (p : Fin 12) :
    (rows 179).val p = rowForward 179 p := by
  calc
    (rows 179).val p = rowPoint 179 p := (rowPoint_eq 179 p).symm
    _ = rowForward 179 p := by fin_cases p <;> decide +kernel

private theorem transition_check_179 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 179) (generatorPermutation s p) =
      generatorPermutation s (rowForward 179 p) := by
  decide +kernel

private theorem code_encoding_179 :
    code 179 = ∑ p : Fin 12, (rowForward 179 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_179 : code 179 < code 180 := by
  decide +kernel

private theorem row_image_180 (p : Fin 12) :
    (rows 180).val p = rowForward 180 p := by
  calc
    (rows 180).val p = rowPoint 180 p := (rowPoint_eq 180 p).symm
    _ = rowForward 180 p := by fin_cases p <;> decide +kernel

private theorem transition_check_180 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 180) (generatorPermutation s p) =
      generatorPermutation s (rowForward 180 p) := by
  decide +kernel

private theorem code_encoding_180 :
    code 180 = ∑ p : Fin 12, (rowForward 180 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_180 : code 180 < code 181 := by
  decide +kernel

private theorem row_image_181 (p : Fin 12) :
    (rows 181).val p = rowForward 181 p := by
  calc
    (rows 181).val p = rowPoint 181 p := (rowPoint_eq 181 p).symm
    _ = rowForward 181 p := by fin_cases p <;> decide +kernel

private theorem transition_check_181 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 181) (generatorPermutation s p) =
      generatorPermutation s (rowForward 181 p) := by
  decide +kernel

private theorem code_encoding_181 :
    code 181 = ∑ p : Fin 12, (rowForward 181 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_181 : code 181 < code 182 := by
  decide +kernel

private theorem row_image_182 (p : Fin 12) :
    (rows 182).val p = rowForward 182 p := by
  calc
    (rows 182).val p = rowPoint 182 p := (rowPoint_eq 182 p).symm
    _ = rowForward 182 p := by fin_cases p <;> decide +kernel

private theorem transition_check_182 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 182) (generatorPermutation s p) =
      generatorPermutation s (rowForward 182 p) := by
  decide +kernel

private theorem code_encoding_182 :
    code 182 = ∑ p : Fin 12, (rowForward 182 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_182 : code 182 < code 183 := by
  decide +kernel

private theorem row_image_183 (p : Fin 12) :
    (rows 183).val p = rowForward 183 p := by
  calc
    (rows 183).val p = rowPoint 183 p := (rowPoint_eq 183 p).symm
    _ = rowForward 183 p := by fin_cases p <;> decide +kernel

private theorem transition_check_183 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 183) (generatorPermutation s p) =
      generatorPermutation s (rowForward 183 p) := by
  decide +kernel

private theorem code_encoding_183 :
    code 183 = ∑ p : Fin 12, (rowForward 183 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_183 : code 183 < code 184 := by
  decide +kernel

private theorem row_image_184 (p : Fin 12) :
    (rows 184).val p = rowForward 184 p := by
  calc
    (rows 184).val p = rowPoint 184 p := (rowPoint_eq 184 p).symm
    _ = rowForward 184 p := by fin_cases p <;> decide +kernel

private theorem transition_check_184 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 184) (generatorPermutation s p) =
      generatorPermutation s (rowForward 184 p) := by
  decide +kernel

private theorem code_encoding_184 :
    code 184 = ∑ p : Fin 12, (rowForward 184 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_184 : code 184 < code 185 := by
  decide +kernel

private theorem row_image_185 (p : Fin 12) :
    (rows 185).val p = rowForward 185 p := by
  calc
    (rows 185).val p = rowPoint 185 p := (rowPoint_eq 185 p).symm
    _ = rowForward 185 p := by fin_cases p <;> decide +kernel

private theorem transition_check_185 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 185) (generatorPermutation s p) =
      generatorPermutation s (rowForward 185 p) := by
  decide +kernel

private theorem code_encoding_185 :
    code 185 = ∑ p : Fin 12, (rowForward 185 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_185 : code 185 < code 186 := by
  decide +kernel

private theorem row_image_186 (p : Fin 12) :
    (rows 186).val p = rowForward 186 p := by
  calc
    (rows 186).val p = rowPoint 186 p := (rowPoint_eq 186 p).symm
    _ = rowForward 186 p := by fin_cases p <;> decide +kernel

private theorem transition_check_186 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 186) (generatorPermutation s p) =
      generatorPermutation s (rowForward 186 p) := by
  decide +kernel

private theorem code_encoding_186 :
    code 186 = ∑ p : Fin 12, (rowForward 186 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_186 : code 186 < code 187 := by
  decide +kernel

private theorem row_image_187 (p : Fin 12) :
    (rows 187).val p = rowForward 187 p := by
  calc
    (rows 187).val p = rowPoint 187 p := (rowPoint_eq 187 p).symm
    _ = rowForward 187 p := by fin_cases p <;> decide +kernel

private theorem transition_check_187 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 187) (generatorPermutation s p) =
      generatorPermutation s (rowForward 187 p) := by
  decide +kernel

private theorem code_encoding_187 :
    code 187 = ∑ p : Fin 12, (rowForward 187 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_187 : code 187 < code 188 := by
  decide +kernel

private theorem row_image_188 (p : Fin 12) :
    (rows 188).val p = rowForward 188 p := by
  calc
    (rows 188).val p = rowPoint 188 p := (rowPoint_eq 188 p).symm
    _ = rowForward 188 p := by fin_cases p <;> decide +kernel

private theorem transition_check_188 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 188) (generatorPermutation s p) =
      generatorPermutation s (rowForward 188 p) := by
  decide +kernel

private theorem code_encoding_188 :
    code 188 = ∑ p : Fin 12, (rowForward 188 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_188 : code 188 < code 189 := by
  decide +kernel

private theorem row_image_189 (p : Fin 12) :
    (rows 189).val p = rowForward 189 p := by
  calc
    (rows 189).val p = rowPoint 189 p := (rowPoint_eq 189 p).symm
    _ = rowForward 189 p := by fin_cases p <;> decide +kernel

private theorem transition_check_189 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 189) (generatorPermutation s p) =
      generatorPermutation s (rowForward 189 p) := by
  decide +kernel

private theorem code_encoding_189 :
    code 189 = ∑ p : Fin 12, (rowForward 189 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_189 : code 189 < code 190 := by
  decide +kernel

private theorem row_image_190 (p : Fin 12) :
    (rows 190).val p = rowForward 190 p := by
  calc
    (rows 190).val p = rowPoint 190 p := (rowPoint_eq 190 p).symm
    _ = rowForward 190 p := by fin_cases p <;> decide +kernel

private theorem transition_check_190 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 190) (generatorPermutation s p) =
      generatorPermutation s (rowForward 190 p) := by
  decide +kernel

private theorem code_encoding_190 :
    code 190 = ∑ p : Fin 12, (rowForward 190 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_190 : code 190 < code 191 := by
  decide +kernel

private theorem row_image_191 (p : Fin 12) :
    (rows 191).val p = rowForward 191 p := by
  calc
    (rows 191).val p = rowPoint 191 p := (rowPoint_eq 191 p).symm
    _ = rowForward 191 p := by fin_cases p <;> decide +kernel

private theorem transition_check_191 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 191) (generatorPermutation s p) =
      generatorPermutation s (rowForward 191 p) := by
  decide +kernel

private theorem code_encoding_191 :
    code 191 = ∑ p : Fin 12, (rowForward 191 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_191 : code 191 < code 192 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (160 : Fin 495) from rfl))
      (row_image_160 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (161 : Fin 495) from rfl))
      (row_image_161 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (162 : Fin 495) from rfl))
      (row_image_162 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (163 : Fin 495) from rfl))
      (row_image_163 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (164 : Fin 495) from rfl))
      (row_image_164 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (165 : Fin 495) from rfl))
      (row_image_165 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (166 : Fin 495) from rfl))
      (row_image_166 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (167 : Fin 495) from rfl))
      (row_image_167 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (168 : Fin 495) from rfl))
      (row_image_168 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (169 : Fin 495) from rfl))
      (row_image_169 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (170 : Fin 495) from rfl))
      (row_image_170 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (171 : Fin 495) from rfl))
      (row_image_171 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (172 : Fin 495) from rfl))
      (row_image_172 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (173 : Fin 495) from rfl))
      (row_image_173 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (174 : Fin 495) from rfl))
      (row_image_174 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (175 : Fin 495) from rfl))
      (row_image_175 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (176 : Fin 495) from rfl))
      (row_image_176 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (177 : Fin 495) from rfl))
      (row_image_177 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (178 : Fin 495) from rfl))
      (row_image_178 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (179 : Fin 495) from rfl))
      (row_image_179 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (180 : Fin 495) from rfl))
      (row_image_180 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (181 : Fin 495) from rfl))
      (row_image_181 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (182 : Fin 495) from rfl))
      (row_image_182 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (183 : Fin 495) from rfl))
      (row_image_183 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (184 : Fin 495) from rfl))
      (row_image_184 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (185 : Fin 495) from rfl))
      (row_image_185 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (186 : Fin 495) from rfl))
      (row_image_186 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (187 : Fin 495) from rfl))
      (row_image_187 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (188 : Fin 495) from rfl))
      (row_image_188 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (189 : Fin 495) from rfl))
      (row_image_189 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (190 : Fin 495) from rfl))
      (row_image_190 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (191 : Fin 495) from rfl))
      (row_image_191 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (160 : Fin 495) from rfl))
      (transition_check_160 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (161 : Fin 495) from rfl))
      (transition_check_161 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (162 : Fin 495) from rfl))
      (transition_check_162 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (163 : Fin 495) from rfl))
      (transition_check_163 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (164 : Fin 495) from rfl))
      (transition_check_164 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (165 : Fin 495) from rfl))
      (transition_check_165 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (166 : Fin 495) from rfl))
      (transition_check_166 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (167 : Fin 495) from rfl))
      (transition_check_167 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (168 : Fin 495) from rfl))
      (transition_check_168 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (169 : Fin 495) from rfl))
      (transition_check_169 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (170 : Fin 495) from rfl))
      (transition_check_170 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (171 : Fin 495) from rfl))
      (transition_check_171 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (172 : Fin 495) from rfl))
      (transition_check_172 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (173 : Fin 495) from rfl))
      (transition_check_173 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (174 : Fin 495) from rfl))
      (transition_check_174 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (175 : Fin 495) from rfl))
      (transition_check_175 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (176 : Fin 495) from rfl))
      (transition_check_176 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (177 : Fin 495) from rfl))
      (transition_check_177 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (178 : Fin 495) from rfl))
      (transition_check_178 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (179 : Fin 495) from rfl))
      (transition_check_179 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (180 : Fin 495) from rfl))
      (transition_check_180 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (181 : Fin 495) from rfl))
      (transition_check_181 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (182 : Fin 495) from rfl))
      (transition_check_182 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (183 : Fin 495) from rfl))
      (transition_check_183 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (184 : Fin 495) from rfl))
      (transition_check_184 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (185 : Fin 495) from rfl))
      (transition_check_185 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (186 : Fin 495) from rfl))
      (transition_check_186 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (187 : Fin 495) from rfl))
      (transition_check_187 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (188 : Fin 495) from rfl))
      (transition_check_188 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (189 : Fin 495) from rfl))
      (transition_check_189 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (190 : Fin 495) from rfl))
      (transition_check_190 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (191 : Fin 495) from rfl))
      (transition_check_191 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (160 : Fin 495) from rfl))
      code_encoding_160
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (161 : Fin 495) from rfl))
      code_encoding_161
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (162 : Fin 495) from rfl))
      code_encoding_162
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (163 : Fin 495) from rfl))
      code_encoding_163
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (164 : Fin 495) from rfl))
      code_encoding_164
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (165 : Fin 495) from rfl))
      code_encoding_165
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (166 : Fin 495) from rfl))
      code_encoding_166
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (167 : Fin 495) from rfl))
      code_encoding_167
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (168 : Fin 495) from rfl))
      code_encoding_168
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (169 : Fin 495) from rfl))
      code_encoding_169
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (170 : Fin 495) from rfl))
      code_encoding_170
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (171 : Fin 495) from rfl))
      code_encoding_171
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (172 : Fin 495) from rfl))
      code_encoding_172
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (173 : Fin 495) from rfl))
      code_encoding_173
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (174 : Fin 495) from rfl))
      code_encoding_174
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (175 : Fin 495) from rfl))
      code_encoding_175
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (176 : Fin 495) from rfl))
      code_encoding_176
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (177 : Fin 495) from rfl))
      code_encoding_177
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (178 : Fin 495) from rfl))
      code_encoding_178
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (179 : Fin 495) from rfl))
      code_encoding_179
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (180 : Fin 495) from rfl))
      code_encoding_180
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (181 : Fin 495) from rfl))
      code_encoding_181
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (182 : Fin 495) from rfl))
      code_encoding_182
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (183 : Fin 495) from rfl))
      code_encoding_183
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (184 : Fin 495) from rfl))
      code_encoding_184
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (185 : Fin 495) from rfl))
      code_encoding_185
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (186 : Fin 495) from rfl))
      code_encoding_186
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (187 : Fin 495) from rfl))
      code_encoding_187
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (188 : Fin 495) from rfl))
      code_encoding_188
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (189 : Fin 495) from rfl))
      code_encoding_189
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (190 : Fin 495) from rfl))
      code_encoding_190
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (191 : Fin 495) from rfl))
      code_encoding_191

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (160 : Fin 495) from rfl))
    intro h
    exact code_adjacent_160
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (161 : Fin 495) from rfl))
    intro h
    exact code_adjacent_161
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (162 : Fin 495) from rfl))
    intro h
    exact code_adjacent_162
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (163 : Fin 495) from rfl))
    intro h
    exact code_adjacent_163
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (164 : Fin 495) from rfl))
    intro h
    exact code_adjacent_164
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (165 : Fin 495) from rfl))
    intro h
    exact code_adjacent_165
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (166 : Fin 495) from rfl))
    intro h
    exact code_adjacent_166
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (167 : Fin 495) from rfl))
    intro h
    exact code_adjacent_167
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (168 : Fin 495) from rfl))
    intro h
    exact code_adjacent_168
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (169 : Fin 495) from rfl))
    intro h
    exact code_adjacent_169
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (170 : Fin 495) from rfl))
    intro h
    exact code_adjacent_170
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (171 : Fin 495) from rfl))
    intro h
    exact code_adjacent_171
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (172 : Fin 495) from rfl))
    intro h
    exact code_adjacent_172
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (173 : Fin 495) from rfl))
    intro h
    exact code_adjacent_173
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (174 : Fin 495) from rfl))
    intro h
    exact code_adjacent_174
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (175 : Fin 495) from rfl))
    intro h
    exact code_adjacent_175
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (176 : Fin 495) from rfl))
    intro h
    exact code_adjacent_176
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (177 : Fin 495) from rfl))
    intro h
    exact code_adjacent_177
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (178 : Fin 495) from rfl))
    intro h
    exact code_adjacent_178
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (179 : Fin 495) from rfl))
    intro h
    exact code_adjacent_179
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (180 : Fin 495) from rfl))
    intro h
    exact code_adjacent_180
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (181 : Fin 495) from rfl))
    intro h
    exact code_adjacent_181
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (182 : Fin 495) from rfl))
    intro h
    exact code_adjacent_182
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (183 : Fin 495) from rfl))
    intro h
    exact code_adjacent_183
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (184 : Fin 495) from rfl))
    intro h
    exact code_adjacent_184
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (185 : Fin 495) from rfl))
    intro h
    exact code_adjacent_185
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (186 : Fin 495) from rfl))
    intro h
    exact code_adjacent_186
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (187 : Fin 495) from rfl))
    intro h
    exact code_adjacent_187
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (188 : Fin 495) from rfl))
    intro h
    exact code_adjacent_188
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (189 : Fin 495) from rfl))
    intro h
    exact code_adjacent_189
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (190 : Fin 495) from rfl))
    intro h
    exact code_adjacent_190
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (191 : Fin 495) from rfl))
    intro h
    exact code_adjacent_191

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock05
