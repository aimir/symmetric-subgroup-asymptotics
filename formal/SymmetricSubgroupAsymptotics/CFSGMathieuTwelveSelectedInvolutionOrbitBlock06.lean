import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows192..223.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock06
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨192+i.val,by omega⟩

private theorem row_image_192 (p : Fin 12) :
    (rows 192).val p = rowForward 192 p := by
  calc
    (rows 192).val p = rowPoint 192 p := (rowPoint_eq 192 p).symm
    _ = rowForward 192 p := by fin_cases p <;> decide +kernel

private theorem transition_check_192 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 192) (generatorPermutation s p) =
      generatorPermutation s (rowForward 192 p) := by
  decide +kernel

private theorem code_encoding_192 :
    code 192 = ∑ p : Fin 12, (rowForward 192 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_192 : code 192 < code 193 := by
  decide +kernel

private theorem row_image_193 (p : Fin 12) :
    (rows 193).val p = rowForward 193 p := by
  calc
    (rows 193).val p = rowPoint 193 p := (rowPoint_eq 193 p).symm
    _ = rowForward 193 p := by fin_cases p <;> decide +kernel

private theorem transition_check_193 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 193) (generatorPermutation s p) =
      generatorPermutation s (rowForward 193 p) := by
  decide +kernel

private theorem code_encoding_193 :
    code 193 = ∑ p : Fin 12, (rowForward 193 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_193 : code 193 < code 194 := by
  decide +kernel

private theorem row_image_194 (p : Fin 12) :
    (rows 194).val p = rowForward 194 p := by
  calc
    (rows 194).val p = rowPoint 194 p := (rowPoint_eq 194 p).symm
    _ = rowForward 194 p := by fin_cases p <;> decide +kernel

private theorem transition_check_194 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 194) (generatorPermutation s p) =
      generatorPermutation s (rowForward 194 p) := by
  decide +kernel

private theorem code_encoding_194 :
    code 194 = ∑ p : Fin 12, (rowForward 194 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_194 : code 194 < code 195 := by
  decide +kernel

private theorem row_image_195 (p : Fin 12) :
    (rows 195).val p = rowForward 195 p := by
  calc
    (rows 195).val p = rowPoint 195 p := (rowPoint_eq 195 p).symm
    _ = rowForward 195 p := by fin_cases p <;> decide +kernel

private theorem transition_check_195 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 195) (generatorPermutation s p) =
      generatorPermutation s (rowForward 195 p) := by
  decide +kernel

private theorem code_encoding_195 :
    code 195 = ∑ p : Fin 12, (rowForward 195 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_195 : code 195 < code 196 := by
  decide +kernel

private theorem row_image_196 (p : Fin 12) :
    (rows 196).val p = rowForward 196 p := by
  calc
    (rows 196).val p = rowPoint 196 p := (rowPoint_eq 196 p).symm
    _ = rowForward 196 p := by fin_cases p <;> decide +kernel

private theorem transition_check_196 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 196) (generatorPermutation s p) =
      generatorPermutation s (rowForward 196 p) := by
  decide +kernel

private theorem code_encoding_196 :
    code 196 = ∑ p : Fin 12, (rowForward 196 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_196 : code 196 < code 197 := by
  decide +kernel

private theorem row_image_197 (p : Fin 12) :
    (rows 197).val p = rowForward 197 p := by
  calc
    (rows 197).val p = rowPoint 197 p := (rowPoint_eq 197 p).symm
    _ = rowForward 197 p := by fin_cases p <;> decide +kernel

private theorem transition_check_197 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 197) (generatorPermutation s p) =
      generatorPermutation s (rowForward 197 p) := by
  decide +kernel

private theorem code_encoding_197 :
    code 197 = ∑ p : Fin 12, (rowForward 197 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_197 : code 197 < code 198 := by
  decide +kernel

private theorem row_image_198 (p : Fin 12) :
    (rows 198).val p = rowForward 198 p := by
  calc
    (rows 198).val p = rowPoint 198 p := (rowPoint_eq 198 p).symm
    _ = rowForward 198 p := by fin_cases p <;> decide +kernel

private theorem transition_check_198 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 198) (generatorPermutation s p) =
      generatorPermutation s (rowForward 198 p) := by
  decide +kernel

private theorem code_encoding_198 :
    code 198 = ∑ p : Fin 12, (rowForward 198 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_198 : code 198 < code 199 := by
  decide +kernel

private theorem row_image_199 (p : Fin 12) :
    (rows 199).val p = rowForward 199 p := by
  calc
    (rows 199).val p = rowPoint 199 p := (rowPoint_eq 199 p).symm
    _ = rowForward 199 p := by fin_cases p <;> decide +kernel

private theorem transition_check_199 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 199) (generatorPermutation s p) =
      generatorPermutation s (rowForward 199 p) := by
  decide +kernel

private theorem code_encoding_199 :
    code 199 = ∑ p : Fin 12, (rowForward 199 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_199 : code 199 < code 200 := by
  decide +kernel

private theorem row_image_200 (p : Fin 12) :
    (rows 200).val p = rowForward 200 p := by
  calc
    (rows 200).val p = rowPoint 200 p := (rowPoint_eq 200 p).symm
    _ = rowForward 200 p := by fin_cases p <;> decide +kernel

private theorem transition_check_200 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 200) (generatorPermutation s p) =
      generatorPermutation s (rowForward 200 p) := by
  decide +kernel

private theorem code_encoding_200 :
    code 200 = ∑ p : Fin 12, (rowForward 200 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_200 : code 200 < code 201 := by
  decide +kernel

private theorem row_image_201 (p : Fin 12) :
    (rows 201).val p = rowForward 201 p := by
  calc
    (rows 201).val p = rowPoint 201 p := (rowPoint_eq 201 p).symm
    _ = rowForward 201 p := by fin_cases p <;> decide +kernel

private theorem transition_check_201 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 201) (generatorPermutation s p) =
      generatorPermutation s (rowForward 201 p) := by
  decide +kernel

private theorem code_encoding_201 :
    code 201 = ∑ p : Fin 12, (rowForward 201 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_201 : code 201 < code 202 := by
  decide +kernel

private theorem row_image_202 (p : Fin 12) :
    (rows 202).val p = rowForward 202 p := by
  calc
    (rows 202).val p = rowPoint 202 p := (rowPoint_eq 202 p).symm
    _ = rowForward 202 p := by fin_cases p <;> decide +kernel

private theorem transition_check_202 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 202) (generatorPermutation s p) =
      generatorPermutation s (rowForward 202 p) := by
  decide +kernel

private theorem code_encoding_202 :
    code 202 = ∑ p : Fin 12, (rowForward 202 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_202 : code 202 < code 203 := by
  decide +kernel

private theorem row_image_203 (p : Fin 12) :
    (rows 203).val p = rowForward 203 p := by
  calc
    (rows 203).val p = rowPoint 203 p := (rowPoint_eq 203 p).symm
    _ = rowForward 203 p := by fin_cases p <;> decide +kernel

private theorem transition_check_203 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 203) (generatorPermutation s p) =
      generatorPermutation s (rowForward 203 p) := by
  decide +kernel

private theorem code_encoding_203 :
    code 203 = ∑ p : Fin 12, (rowForward 203 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_203 : code 203 < code 204 := by
  decide +kernel

private theorem row_image_204 (p : Fin 12) :
    (rows 204).val p = rowForward 204 p := by
  calc
    (rows 204).val p = rowPoint 204 p := (rowPoint_eq 204 p).symm
    _ = rowForward 204 p := by fin_cases p <;> decide +kernel

private theorem transition_check_204 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 204) (generatorPermutation s p) =
      generatorPermutation s (rowForward 204 p) := by
  decide +kernel

private theorem code_encoding_204 :
    code 204 = ∑ p : Fin 12, (rowForward 204 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_204 : code 204 < code 205 := by
  decide +kernel

private theorem row_image_205 (p : Fin 12) :
    (rows 205).val p = rowForward 205 p := by
  calc
    (rows 205).val p = rowPoint 205 p := (rowPoint_eq 205 p).symm
    _ = rowForward 205 p := by fin_cases p <;> decide +kernel

private theorem transition_check_205 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 205) (generatorPermutation s p) =
      generatorPermutation s (rowForward 205 p) := by
  decide +kernel

private theorem code_encoding_205 :
    code 205 = ∑ p : Fin 12, (rowForward 205 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_205 : code 205 < code 206 := by
  decide +kernel

private theorem row_image_206 (p : Fin 12) :
    (rows 206).val p = rowForward 206 p := by
  calc
    (rows 206).val p = rowPoint 206 p := (rowPoint_eq 206 p).symm
    _ = rowForward 206 p := by fin_cases p <;> decide +kernel

private theorem transition_check_206 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 206) (generatorPermutation s p) =
      generatorPermutation s (rowForward 206 p) := by
  decide +kernel

private theorem code_encoding_206 :
    code 206 = ∑ p : Fin 12, (rowForward 206 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_206 : code 206 < code 207 := by
  decide +kernel

private theorem row_image_207 (p : Fin 12) :
    (rows 207).val p = rowForward 207 p := by
  calc
    (rows 207).val p = rowPoint 207 p := (rowPoint_eq 207 p).symm
    _ = rowForward 207 p := by fin_cases p <;> decide +kernel

private theorem transition_check_207 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 207) (generatorPermutation s p) =
      generatorPermutation s (rowForward 207 p) := by
  decide +kernel

private theorem code_encoding_207 :
    code 207 = ∑ p : Fin 12, (rowForward 207 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_207 : code 207 < code 208 := by
  decide +kernel

private theorem row_image_208 (p : Fin 12) :
    (rows 208).val p = rowForward 208 p := by
  calc
    (rows 208).val p = rowPoint 208 p := (rowPoint_eq 208 p).symm
    _ = rowForward 208 p := by fin_cases p <;> decide +kernel

private theorem transition_check_208 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 208) (generatorPermutation s p) =
      generatorPermutation s (rowForward 208 p) := by
  decide +kernel

private theorem code_encoding_208 :
    code 208 = ∑ p : Fin 12, (rowForward 208 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_208 : code 208 < code 209 := by
  decide +kernel

private theorem row_image_209 (p : Fin 12) :
    (rows 209).val p = rowForward 209 p := by
  calc
    (rows 209).val p = rowPoint 209 p := (rowPoint_eq 209 p).symm
    _ = rowForward 209 p := by fin_cases p <;> decide +kernel

private theorem transition_check_209 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 209) (generatorPermutation s p) =
      generatorPermutation s (rowForward 209 p) := by
  decide +kernel

private theorem code_encoding_209 :
    code 209 = ∑ p : Fin 12, (rowForward 209 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_209 : code 209 < code 210 := by
  decide +kernel

private theorem row_image_210 (p : Fin 12) :
    (rows 210).val p = rowForward 210 p := by
  calc
    (rows 210).val p = rowPoint 210 p := (rowPoint_eq 210 p).symm
    _ = rowForward 210 p := by fin_cases p <;> decide +kernel

private theorem transition_check_210 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 210) (generatorPermutation s p) =
      generatorPermutation s (rowForward 210 p) := by
  decide +kernel

private theorem code_encoding_210 :
    code 210 = ∑ p : Fin 12, (rowForward 210 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_210 : code 210 < code 211 := by
  decide +kernel

private theorem row_image_211 (p : Fin 12) :
    (rows 211).val p = rowForward 211 p := by
  calc
    (rows 211).val p = rowPoint 211 p := (rowPoint_eq 211 p).symm
    _ = rowForward 211 p := by fin_cases p <;> decide +kernel

private theorem transition_check_211 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 211) (generatorPermutation s p) =
      generatorPermutation s (rowForward 211 p) := by
  decide +kernel

private theorem code_encoding_211 :
    code 211 = ∑ p : Fin 12, (rowForward 211 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_211 : code 211 < code 212 := by
  decide +kernel

private theorem row_image_212 (p : Fin 12) :
    (rows 212).val p = rowForward 212 p := by
  calc
    (rows 212).val p = rowPoint 212 p := (rowPoint_eq 212 p).symm
    _ = rowForward 212 p := by fin_cases p <;> decide +kernel

private theorem transition_check_212 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 212) (generatorPermutation s p) =
      generatorPermutation s (rowForward 212 p) := by
  decide +kernel

private theorem code_encoding_212 :
    code 212 = ∑ p : Fin 12, (rowForward 212 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_212 : code 212 < code 213 := by
  decide +kernel

private theorem row_image_213 (p : Fin 12) :
    (rows 213).val p = rowForward 213 p := by
  calc
    (rows 213).val p = rowPoint 213 p := (rowPoint_eq 213 p).symm
    _ = rowForward 213 p := by fin_cases p <;> decide +kernel

private theorem transition_check_213 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 213) (generatorPermutation s p) =
      generatorPermutation s (rowForward 213 p) := by
  decide +kernel

private theorem code_encoding_213 :
    code 213 = ∑ p : Fin 12, (rowForward 213 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_213 : code 213 < code 214 := by
  decide +kernel

private theorem row_image_214 (p : Fin 12) :
    (rows 214).val p = rowForward 214 p := by
  calc
    (rows 214).val p = rowPoint 214 p := (rowPoint_eq 214 p).symm
    _ = rowForward 214 p := by fin_cases p <;> decide +kernel

private theorem transition_check_214 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 214) (generatorPermutation s p) =
      generatorPermutation s (rowForward 214 p) := by
  decide +kernel

private theorem code_encoding_214 :
    code 214 = ∑ p : Fin 12, (rowForward 214 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_214 : code 214 < code 215 := by
  decide +kernel

private theorem row_image_215 (p : Fin 12) :
    (rows 215).val p = rowForward 215 p := by
  calc
    (rows 215).val p = rowPoint 215 p := (rowPoint_eq 215 p).symm
    _ = rowForward 215 p := by fin_cases p <;> decide +kernel

private theorem transition_check_215 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 215) (generatorPermutation s p) =
      generatorPermutation s (rowForward 215 p) := by
  decide +kernel

private theorem code_encoding_215 :
    code 215 = ∑ p : Fin 12, (rowForward 215 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_215 : code 215 < code 216 := by
  decide +kernel

private theorem row_image_216 (p : Fin 12) :
    (rows 216).val p = rowForward 216 p := by
  calc
    (rows 216).val p = rowPoint 216 p := (rowPoint_eq 216 p).symm
    _ = rowForward 216 p := by fin_cases p <;> decide +kernel

private theorem transition_check_216 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 216) (generatorPermutation s p) =
      generatorPermutation s (rowForward 216 p) := by
  decide +kernel

private theorem code_encoding_216 :
    code 216 = ∑ p : Fin 12, (rowForward 216 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_216 : code 216 < code 217 := by
  decide +kernel

private theorem row_image_217 (p : Fin 12) :
    (rows 217).val p = rowForward 217 p := by
  calc
    (rows 217).val p = rowPoint 217 p := (rowPoint_eq 217 p).symm
    _ = rowForward 217 p := by fin_cases p <;> decide +kernel

private theorem transition_check_217 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 217) (generatorPermutation s p) =
      generatorPermutation s (rowForward 217 p) := by
  decide +kernel

private theorem code_encoding_217 :
    code 217 = ∑ p : Fin 12, (rowForward 217 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_217 : code 217 < code 218 := by
  decide +kernel

private theorem row_image_218 (p : Fin 12) :
    (rows 218).val p = rowForward 218 p := by
  calc
    (rows 218).val p = rowPoint 218 p := (rowPoint_eq 218 p).symm
    _ = rowForward 218 p := by fin_cases p <;> decide +kernel

private theorem transition_check_218 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 218) (generatorPermutation s p) =
      generatorPermutation s (rowForward 218 p) := by
  decide +kernel

private theorem code_encoding_218 :
    code 218 = ∑ p : Fin 12, (rowForward 218 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_218 : code 218 < code 219 := by
  decide +kernel

private theorem row_image_219 (p : Fin 12) :
    (rows 219).val p = rowForward 219 p := by
  calc
    (rows 219).val p = rowPoint 219 p := (rowPoint_eq 219 p).symm
    _ = rowForward 219 p := by fin_cases p <;> decide +kernel

private theorem transition_check_219 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 219) (generatorPermutation s p) =
      generatorPermutation s (rowForward 219 p) := by
  decide +kernel

private theorem code_encoding_219 :
    code 219 = ∑ p : Fin 12, (rowForward 219 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_219 : code 219 < code 220 := by
  decide +kernel

private theorem row_image_220 (p : Fin 12) :
    (rows 220).val p = rowForward 220 p := by
  calc
    (rows 220).val p = rowPoint 220 p := (rowPoint_eq 220 p).symm
    _ = rowForward 220 p := by fin_cases p <;> decide +kernel

private theorem transition_check_220 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 220) (generatorPermutation s p) =
      generatorPermutation s (rowForward 220 p) := by
  decide +kernel

private theorem code_encoding_220 :
    code 220 = ∑ p : Fin 12, (rowForward 220 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_220 : code 220 < code 221 := by
  decide +kernel

private theorem row_image_221 (p : Fin 12) :
    (rows 221).val p = rowForward 221 p := by
  calc
    (rows 221).val p = rowPoint 221 p := (rowPoint_eq 221 p).symm
    _ = rowForward 221 p := by fin_cases p <;> decide +kernel

private theorem transition_check_221 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 221) (generatorPermutation s p) =
      generatorPermutation s (rowForward 221 p) := by
  decide +kernel

private theorem code_encoding_221 :
    code 221 = ∑ p : Fin 12, (rowForward 221 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_221 : code 221 < code 222 := by
  decide +kernel

private theorem row_image_222 (p : Fin 12) :
    (rows 222).val p = rowForward 222 p := by
  calc
    (rows 222).val p = rowPoint 222 p := (rowPoint_eq 222 p).symm
    _ = rowForward 222 p := by fin_cases p <;> decide +kernel

private theorem transition_check_222 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 222) (generatorPermutation s p) =
      generatorPermutation s (rowForward 222 p) := by
  decide +kernel

private theorem code_encoding_222 :
    code 222 = ∑ p : Fin 12, (rowForward 222 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_222 : code 222 < code 223 := by
  decide +kernel

private theorem row_image_223 (p : Fin 12) :
    (rows 223).val p = rowForward 223 p := by
  calc
    (rows 223).val p = rowPoint 223 p := (rowPoint_eq 223 p).symm
    _ = rowForward 223 p := by fin_cases p <;> decide +kernel

private theorem transition_check_223 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 223) (generatorPermutation s p) =
      generatorPermutation s (rowForward 223 p) := by
  decide +kernel

private theorem code_encoding_223 :
    code 223 = ∑ p : Fin 12, (rowForward 223 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_223 : code 223 < code 224 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (192 : Fin 495) from rfl))
      (row_image_192 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (193 : Fin 495) from rfl))
      (row_image_193 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (194 : Fin 495) from rfl))
      (row_image_194 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (195 : Fin 495) from rfl))
      (row_image_195 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (196 : Fin 495) from rfl))
      (row_image_196 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (197 : Fin 495) from rfl))
      (row_image_197 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (198 : Fin 495) from rfl))
      (row_image_198 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (199 : Fin 495) from rfl))
      (row_image_199 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (200 : Fin 495) from rfl))
      (row_image_200 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (201 : Fin 495) from rfl))
      (row_image_201 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (202 : Fin 495) from rfl))
      (row_image_202 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (203 : Fin 495) from rfl))
      (row_image_203 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (204 : Fin 495) from rfl))
      (row_image_204 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (205 : Fin 495) from rfl))
      (row_image_205 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (206 : Fin 495) from rfl))
      (row_image_206 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (207 : Fin 495) from rfl))
      (row_image_207 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (208 : Fin 495) from rfl))
      (row_image_208 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (209 : Fin 495) from rfl))
      (row_image_209 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (210 : Fin 495) from rfl))
      (row_image_210 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (211 : Fin 495) from rfl))
      (row_image_211 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (212 : Fin 495) from rfl))
      (row_image_212 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (213 : Fin 495) from rfl))
      (row_image_213 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (214 : Fin 495) from rfl))
      (row_image_214 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (215 : Fin 495) from rfl))
      (row_image_215 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (216 : Fin 495) from rfl))
      (row_image_216 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (217 : Fin 495) from rfl))
      (row_image_217 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (218 : Fin 495) from rfl))
      (row_image_218 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (219 : Fin 495) from rfl))
      (row_image_219 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (220 : Fin 495) from rfl))
      (row_image_220 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (221 : Fin 495) from rfl))
      (row_image_221 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (222 : Fin 495) from rfl))
      (row_image_222 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (223 : Fin 495) from rfl))
      (row_image_223 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (192 : Fin 495) from rfl))
      (transition_check_192 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (193 : Fin 495) from rfl))
      (transition_check_193 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (194 : Fin 495) from rfl))
      (transition_check_194 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (195 : Fin 495) from rfl))
      (transition_check_195 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (196 : Fin 495) from rfl))
      (transition_check_196 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (197 : Fin 495) from rfl))
      (transition_check_197 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (198 : Fin 495) from rfl))
      (transition_check_198 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (199 : Fin 495) from rfl))
      (transition_check_199 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (200 : Fin 495) from rfl))
      (transition_check_200 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (201 : Fin 495) from rfl))
      (transition_check_201 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (202 : Fin 495) from rfl))
      (transition_check_202 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (203 : Fin 495) from rfl))
      (transition_check_203 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (204 : Fin 495) from rfl))
      (transition_check_204 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (205 : Fin 495) from rfl))
      (transition_check_205 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (206 : Fin 495) from rfl))
      (transition_check_206 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (207 : Fin 495) from rfl))
      (transition_check_207 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (208 : Fin 495) from rfl))
      (transition_check_208 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (209 : Fin 495) from rfl))
      (transition_check_209 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (210 : Fin 495) from rfl))
      (transition_check_210 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (211 : Fin 495) from rfl))
      (transition_check_211 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (212 : Fin 495) from rfl))
      (transition_check_212 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (213 : Fin 495) from rfl))
      (transition_check_213 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (214 : Fin 495) from rfl))
      (transition_check_214 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (215 : Fin 495) from rfl))
      (transition_check_215 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (216 : Fin 495) from rfl))
      (transition_check_216 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (217 : Fin 495) from rfl))
      (transition_check_217 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (218 : Fin 495) from rfl))
      (transition_check_218 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (219 : Fin 495) from rfl))
      (transition_check_219 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (220 : Fin 495) from rfl))
      (transition_check_220 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (221 : Fin 495) from rfl))
      (transition_check_221 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (222 : Fin 495) from rfl))
      (transition_check_222 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (223 : Fin 495) from rfl))
      (transition_check_223 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (192 : Fin 495) from rfl))
      code_encoding_192
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (193 : Fin 495) from rfl))
      code_encoding_193
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (194 : Fin 495) from rfl))
      code_encoding_194
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (195 : Fin 495) from rfl))
      code_encoding_195
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (196 : Fin 495) from rfl))
      code_encoding_196
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (197 : Fin 495) from rfl))
      code_encoding_197
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (198 : Fin 495) from rfl))
      code_encoding_198
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (199 : Fin 495) from rfl))
      code_encoding_199
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (200 : Fin 495) from rfl))
      code_encoding_200
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (201 : Fin 495) from rfl))
      code_encoding_201
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (202 : Fin 495) from rfl))
      code_encoding_202
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (203 : Fin 495) from rfl))
      code_encoding_203
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (204 : Fin 495) from rfl))
      code_encoding_204
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (205 : Fin 495) from rfl))
      code_encoding_205
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (206 : Fin 495) from rfl))
      code_encoding_206
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (207 : Fin 495) from rfl))
      code_encoding_207
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (208 : Fin 495) from rfl))
      code_encoding_208
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (209 : Fin 495) from rfl))
      code_encoding_209
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (210 : Fin 495) from rfl))
      code_encoding_210
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (211 : Fin 495) from rfl))
      code_encoding_211
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (212 : Fin 495) from rfl))
      code_encoding_212
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (213 : Fin 495) from rfl))
      code_encoding_213
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (214 : Fin 495) from rfl))
      code_encoding_214
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (215 : Fin 495) from rfl))
      code_encoding_215
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (216 : Fin 495) from rfl))
      code_encoding_216
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (217 : Fin 495) from rfl))
      code_encoding_217
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (218 : Fin 495) from rfl))
      code_encoding_218
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (219 : Fin 495) from rfl))
      code_encoding_219
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (220 : Fin 495) from rfl))
      code_encoding_220
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (221 : Fin 495) from rfl))
      code_encoding_221
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (222 : Fin 495) from rfl))
      code_encoding_222
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (223 : Fin 495) from rfl))
      code_encoding_223

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (192 : Fin 495) from rfl))
    intro h
    exact code_adjacent_192
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (193 : Fin 495) from rfl))
    intro h
    exact code_adjacent_193
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (194 : Fin 495) from rfl))
    intro h
    exact code_adjacent_194
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (195 : Fin 495) from rfl))
    intro h
    exact code_adjacent_195
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (196 : Fin 495) from rfl))
    intro h
    exact code_adjacent_196
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (197 : Fin 495) from rfl))
    intro h
    exact code_adjacent_197
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (198 : Fin 495) from rfl))
    intro h
    exact code_adjacent_198
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (199 : Fin 495) from rfl))
    intro h
    exact code_adjacent_199
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (200 : Fin 495) from rfl))
    intro h
    exact code_adjacent_200
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (201 : Fin 495) from rfl))
    intro h
    exact code_adjacent_201
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (202 : Fin 495) from rfl))
    intro h
    exact code_adjacent_202
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (203 : Fin 495) from rfl))
    intro h
    exact code_adjacent_203
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (204 : Fin 495) from rfl))
    intro h
    exact code_adjacent_204
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (205 : Fin 495) from rfl))
    intro h
    exact code_adjacent_205
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (206 : Fin 495) from rfl))
    intro h
    exact code_adjacent_206
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (207 : Fin 495) from rfl))
    intro h
    exact code_adjacent_207
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (208 : Fin 495) from rfl))
    intro h
    exact code_adjacent_208
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (209 : Fin 495) from rfl))
    intro h
    exact code_adjacent_209
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (210 : Fin 495) from rfl))
    intro h
    exact code_adjacent_210
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (211 : Fin 495) from rfl))
    intro h
    exact code_adjacent_211
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (212 : Fin 495) from rfl))
    intro h
    exact code_adjacent_212
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (213 : Fin 495) from rfl))
    intro h
    exact code_adjacent_213
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (214 : Fin 495) from rfl))
    intro h
    exact code_adjacent_214
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (215 : Fin 495) from rfl))
    intro h
    exact code_adjacent_215
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (216 : Fin 495) from rfl))
    intro h
    exact code_adjacent_216
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (217 : Fin 495) from rfl))
    intro h
    exact code_adjacent_217
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (218 : Fin 495) from rfl))
    intro h
    exact code_adjacent_218
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (219 : Fin 495) from rfl))
    intro h
    exact code_adjacent_219
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (220 : Fin 495) from rfl))
    intro h
    exact code_adjacent_220
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (221 : Fin 495) from rfl))
    intro h
    exact code_adjacent_221
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (222 : Fin 495) from rfl))
    intro h
    exact code_adjacent_222
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (223 : Fin 495) from rfl))
    intro h
    exact code_adjacent_223

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock06
