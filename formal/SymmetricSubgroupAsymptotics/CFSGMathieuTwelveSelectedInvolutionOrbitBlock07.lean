import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows224..255.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock07
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨224+i.val,by omega⟩

private theorem row_image_224 (p : Fin 12) :
    (rows 224).val p = rowForward 224 p := by
  calc
    (rows 224).val p = rowPoint 224 p := (rowPoint_eq 224 p).symm
    _ = rowForward 224 p := by fin_cases p <;> decide +kernel

private theorem transition_check_224 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 224) (generatorPermutation s p) =
      generatorPermutation s (rowForward 224 p) := by
  decide +kernel

private theorem code_encoding_224 :
    code 224 = ∑ p : Fin 12, (rowForward 224 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_224 : code 224 < code 225 := by
  decide +kernel

private theorem row_image_225 (p : Fin 12) :
    (rows 225).val p = rowForward 225 p := by
  calc
    (rows 225).val p = rowPoint 225 p := (rowPoint_eq 225 p).symm
    _ = rowForward 225 p := by fin_cases p <;> decide +kernel

private theorem transition_check_225 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 225) (generatorPermutation s p) =
      generatorPermutation s (rowForward 225 p) := by
  decide +kernel

private theorem code_encoding_225 :
    code 225 = ∑ p : Fin 12, (rowForward 225 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_225 : code 225 < code 226 := by
  decide +kernel

private theorem row_image_226 (p : Fin 12) :
    (rows 226).val p = rowForward 226 p := by
  calc
    (rows 226).val p = rowPoint 226 p := (rowPoint_eq 226 p).symm
    _ = rowForward 226 p := by fin_cases p <;> decide +kernel

private theorem transition_check_226 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 226) (generatorPermutation s p) =
      generatorPermutation s (rowForward 226 p) := by
  decide +kernel

private theorem code_encoding_226 :
    code 226 = ∑ p : Fin 12, (rowForward 226 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_226 : code 226 < code 227 := by
  decide +kernel

private theorem row_image_227 (p : Fin 12) :
    (rows 227).val p = rowForward 227 p := by
  calc
    (rows 227).val p = rowPoint 227 p := (rowPoint_eq 227 p).symm
    _ = rowForward 227 p := by fin_cases p <;> decide +kernel

private theorem transition_check_227 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 227) (generatorPermutation s p) =
      generatorPermutation s (rowForward 227 p) := by
  decide +kernel

private theorem code_encoding_227 :
    code 227 = ∑ p : Fin 12, (rowForward 227 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_227 : code 227 < code 228 := by
  decide +kernel

private theorem row_image_228 (p : Fin 12) :
    (rows 228).val p = rowForward 228 p := by
  calc
    (rows 228).val p = rowPoint 228 p := (rowPoint_eq 228 p).symm
    _ = rowForward 228 p := by fin_cases p <;> decide +kernel

private theorem transition_check_228 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 228) (generatorPermutation s p) =
      generatorPermutation s (rowForward 228 p) := by
  decide +kernel

private theorem code_encoding_228 :
    code 228 = ∑ p : Fin 12, (rowForward 228 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_228 : code 228 < code 229 := by
  decide +kernel

private theorem row_image_229 (p : Fin 12) :
    (rows 229).val p = rowForward 229 p := by
  calc
    (rows 229).val p = rowPoint 229 p := (rowPoint_eq 229 p).symm
    _ = rowForward 229 p := by fin_cases p <;> decide +kernel

private theorem transition_check_229 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 229) (generatorPermutation s p) =
      generatorPermutation s (rowForward 229 p) := by
  decide +kernel

private theorem code_encoding_229 :
    code 229 = ∑ p : Fin 12, (rowForward 229 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_229 : code 229 < code 230 := by
  decide +kernel

private theorem row_image_230 (p : Fin 12) :
    (rows 230).val p = rowForward 230 p := by
  calc
    (rows 230).val p = rowPoint 230 p := (rowPoint_eq 230 p).symm
    _ = rowForward 230 p := by fin_cases p <;> decide +kernel

private theorem transition_check_230 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 230) (generatorPermutation s p) =
      generatorPermutation s (rowForward 230 p) := by
  decide +kernel

private theorem code_encoding_230 :
    code 230 = ∑ p : Fin 12, (rowForward 230 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_230 : code 230 < code 231 := by
  decide +kernel

private theorem row_image_231 (p : Fin 12) :
    (rows 231).val p = rowForward 231 p := by
  calc
    (rows 231).val p = rowPoint 231 p := (rowPoint_eq 231 p).symm
    _ = rowForward 231 p := by fin_cases p <;> decide +kernel

private theorem transition_check_231 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 231) (generatorPermutation s p) =
      generatorPermutation s (rowForward 231 p) := by
  decide +kernel

private theorem code_encoding_231 :
    code 231 = ∑ p : Fin 12, (rowForward 231 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_231 : code 231 < code 232 := by
  decide +kernel

private theorem row_image_232 (p : Fin 12) :
    (rows 232).val p = rowForward 232 p := by
  calc
    (rows 232).val p = rowPoint 232 p := (rowPoint_eq 232 p).symm
    _ = rowForward 232 p := by fin_cases p <;> decide +kernel

private theorem transition_check_232 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 232) (generatorPermutation s p) =
      generatorPermutation s (rowForward 232 p) := by
  decide +kernel

private theorem code_encoding_232 :
    code 232 = ∑ p : Fin 12, (rowForward 232 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_232 : code 232 < code 233 := by
  decide +kernel

private theorem row_image_233 (p : Fin 12) :
    (rows 233).val p = rowForward 233 p := by
  calc
    (rows 233).val p = rowPoint 233 p := (rowPoint_eq 233 p).symm
    _ = rowForward 233 p := by fin_cases p <;> decide +kernel

private theorem transition_check_233 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 233) (generatorPermutation s p) =
      generatorPermutation s (rowForward 233 p) := by
  decide +kernel

private theorem code_encoding_233 :
    code 233 = ∑ p : Fin 12, (rowForward 233 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_233 : code 233 < code 234 := by
  decide +kernel

private theorem row_image_234 (p : Fin 12) :
    (rows 234).val p = rowForward 234 p := by
  calc
    (rows 234).val p = rowPoint 234 p := (rowPoint_eq 234 p).symm
    _ = rowForward 234 p := by fin_cases p <;> decide +kernel

private theorem transition_check_234 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 234) (generatorPermutation s p) =
      generatorPermutation s (rowForward 234 p) := by
  decide +kernel

private theorem code_encoding_234 :
    code 234 = ∑ p : Fin 12, (rowForward 234 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_234 : code 234 < code 235 := by
  decide +kernel

private theorem row_image_235 (p : Fin 12) :
    (rows 235).val p = rowForward 235 p := by
  calc
    (rows 235).val p = rowPoint 235 p := (rowPoint_eq 235 p).symm
    _ = rowForward 235 p := by fin_cases p <;> decide +kernel

private theorem transition_check_235 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 235) (generatorPermutation s p) =
      generatorPermutation s (rowForward 235 p) := by
  decide +kernel

private theorem code_encoding_235 :
    code 235 = ∑ p : Fin 12, (rowForward 235 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_235 : code 235 < code 236 := by
  decide +kernel

private theorem row_image_236 (p : Fin 12) :
    (rows 236).val p = rowForward 236 p := by
  calc
    (rows 236).val p = rowPoint 236 p := (rowPoint_eq 236 p).symm
    _ = rowForward 236 p := by fin_cases p <;> decide +kernel

private theorem transition_check_236 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 236) (generatorPermutation s p) =
      generatorPermutation s (rowForward 236 p) := by
  decide +kernel

private theorem code_encoding_236 :
    code 236 = ∑ p : Fin 12, (rowForward 236 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_236 : code 236 < code 237 := by
  decide +kernel

private theorem row_image_237 (p : Fin 12) :
    (rows 237).val p = rowForward 237 p := by
  calc
    (rows 237).val p = rowPoint 237 p := (rowPoint_eq 237 p).symm
    _ = rowForward 237 p := by fin_cases p <;> decide +kernel

private theorem transition_check_237 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 237) (generatorPermutation s p) =
      generatorPermutation s (rowForward 237 p) := by
  decide +kernel

private theorem code_encoding_237 :
    code 237 = ∑ p : Fin 12, (rowForward 237 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_237 : code 237 < code 238 := by
  decide +kernel

private theorem row_image_238 (p : Fin 12) :
    (rows 238).val p = rowForward 238 p := by
  calc
    (rows 238).val p = rowPoint 238 p := (rowPoint_eq 238 p).symm
    _ = rowForward 238 p := by fin_cases p <;> decide +kernel

private theorem transition_check_238 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 238) (generatorPermutation s p) =
      generatorPermutation s (rowForward 238 p) := by
  decide +kernel

private theorem code_encoding_238 :
    code 238 = ∑ p : Fin 12, (rowForward 238 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_238 : code 238 < code 239 := by
  decide +kernel

private theorem row_image_239 (p : Fin 12) :
    (rows 239).val p = rowForward 239 p := by
  calc
    (rows 239).val p = rowPoint 239 p := (rowPoint_eq 239 p).symm
    _ = rowForward 239 p := by fin_cases p <;> decide +kernel

private theorem transition_check_239 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 239) (generatorPermutation s p) =
      generatorPermutation s (rowForward 239 p) := by
  decide +kernel

private theorem code_encoding_239 :
    code 239 = ∑ p : Fin 12, (rowForward 239 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_239 : code 239 < code 240 := by
  decide +kernel

private theorem row_image_240 (p : Fin 12) :
    (rows 240).val p = rowForward 240 p := by
  calc
    (rows 240).val p = rowPoint 240 p := (rowPoint_eq 240 p).symm
    _ = rowForward 240 p := by fin_cases p <;> decide +kernel

private theorem transition_check_240 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 240) (generatorPermutation s p) =
      generatorPermutation s (rowForward 240 p) := by
  decide +kernel

private theorem code_encoding_240 :
    code 240 = ∑ p : Fin 12, (rowForward 240 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_240 : code 240 < code 241 := by
  decide +kernel

private theorem row_image_241 (p : Fin 12) :
    (rows 241).val p = rowForward 241 p := by
  calc
    (rows 241).val p = rowPoint 241 p := (rowPoint_eq 241 p).symm
    _ = rowForward 241 p := by fin_cases p <;> decide +kernel

private theorem transition_check_241 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 241) (generatorPermutation s p) =
      generatorPermutation s (rowForward 241 p) := by
  decide +kernel

private theorem code_encoding_241 :
    code 241 = ∑ p : Fin 12, (rowForward 241 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_241 : code 241 < code 242 := by
  decide +kernel

private theorem row_image_242 (p : Fin 12) :
    (rows 242).val p = rowForward 242 p := by
  calc
    (rows 242).val p = rowPoint 242 p := (rowPoint_eq 242 p).symm
    _ = rowForward 242 p := by fin_cases p <;> decide +kernel

private theorem transition_check_242 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 242) (generatorPermutation s p) =
      generatorPermutation s (rowForward 242 p) := by
  decide +kernel

private theorem code_encoding_242 :
    code 242 = ∑ p : Fin 12, (rowForward 242 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_242 : code 242 < code 243 := by
  decide +kernel

private theorem row_image_243 (p : Fin 12) :
    (rows 243).val p = rowForward 243 p := by
  calc
    (rows 243).val p = rowPoint 243 p := (rowPoint_eq 243 p).symm
    _ = rowForward 243 p := by fin_cases p <;> decide +kernel

private theorem transition_check_243 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 243) (generatorPermutation s p) =
      generatorPermutation s (rowForward 243 p) := by
  decide +kernel

private theorem code_encoding_243 :
    code 243 = ∑ p : Fin 12, (rowForward 243 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_243 : code 243 < code 244 := by
  decide +kernel

private theorem row_image_244 (p : Fin 12) :
    (rows 244).val p = rowForward 244 p := by
  calc
    (rows 244).val p = rowPoint 244 p := (rowPoint_eq 244 p).symm
    _ = rowForward 244 p := by fin_cases p <;> decide +kernel

private theorem transition_check_244 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 244) (generatorPermutation s p) =
      generatorPermutation s (rowForward 244 p) := by
  decide +kernel

private theorem code_encoding_244 :
    code 244 = ∑ p : Fin 12, (rowForward 244 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_244 : code 244 < code 245 := by
  decide +kernel

private theorem row_image_245 (p : Fin 12) :
    (rows 245).val p = rowForward 245 p := by
  calc
    (rows 245).val p = rowPoint 245 p := (rowPoint_eq 245 p).symm
    _ = rowForward 245 p := by fin_cases p <;> decide +kernel

private theorem transition_check_245 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 245) (generatorPermutation s p) =
      generatorPermutation s (rowForward 245 p) := by
  decide +kernel

private theorem code_encoding_245 :
    code 245 = ∑ p : Fin 12, (rowForward 245 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_245 : code 245 < code 246 := by
  decide +kernel

private theorem row_image_246 (p : Fin 12) :
    (rows 246).val p = rowForward 246 p := by
  calc
    (rows 246).val p = rowPoint 246 p := (rowPoint_eq 246 p).symm
    _ = rowForward 246 p := by fin_cases p <;> decide +kernel

private theorem transition_check_246 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 246) (generatorPermutation s p) =
      generatorPermutation s (rowForward 246 p) := by
  decide +kernel

private theorem code_encoding_246 :
    code 246 = ∑ p : Fin 12, (rowForward 246 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_246 : code 246 < code 247 := by
  decide +kernel

private theorem row_image_247 (p : Fin 12) :
    (rows 247).val p = rowForward 247 p := by
  calc
    (rows 247).val p = rowPoint 247 p := (rowPoint_eq 247 p).symm
    _ = rowForward 247 p := by fin_cases p <;> decide +kernel

private theorem transition_check_247 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 247) (generatorPermutation s p) =
      generatorPermutation s (rowForward 247 p) := by
  decide +kernel

private theorem code_encoding_247 :
    code 247 = ∑ p : Fin 12, (rowForward 247 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_247 : code 247 < code 248 := by
  decide +kernel

private theorem row_image_248 (p : Fin 12) :
    (rows 248).val p = rowForward 248 p := by
  calc
    (rows 248).val p = rowPoint 248 p := (rowPoint_eq 248 p).symm
    _ = rowForward 248 p := by fin_cases p <;> decide +kernel

private theorem transition_check_248 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 248) (generatorPermutation s p) =
      generatorPermutation s (rowForward 248 p) := by
  decide +kernel

private theorem code_encoding_248 :
    code 248 = ∑ p : Fin 12, (rowForward 248 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_248 : code 248 < code 249 := by
  decide +kernel

private theorem row_image_249 (p : Fin 12) :
    (rows 249).val p = rowForward 249 p := by
  calc
    (rows 249).val p = rowPoint 249 p := (rowPoint_eq 249 p).symm
    _ = rowForward 249 p := by fin_cases p <;> decide +kernel

private theorem transition_check_249 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 249) (generatorPermutation s p) =
      generatorPermutation s (rowForward 249 p) := by
  decide +kernel

private theorem code_encoding_249 :
    code 249 = ∑ p : Fin 12, (rowForward 249 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_249 : code 249 < code 250 := by
  decide +kernel

private theorem row_image_250 (p : Fin 12) :
    (rows 250).val p = rowForward 250 p := by
  calc
    (rows 250).val p = rowPoint 250 p := (rowPoint_eq 250 p).symm
    _ = rowForward 250 p := by fin_cases p <;> decide +kernel

private theorem transition_check_250 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 250) (generatorPermutation s p) =
      generatorPermutation s (rowForward 250 p) := by
  decide +kernel

private theorem code_encoding_250 :
    code 250 = ∑ p : Fin 12, (rowForward 250 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_250 : code 250 < code 251 := by
  decide +kernel

private theorem row_image_251 (p : Fin 12) :
    (rows 251).val p = rowForward 251 p := by
  calc
    (rows 251).val p = rowPoint 251 p := (rowPoint_eq 251 p).symm
    _ = rowForward 251 p := by fin_cases p <;> decide +kernel

private theorem transition_check_251 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 251) (generatorPermutation s p) =
      generatorPermutation s (rowForward 251 p) := by
  decide +kernel

private theorem code_encoding_251 :
    code 251 = ∑ p : Fin 12, (rowForward 251 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_251 : code 251 < code 252 := by
  decide +kernel

private theorem row_image_252 (p : Fin 12) :
    (rows 252).val p = rowForward 252 p := by
  calc
    (rows 252).val p = rowPoint 252 p := (rowPoint_eq 252 p).symm
    _ = rowForward 252 p := by fin_cases p <;> decide +kernel

private theorem transition_check_252 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 252) (generatorPermutation s p) =
      generatorPermutation s (rowForward 252 p) := by
  decide +kernel

private theorem code_encoding_252 :
    code 252 = ∑ p : Fin 12, (rowForward 252 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_252 : code 252 < code 253 := by
  decide +kernel

private theorem row_image_253 (p : Fin 12) :
    (rows 253).val p = rowForward 253 p := by
  calc
    (rows 253).val p = rowPoint 253 p := (rowPoint_eq 253 p).symm
    _ = rowForward 253 p := by fin_cases p <;> decide +kernel

private theorem transition_check_253 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 253) (generatorPermutation s p) =
      generatorPermutation s (rowForward 253 p) := by
  decide +kernel

private theorem code_encoding_253 :
    code 253 = ∑ p : Fin 12, (rowForward 253 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_253 : code 253 < code 254 := by
  decide +kernel

private theorem row_image_254 (p : Fin 12) :
    (rows 254).val p = rowForward 254 p := by
  calc
    (rows 254).val p = rowPoint 254 p := (rowPoint_eq 254 p).symm
    _ = rowForward 254 p := by fin_cases p <;> decide +kernel

private theorem transition_check_254 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 254) (generatorPermutation s p) =
      generatorPermutation s (rowForward 254 p) := by
  decide +kernel

private theorem code_encoding_254 :
    code 254 = ∑ p : Fin 12, (rowForward 254 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_254 : code 254 < code 255 := by
  decide +kernel

private theorem row_image_255 (p : Fin 12) :
    (rows 255).val p = rowForward 255 p := by
  calc
    (rows 255).val p = rowPoint 255 p := (rowPoint_eq 255 p).symm
    _ = rowForward 255 p := by fin_cases p <;> decide +kernel

private theorem transition_check_255 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 255) (generatorPermutation s p) =
      generatorPermutation s (rowForward 255 p) := by
  decide +kernel

private theorem code_encoding_255 :
    code 255 = ∑ p : Fin 12, (rowForward 255 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_255 : code 255 < code 256 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (224 : Fin 495) from rfl))
      (row_image_224 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (225 : Fin 495) from rfl))
      (row_image_225 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (226 : Fin 495) from rfl))
      (row_image_226 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (227 : Fin 495) from rfl))
      (row_image_227 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (228 : Fin 495) from rfl))
      (row_image_228 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (229 : Fin 495) from rfl))
      (row_image_229 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (230 : Fin 495) from rfl))
      (row_image_230 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (231 : Fin 495) from rfl))
      (row_image_231 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (232 : Fin 495) from rfl))
      (row_image_232 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (233 : Fin 495) from rfl))
      (row_image_233 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (234 : Fin 495) from rfl))
      (row_image_234 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (235 : Fin 495) from rfl))
      (row_image_235 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (236 : Fin 495) from rfl))
      (row_image_236 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (237 : Fin 495) from rfl))
      (row_image_237 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (238 : Fin 495) from rfl))
      (row_image_238 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (239 : Fin 495) from rfl))
      (row_image_239 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (240 : Fin 495) from rfl))
      (row_image_240 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (241 : Fin 495) from rfl))
      (row_image_241 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (242 : Fin 495) from rfl))
      (row_image_242 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (243 : Fin 495) from rfl))
      (row_image_243 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (244 : Fin 495) from rfl))
      (row_image_244 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (245 : Fin 495) from rfl))
      (row_image_245 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (246 : Fin 495) from rfl))
      (row_image_246 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (247 : Fin 495) from rfl))
      (row_image_247 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (248 : Fin 495) from rfl))
      (row_image_248 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (249 : Fin 495) from rfl))
      (row_image_249 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (250 : Fin 495) from rfl))
      (row_image_250 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (251 : Fin 495) from rfl))
      (row_image_251 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (252 : Fin 495) from rfl))
      (row_image_252 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (253 : Fin 495) from rfl))
      (row_image_253 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (254 : Fin 495) from rfl))
      (row_image_254 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (255 : Fin 495) from rfl))
      (row_image_255 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (224 : Fin 495) from rfl))
      (transition_check_224 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (225 : Fin 495) from rfl))
      (transition_check_225 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (226 : Fin 495) from rfl))
      (transition_check_226 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (227 : Fin 495) from rfl))
      (transition_check_227 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (228 : Fin 495) from rfl))
      (transition_check_228 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (229 : Fin 495) from rfl))
      (transition_check_229 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (230 : Fin 495) from rfl))
      (transition_check_230 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (231 : Fin 495) from rfl))
      (transition_check_231 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (232 : Fin 495) from rfl))
      (transition_check_232 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (233 : Fin 495) from rfl))
      (transition_check_233 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (234 : Fin 495) from rfl))
      (transition_check_234 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (235 : Fin 495) from rfl))
      (transition_check_235 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (236 : Fin 495) from rfl))
      (transition_check_236 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (237 : Fin 495) from rfl))
      (transition_check_237 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (238 : Fin 495) from rfl))
      (transition_check_238 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (239 : Fin 495) from rfl))
      (transition_check_239 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (240 : Fin 495) from rfl))
      (transition_check_240 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (241 : Fin 495) from rfl))
      (transition_check_241 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (242 : Fin 495) from rfl))
      (transition_check_242 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (243 : Fin 495) from rfl))
      (transition_check_243 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (244 : Fin 495) from rfl))
      (transition_check_244 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (245 : Fin 495) from rfl))
      (transition_check_245 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (246 : Fin 495) from rfl))
      (transition_check_246 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (247 : Fin 495) from rfl))
      (transition_check_247 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (248 : Fin 495) from rfl))
      (transition_check_248 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (249 : Fin 495) from rfl))
      (transition_check_249 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (250 : Fin 495) from rfl))
      (transition_check_250 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (251 : Fin 495) from rfl))
      (transition_check_251 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (252 : Fin 495) from rfl))
      (transition_check_252 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (253 : Fin 495) from rfl))
      (transition_check_253 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (254 : Fin 495) from rfl))
      (transition_check_254 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (255 : Fin 495) from rfl))
      (transition_check_255 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (224 : Fin 495) from rfl))
      code_encoding_224
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (225 : Fin 495) from rfl))
      code_encoding_225
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (226 : Fin 495) from rfl))
      code_encoding_226
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (227 : Fin 495) from rfl))
      code_encoding_227
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (228 : Fin 495) from rfl))
      code_encoding_228
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (229 : Fin 495) from rfl))
      code_encoding_229
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (230 : Fin 495) from rfl))
      code_encoding_230
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (231 : Fin 495) from rfl))
      code_encoding_231
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (232 : Fin 495) from rfl))
      code_encoding_232
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (233 : Fin 495) from rfl))
      code_encoding_233
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (234 : Fin 495) from rfl))
      code_encoding_234
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (235 : Fin 495) from rfl))
      code_encoding_235
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (236 : Fin 495) from rfl))
      code_encoding_236
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (237 : Fin 495) from rfl))
      code_encoding_237
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (238 : Fin 495) from rfl))
      code_encoding_238
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (239 : Fin 495) from rfl))
      code_encoding_239
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (240 : Fin 495) from rfl))
      code_encoding_240
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (241 : Fin 495) from rfl))
      code_encoding_241
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (242 : Fin 495) from rfl))
      code_encoding_242
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (243 : Fin 495) from rfl))
      code_encoding_243
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (244 : Fin 495) from rfl))
      code_encoding_244
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (245 : Fin 495) from rfl))
      code_encoding_245
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (246 : Fin 495) from rfl))
      code_encoding_246
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (247 : Fin 495) from rfl))
      code_encoding_247
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (248 : Fin 495) from rfl))
      code_encoding_248
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (249 : Fin 495) from rfl))
      code_encoding_249
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (250 : Fin 495) from rfl))
      code_encoding_250
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (251 : Fin 495) from rfl))
      code_encoding_251
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (252 : Fin 495) from rfl))
      code_encoding_252
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (253 : Fin 495) from rfl))
      code_encoding_253
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (254 : Fin 495) from rfl))
      code_encoding_254
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (255 : Fin 495) from rfl))
      code_encoding_255

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (224 : Fin 495) from rfl))
    intro h
    exact code_adjacent_224
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (225 : Fin 495) from rfl))
    intro h
    exact code_adjacent_225
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (226 : Fin 495) from rfl))
    intro h
    exact code_adjacent_226
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (227 : Fin 495) from rfl))
    intro h
    exact code_adjacent_227
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (228 : Fin 495) from rfl))
    intro h
    exact code_adjacent_228
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (229 : Fin 495) from rfl))
    intro h
    exact code_adjacent_229
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (230 : Fin 495) from rfl))
    intro h
    exact code_adjacent_230
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (231 : Fin 495) from rfl))
    intro h
    exact code_adjacent_231
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (232 : Fin 495) from rfl))
    intro h
    exact code_adjacent_232
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (233 : Fin 495) from rfl))
    intro h
    exact code_adjacent_233
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (234 : Fin 495) from rfl))
    intro h
    exact code_adjacent_234
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (235 : Fin 495) from rfl))
    intro h
    exact code_adjacent_235
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (236 : Fin 495) from rfl))
    intro h
    exact code_adjacent_236
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (237 : Fin 495) from rfl))
    intro h
    exact code_adjacent_237
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (238 : Fin 495) from rfl))
    intro h
    exact code_adjacent_238
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (239 : Fin 495) from rfl))
    intro h
    exact code_adjacent_239
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (240 : Fin 495) from rfl))
    intro h
    exact code_adjacent_240
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (241 : Fin 495) from rfl))
    intro h
    exact code_adjacent_241
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (242 : Fin 495) from rfl))
    intro h
    exact code_adjacent_242
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (243 : Fin 495) from rfl))
    intro h
    exact code_adjacent_243
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (244 : Fin 495) from rfl))
    intro h
    exact code_adjacent_244
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (245 : Fin 495) from rfl))
    intro h
    exact code_adjacent_245
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (246 : Fin 495) from rfl))
    intro h
    exact code_adjacent_246
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (247 : Fin 495) from rfl))
    intro h
    exact code_adjacent_247
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (248 : Fin 495) from rfl))
    intro h
    exact code_adjacent_248
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (249 : Fin 495) from rfl))
    intro h
    exact code_adjacent_249
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (250 : Fin 495) from rfl))
    intro h
    exact code_adjacent_250
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (251 : Fin 495) from rfl))
    intro h
    exact code_adjacent_251
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (252 : Fin 495) from rfl))
    intro h
    exact code_adjacent_252
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (253 : Fin 495) from rfl))
    intro h
    exact code_adjacent_253
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (254 : Fin 495) from rfl))
    intro h
    exact code_adjacent_254
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (255 : Fin 495) from rfl))
    intro h
    exact code_adjacent_255

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock07
