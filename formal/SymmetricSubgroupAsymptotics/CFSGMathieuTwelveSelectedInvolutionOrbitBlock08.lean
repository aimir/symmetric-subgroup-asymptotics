import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows256..287.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock08
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨256+i.val,by omega⟩

private theorem row_image_256 (p : Fin 12) :
    (rows 256).val p = rowForward 256 p := by
  calc
    (rows 256).val p = rowPoint 256 p := (rowPoint_eq 256 p).symm
    _ = rowForward 256 p := by fin_cases p <;> decide +kernel

private theorem transition_check_256 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 256) (generatorPermutation s p) =
      generatorPermutation s (rowForward 256 p) := by
  decide +kernel

private theorem code_encoding_256 :
    code 256 = ∑ p : Fin 12, (rowForward 256 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_256 : code 256 < code 257 := by
  decide +kernel

private theorem row_image_257 (p : Fin 12) :
    (rows 257).val p = rowForward 257 p := by
  calc
    (rows 257).val p = rowPoint 257 p := (rowPoint_eq 257 p).symm
    _ = rowForward 257 p := by fin_cases p <;> decide +kernel

private theorem transition_check_257 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 257) (generatorPermutation s p) =
      generatorPermutation s (rowForward 257 p) := by
  decide +kernel

private theorem code_encoding_257 :
    code 257 = ∑ p : Fin 12, (rowForward 257 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_257 : code 257 < code 258 := by
  decide +kernel

private theorem row_image_258 (p : Fin 12) :
    (rows 258).val p = rowForward 258 p := by
  calc
    (rows 258).val p = rowPoint 258 p := (rowPoint_eq 258 p).symm
    _ = rowForward 258 p := by fin_cases p <;> decide +kernel

private theorem transition_check_258 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 258) (generatorPermutation s p) =
      generatorPermutation s (rowForward 258 p) := by
  decide +kernel

private theorem code_encoding_258 :
    code 258 = ∑ p : Fin 12, (rowForward 258 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_258 : code 258 < code 259 := by
  decide +kernel

private theorem row_image_259 (p : Fin 12) :
    (rows 259).val p = rowForward 259 p := by
  calc
    (rows 259).val p = rowPoint 259 p := (rowPoint_eq 259 p).symm
    _ = rowForward 259 p := by fin_cases p <;> decide +kernel

private theorem transition_check_259 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 259) (generatorPermutation s p) =
      generatorPermutation s (rowForward 259 p) := by
  decide +kernel

private theorem code_encoding_259 :
    code 259 = ∑ p : Fin 12, (rowForward 259 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_259 : code 259 < code 260 := by
  decide +kernel

private theorem row_image_260 (p : Fin 12) :
    (rows 260).val p = rowForward 260 p := by
  calc
    (rows 260).val p = rowPoint 260 p := (rowPoint_eq 260 p).symm
    _ = rowForward 260 p := by fin_cases p <;> decide +kernel

private theorem transition_check_260 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 260) (generatorPermutation s p) =
      generatorPermutation s (rowForward 260 p) := by
  decide +kernel

private theorem code_encoding_260 :
    code 260 = ∑ p : Fin 12, (rowForward 260 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_260 : code 260 < code 261 := by
  decide +kernel

private theorem row_image_261 (p : Fin 12) :
    (rows 261).val p = rowForward 261 p := by
  calc
    (rows 261).val p = rowPoint 261 p := (rowPoint_eq 261 p).symm
    _ = rowForward 261 p := by fin_cases p <;> decide +kernel

private theorem transition_check_261 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 261) (generatorPermutation s p) =
      generatorPermutation s (rowForward 261 p) := by
  decide +kernel

private theorem code_encoding_261 :
    code 261 = ∑ p : Fin 12, (rowForward 261 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_261 : code 261 < code 262 := by
  decide +kernel

private theorem row_image_262 (p : Fin 12) :
    (rows 262).val p = rowForward 262 p := by
  calc
    (rows 262).val p = rowPoint 262 p := (rowPoint_eq 262 p).symm
    _ = rowForward 262 p := by fin_cases p <;> decide +kernel

private theorem transition_check_262 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 262) (generatorPermutation s p) =
      generatorPermutation s (rowForward 262 p) := by
  decide +kernel

private theorem code_encoding_262 :
    code 262 = ∑ p : Fin 12, (rowForward 262 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_262 : code 262 < code 263 := by
  decide +kernel

private theorem row_image_263 (p : Fin 12) :
    (rows 263).val p = rowForward 263 p := by
  calc
    (rows 263).val p = rowPoint 263 p := (rowPoint_eq 263 p).symm
    _ = rowForward 263 p := by fin_cases p <;> decide +kernel

private theorem transition_check_263 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 263) (generatorPermutation s p) =
      generatorPermutation s (rowForward 263 p) := by
  decide +kernel

private theorem code_encoding_263 :
    code 263 = ∑ p : Fin 12, (rowForward 263 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_263 : code 263 < code 264 := by
  decide +kernel

private theorem row_image_264 (p : Fin 12) :
    (rows 264).val p = rowForward 264 p := by
  calc
    (rows 264).val p = rowPoint 264 p := (rowPoint_eq 264 p).symm
    _ = rowForward 264 p := by fin_cases p <;> decide +kernel

private theorem transition_check_264 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 264) (generatorPermutation s p) =
      generatorPermutation s (rowForward 264 p) := by
  decide +kernel

private theorem code_encoding_264 :
    code 264 = ∑ p : Fin 12, (rowForward 264 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_264 : code 264 < code 265 := by
  decide +kernel

private theorem row_image_265 (p : Fin 12) :
    (rows 265).val p = rowForward 265 p := by
  calc
    (rows 265).val p = rowPoint 265 p := (rowPoint_eq 265 p).symm
    _ = rowForward 265 p := by fin_cases p <;> decide +kernel

private theorem transition_check_265 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 265) (generatorPermutation s p) =
      generatorPermutation s (rowForward 265 p) := by
  decide +kernel

private theorem code_encoding_265 :
    code 265 = ∑ p : Fin 12, (rowForward 265 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_265 : code 265 < code 266 := by
  decide +kernel

private theorem row_image_266 (p : Fin 12) :
    (rows 266).val p = rowForward 266 p := by
  calc
    (rows 266).val p = rowPoint 266 p := (rowPoint_eq 266 p).symm
    _ = rowForward 266 p := by fin_cases p <;> decide +kernel

private theorem transition_check_266 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 266) (generatorPermutation s p) =
      generatorPermutation s (rowForward 266 p) := by
  decide +kernel

private theorem code_encoding_266 :
    code 266 = ∑ p : Fin 12, (rowForward 266 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_266 : code 266 < code 267 := by
  decide +kernel

private theorem row_image_267 (p : Fin 12) :
    (rows 267).val p = rowForward 267 p := by
  calc
    (rows 267).val p = rowPoint 267 p := (rowPoint_eq 267 p).symm
    _ = rowForward 267 p := by fin_cases p <;> decide +kernel

private theorem transition_check_267 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 267) (generatorPermutation s p) =
      generatorPermutation s (rowForward 267 p) := by
  decide +kernel

private theorem code_encoding_267 :
    code 267 = ∑ p : Fin 12, (rowForward 267 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_267 : code 267 < code 268 := by
  decide +kernel

private theorem row_image_268 (p : Fin 12) :
    (rows 268).val p = rowForward 268 p := by
  calc
    (rows 268).val p = rowPoint 268 p := (rowPoint_eq 268 p).symm
    _ = rowForward 268 p := by fin_cases p <;> decide +kernel

private theorem transition_check_268 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 268) (generatorPermutation s p) =
      generatorPermutation s (rowForward 268 p) := by
  decide +kernel

private theorem code_encoding_268 :
    code 268 = ∑ p : Fin 12, (rowForward 268 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_268 : code 268 < code 269 := by
  decide +kernel

private theorem row_image_269 (p : Fin 12) :
    (rows 269).val p = rowForward 269 p := by
  calc
    (rows 269).val p = rowPoint 269 p := (rowPoint_eq 269 p).symm
    _ = rowForward 269 p := by fin_cases p <;> decide +kernel

private theorem transition_check_269 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 269) (generatorPermutation s p) =
      generatorPermutation s (rowForward 269 p) := by
  decide +kernel

private theorem code_encoding_269 :
    code 269 = ∑ p : Fin 12, (rowForward 269 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_269 : code 269 < code 270 := by
  decide +kernel

private theorem row_image_270 (p : Fin 12) :
    (rows 270).val p = rowForward 270 p := by
  calc
    (rows 270).val p = rowPoint 270 p := (rowPoint_eq 270 p).symm
    _ = rowForward 270 p := by fin_cases p <;> decide +kernel

private theorem transition_check_270 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 270) (generatorPermutation s p) =
      generatorPermutation s (rowForward 270 p) := by
  decide +kernel

private theorem code_encoding_270 :
    code 270 = ∑ p : Fin 12, (rowForward 270 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_270 : code 270 < code 271 := by
  decide +kernel

private theorem row_image_271 (p : Fin 12) :
    (rows 271).val p = rowForward 271 p := by
  calc
    (rows 271).val p = rowPoint 271 p := (rowPoint_eq 271 p).symm
    _ = rowForward 271 p := by fin_cases p <;> decide +kernel

private theorem transition_check_271 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 271) (generatorPermutation s p) =
      generatorPermutation s (rowForward 271 p) := by
  decide +kernel

private theorem code_encoding_271 :
    code 271 = ∑ p : Fin 12, (rowForward 271 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_271 : code 271 < code 272 := by
  decide +kernel

private theorem row_image_272 (p : Fin 12) :
    (rows 272).val p = rowForward 272 p := by
  calc
    (rows 272).val p = rowPoint 272 p := (rowPoint_eq 272 p).symm
    _ = rowForward 272 p := by fin_cases p <;> decide +kernel

private theorem transition_check_272 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 272) (generatorPermutation s p) =
      generatorPermutation s (rowForward 272 p) := by
  decide +kernel

private theorem code_encoding_272 :
    code 272 = ∑ p : Fin 12, (rowForward 272 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_272 : code 272 < code 273 := by
  decide +kernel

private theorem row_image_273 (p : Fin 12) :
    (rows 273).val p = rowForward 273 p := by
  calc
    (rows 273).val p = rowPoint 273 p := (rowPoint_eq 273 p).symm
    _ = rowForward 273 p := by fin_cases p <;> decide +kernel

private theorem transition_check_273 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 273) (generatorPermutation s p) =
      generatorPermutation s (rowForward 273 p) := by
  decide +kernel

private theorem code_encoding_273 :
    code 273 = ∑ p : Fin 12, (rowForward 273 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_273 : code 273 < code 274 := by
  decide +kernel

private theorem row_image_274 (p : Fin 12) :
    (rows 274).val p = rowForward 274 p := by
  calc
    (rows 274).val p = rowPoint 274 p := (rowPoint_eq 274 p).symm
    _ = rowForward 274 p := by fin_cases p <;> decide +kernel

private theorem transition_check_274 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 274) (generatorPermutation s p) =
      generatorPermutation s (rowForward 274 p) := by
  decide +kernel

private theorem code_encoding_274 :
    code 274 = ∑ p : Fin 12, (rowForward 274 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_274 : code 274 < code 275 := by
  decide +kernel

private theorem row_image_275 (p : Fin 12) :
    (rows 275).val p = rowForward 275 p := by
  calc
    (rows 275).val p = rowPoint 275 p := (rowPoint_eq 275 p).symm
    _ = rowForward 275 p := by fin_cases p <;> decide +kernel

private theorem transition_check_275 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 275) (generatorPermutation s p) =
      generatorPermutation s (rowForward 275 p) := by
  decide +kernel

private theorem code_encoding_275 :
    code 275 = ∑ p : Fin 12, (rowForward 275 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_275 : code 275 < code 276 := by
  decide +kernel

private theorem row_image_276 (p : Fin 12) :
    (rows 276).val p = rowForward 276 p := by
  calc
    (rows 276).val p = rowPoint 276 p := (rowPoint_eq 276 p).symm
    _ = rowForward 276 p := by fin_cases p <;> decide +kernel

private theorem transition_check_276 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 276) (generatorPermutation s p) =
      generatorPermutation s (rowForward 276 p) := by
  decide +kernel

private theorem code_encoding_276 :
    code 276 = ∑ p : Fin 12, (rowForward 276 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_276 : code 276 < code 277 := by
  decide +kernel

private theorem row_image_277 (p : Fin 12) :
    (rows 277).val p = rowForward 277 p := by
  calc
    (rows 277).val p = rowPoint 277 p := (rowPoint_eq 277 p).symm
    _ = rowForward 277 p := by fin_cases p <;> decide +kernel

private theorem transition_check_277 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 277) (generatorPermutation s p) =
      generatorPermutation s (rowForward 277 p) := by
  decide +kernel

private theorem code_encoding_277 :
    code 277 = ∑ p : Fin 12, (rowForward 277 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_277 : code 277 < code 278 := by
  decide +kernel

private theorem row_image_278 (p : Fin 12) :
    (rows 278).val p = rowForward 278 p := by
  calc
    (rows 278).val p = rowPoint 278 p := (rowPoint_eq 278 p).symm
    _ = rowForward 278 p := by fin_cases p <;> decide +kernel

private theorem transition_check_278 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 278) (generatorPermutation s p) =
      generatorPermutation s (rowForward 278 p) := by
  decide +kernel

private theorem code_encoding_278 :
    code 278 = ∑ p : Fin 12, (rowForward 278 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_278 : code 278 < code 279 := by
  decide +kernel

private theorem row_image_279 (p : Fin 12) :
    (rows 279).val p = rowForward 279 p := by
  calc
    (rows 279).val p = rowPoint 279 p := (rowPoint_eq 279 p).symm
    _ = rowForward 279 p := by fin_cases p <;> decide +kernel

private theorem transition_check_279 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 279) (generatorPermutation s p) =
      generatorPermutation s (rowForward 279 p) := by
  decide +kernel

private theorem code_encoding_279 :
    code 279 = ∑ p : Fin 12, (rowForward 279 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_279 : code 279 < code 280 := by
  decide +kernel

private theorem row_image_280 (p : Fin 12) :
    (rows 280).val p = rowForward 280 p := by
  calc
    (rows 280).val p = rowPoint 280 p := (rowPoint_eq 280 p).symm
    _ = rowForward 280 p := by fin_cases p <;> decide +kernel

private theorem transition_check_280 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 280) (generatorPermutation s p) =
      generatorPermutation s (rowForward 280 p) := by
  decide +kernel

private theorem code_encoding_280 :
    code 280 = ∑ p : Fin 12, (rowForward 280 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_280 : code 280 < code 281 := by
  decide +kernel

private theorem row_image_281 (p : Fin 12) :
    (rows 281).val p = rowForward 281 p := by
  calc
    (rows 281).val p = rowPoint 281 p := (rowPoint_eq 281 p).symm
    _ = rowForward 281 p := by fin_cases p <;> decide +kernel

private theorem transition_check_281 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 281) (generatorPermutation s p) =
      generatorPermutation s (rowForward 281 p) := by
  decide +kernel

private theorem code_encoding_281 :
    code 281 = ∑ p : Fin 12, (rowForward 281 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_281 : code 281 < code 282 := by
  decide +kernel

private theorem row_image_282 (p : Fin 12) :
    (rows 282).val p = rowForward 282 p := by
  calc
    (rows 282).val p = rowPoint 282 p := (rowPoint_eq 282 p).symm
    _ = rowForward 282 p := by fin_cases p <;> decide +kernel

private theorem transition_check_282 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 282) (generatorPermutation s p) =
      generatorPermutation s (rowForward 282 p) := by
  decide +kernel

private theorem code_encoding_282 :
    code 282 = ∑ p : Fin 12, (rowForward 282 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_282 : code 282 < code 283 := by
  decide +kernel

private theorem row_image_283 (p : Fin 12) :
    (rows 283).val p = rowForward 283 p := by
  calc
    (rows 283).val p = rowPoint 283 p := (rowPoint_eq 283 p).symm
    _ = rowForward 283 p := by fin_cases p <;> decide +kernel

private theorem transition_check_283 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 283) (generatorPermutation s p) =
      generatorPermutation s (rowForward 283 p) := by
  decide +kernel

private theorem code_encoding_283 :
    code 283 = ∑ p : Fin 12, (rowForward 283 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_283 : code 283 < code 284 := by
  decide +kernel

private theorem row_image_284 (p : Fin 12) :
    (rows 284).val p = rowForward 284 p := by
  calc
    (rows 284).val p = rowPoint 284 p := (rowPoint_eq 284 p).symm
    _ = rowForward 284 p := by fin_cases p <;> decide +kernel

private theorem transition_check_284 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 284) (generatorPermutation s p) =
      generatorPermutation s (rowForward 284 p) := by
  decide +kernel

private theorem code_encoding_284 :
    code 284 = ∑ p : Fin 12, (rowForward 284 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_284 : code 284 < code 285 := by
  decide +kernel

private theorem row_image_285 (p : Fin 12) :
    (rows 285).val p = rowForward 285 p := by
  calc
    (rows 285).val p = rowPoint 285 p := (rowPoint_eq 285 p).symm
    _ = rowForward 285 p := by fin_cases p <;> decide +kernel

private theorem transition_check_285 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 285) (generatorPermutation s p) =
      generatorPermutation s (rowForward 285 p) := by
  decide +kernel

private theorem code_encoding_285 :
    code 285 = ∑ p : Fin 12, (rowForward 285 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_285 : code 285 < code 286 := by
  decide +kernel

private theorem row_image_286 (p : Fin 12) :
    (rows 286).val p = rowForward 286 p := by
  calc
    (rows 286).val p = rowPoint 286 p := (rowPoint_eq 286 p).symm
    _ = rowForward 286 p := by fin_cases p <;> decide +kernel

private theorem transition_check_286 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 286) (generatorPermutation s p) =
      generatorPermutation s (rowForward 286 p) := by
  decide +kernel

private theorem code_encoding_286 :
    code 286 = ∑ p : Fin 12, (rowForward 286 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_286 : code 286 < code 287 := by
  decide +kernel

private theorem row_image_287 (p : Fin 12) :
    (rows 287).val p = rowForward 287 p := by
  calc
    (rows 287).val p = rowPoint 287 p := (rowPoint_eq 287 p).symm
    _ = rowForward 287 p := by fin_cases p <;> decide +kernel

private theorem transition_check_287 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 287) (generatorPermutation s p) =
      generatorPermutation s (rowForward 287 p) := by
  decide +kernel

private theorem code_encoding_287 :
    code 287 = ∑ p : Fin 12, (rowForward 287 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_287 : code 287 < code 288 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (256 : Fin 495) from rfl))
      (row_image_256 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (257 : Fin 495) from rfl))
      (row_image_257 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (258 : Fin 495) from rfl))
      (row_image_258 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (259 : Fin 495) from rfl))
      (row_image_259 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (260 : Fin 495) from rfl))
      (row_image_260 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (261 : Fin 495) from rfl))
      (row_image_261 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (262 : Fin 495) from rfl))
      (row_image_262 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (263 : Fin 495) from rfl))
      (row_image_263 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (264 : Fin 495) from rfl))
      (row_image_264 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (265 : Fin 495) from rfl))
      (row_image_265 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (266 : Fin 495) from rfl))
      (row_image_266 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (267 : Fin 495) from rfl))
      (row_image_267 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (268 : Fin 495) from rfl))
      (row_image_268 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (269 : Fin 495) from rfl))
      (row_image_269 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (270 : Fin 495) from rfl))
      (row_image_270 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (271 : Fin 495) from rfl))
      (row_image_271 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (272 : Fin 495) from rfl))
      (row_image_272 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (273 : Fin 495) from rfl))
      (row_image_273 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (274 : Fin 495) from rfl))
      (row_image_274 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (275 : Fin 495) from rfl))
      (row_image_275 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (276 : Fin 495) from rfl))
      (row_image_276 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (277 : Fin 495) from rfl))
      (row_image_277 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (278 : Fin 495) from rfl))
      (row_image_278 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (279 : Fin 495) from rfl))
      (row_image_279 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (280 : Fin 495) from rfl))
      (row_image_280 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (281 : Fin 495) from rfl))
      (row_image_281 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (282 : Fin 495) from rfl))
      (row_image_282 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (283 : Fin 495) from rfl))
      (row_image_283 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (284 : Fin 495) from rfl))
      (row_image_284 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (285 : Fin 495) from rfl))
      (row_image_285 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (286 : Fin 495) from rfl))
      (row_image_286 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (287 : Fin 495) from rfl))
      (row_image_287 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (256 : Fin 495) from rfl))
      (transition_check_256 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (257 : Fin 495) from rfl))
      (transition_check_257 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (258 : Fin 495) from rfl))
      (transition_check_258 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (259 : Fin 495) from rfl))
      (transition_check_259 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (260 : Fin 495) from rfl))
      (transition_check_260 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (261 : Fin 495) from rfl))
      (transition_check_261 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (262 : Fin 495) from rfl))
      (transition_check_262 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (263 : Fin 495) from rfl))
      (transition_check_263 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (264 : Fin 495) from rfl))
      (transition_check_264 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (265 : Fin 495) from rfl))
      (transition_check_265 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (266 : Fin 495) from rfl))
      (transition_check_266 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (267 : Fin 495) from rfl))
      (transition_check_267 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (268 : Fin 495) from rfl))
      (transition_check_268 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (269 : Fin 495) from rfl))
      (transition_check_269 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (270 : Fin 495) from rfl))
      (transition_check_270 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (271 : Fin 495) from rfl))
      (transition_check_271 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (272 : Fin 495) from rfl))
      (transition_check_272 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (273 : Fin 495) from rfl))
      (transition_check_273 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (274 : Fin 495) from rfl))
      (transition_check_274 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (275 : Fin 495) from rfl))
      (transition_check_275 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (276 : Fin 495) from rfl))
      (transition_check_276 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (277 : Fin 495) from rfl))
      (transition_check_277 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (278 : Fin 495) from rfl))
      (transition_check_278 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (279 : Fin 495) from rfl))
      (transition_check_279 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (280 : Fin 495) from rfl))
      (transition_check_280 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (281 : Fin 495) from rfl))
      (transition_check_281 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (282 : Fin 495) from rfl))
      (transition_check_282 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (283 : Fin 495) from rfl))
      (transition_check_283 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (284 : Fin 495) from rfl))
      (transition_check_284 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (285 : Fin 495) from rfl))
      (transition_check_285 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (286 : Fin 495) from rfl))
      (transition_check_286 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (287 : Fin 495) from rfl))
      (transition_check_287 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (256 : Fin 495) from rfl))
      code_encoding_256
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (257 : Fin 495) from rfl))
      code_encoding_257
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (258 : Fin 495) from rfl))
      code_encoding_258
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (259 : Fin 495) from rfl))
      code_encoding_259
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (260 : Fin 495) from rfl))
      code_encoding_260
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (261 : Fin 495) from rfl))
      code_encoding_261
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (262 : Fin 495) from rfl))
      code_encoding_262
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (263 : Fin 495) from rfl))
      code_encoding_263
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (264 : Fin 495) from rfl))
      code_encoding_264
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (265 : Fin 495) from rfl))
      code_encoding_265
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (266 : Fin 495) from rfl))
      code_encoding_266
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (267 : Fin 495) from rfl))
      code_encoding_267
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (268 : Fin 495) from rfl))
      code_encoding_268
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (269 : Fin 495) from rfl))
      code_encoding_269
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (270 : Fin 495) from rfl))
      code_encoding_270
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (271 : Fin 495) from rfl))
      code_encoding_271
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (272 : Fin 495) from rfl))
      code_encoding_272
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (273 : Fin 495) from rfl))
      code_encoding_273
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (274 : Fin 495) from rfl))
      code_encoding_274
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (275 : Fin 495) from rfl))
      code_encoding_275
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (276 : Fin 495) from rfl))
      code_encoding_276
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (277 : Fin 495) from rfl))
      code_encoding_277
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (278 : Fin 495) from rfl))
      code_encoding_278
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (279 : Fin 495) from rfl))
      code_encoding_279
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (280 : Fin 495) from rfl))
      code_encoding_280
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (281 : Fin 495) from rfl))
      code_encoding_281
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (282 : Fin 495) from rfl))
      code_encoding_282
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (283 : Fin 495) from rfl))
      code_encoding_283
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (284 : Fin 495) from rfl))
      code_encoding_284
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (285 : Fin 495) from rfl))
      code_encoding_285
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (286 : Fin 495) from rfl))
      code_encoding_286
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (287 : Fin 495) from rfl))
      code_encoding_287

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (256 : Fin 495) from rfl))
    intro h
    exact code_adjacent_256
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (257 : Fin 495) from rfl))
    intro h
    exact code_adjacent_257
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (258 : Fin 495) from rfl))
    intro h
    exact code_adjacent_258
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (259 : Fin 495) from rfl))
    intro h
    exact code_adjacent_259
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (260 : Fin 495) from rfl))
    intro h
    exact code_adjacent_260
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (261 : Fin 495) from rfl))
    intro h
    exact code_adjacent_261
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (262 : Fin 495) from rfl))
    intro h
    exact code_adjacent_262
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (263 : Fin 495) from rfl))
    intro h
    exact code_adjacent_263
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (264 : Fin 495) from rfl))
    intro h
    exact code_adjacent_264
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (265 : Fin 495) from rfl))
    intro h
    exact code_adjacent_265
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (266 : Fin 495) from rfl))
    intro h
    exact code_adjacent_266
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (267 : Fin 495) from rfl))
    intro h
    exact code_adjacent_267
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (268 : Fin 495) from rfl))
    intro h
    exact code_adjacent_268
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (269 : Fin 495) from rfl))
    intro h
    exact code_adjacent_269
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (270 : Fin 495) from rfl))
    intro h
    exact code_adjacent_270
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (271 : Fin 495) from rfl))
    intro h
    exact code_adjacent_271
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (272 : Fin 495) from rfl))
    intro h
    exact code_adjacent_272
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (273 : Fin 495) from rfl))
    intro h
    exact code_adjacent_273
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (274 : Fin 495) from rfl))
    intro h
    exact code_adjacent_274
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (275 : Fin 495) from rfl))
    intro h
    exact code_adjacent_275
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (276 : Fin 495) from rfl))
    intro h
    exact code_adjacent_276
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (277 : Fin 495) from rfl))
    intro h
    exact code_adjacent_277
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (278 : Fin 495) from rfl))
    intro h
    exact code_adjacent_278
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (279 : Fin 495) from rfl))
    intro h
    exact code_adjacent_279
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (280 : Fin 495) from rfl))
    intro h
    exact code_adjacent_280
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (281 : Fin 495) from rfl))
    intro h
    exact code_adjacent_281
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (282 : Fin 495) from rfl))
    intro h
    exact code_adjacent_282
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (283 : Fin 495) from rfl))
    intro h
    exact code_adjacent_283
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (284 : Fin 495) from rfl))
    intro h
    exact code_adjacent_284
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (285 : Fin 495) from rfl))
    intro h
    exact code_adjacent_285
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (286 : Fin 495) from rfl))
    intro h
    exact code_adjacent_286
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (287 : Fin 495) from rfl))
    intro h
    exact code_adjacent_287

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock08
