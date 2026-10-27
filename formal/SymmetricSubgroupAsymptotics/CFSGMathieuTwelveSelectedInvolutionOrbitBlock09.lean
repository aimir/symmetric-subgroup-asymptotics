import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows288..319.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock09
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨288+i.val,by omega⟩

private theorem row_image_288 (p : Fin 12) :
    (rows 288).val p = rowForward 288 p := by
  calc
    (rows 288).val p = rowPoint 288 p := (rowPoint_eq 288 p).symm
    _ = rowForward 288 p := by fin_cases p <;> decide +kernel

private theorem transition_check_288 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 288) (generatorPermutation s p) =
      generatorPermutation s (rowForward 288 p) := by
  decide +kernel

private theorem code_encoding_288 :
    code 288 = ∑ p : Fin 12, (rowForward 288 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_288 : code 288 < code 289 := by
  decide +kernel

private theorem row_image_289 (p : Fin 12) :
    (rows 289).val p = rowForward 289 p := by
  calc
    (rows 289).val p = rowPoint 289 p := (rowPoint_eq 289 p).symm
    _ = rowForward 289 p := by fin_cases p <;> decide +kernel

private theorem transition_check_289 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 289) (generatorPermutation s p) =
      generatorPermutation s (rowForward 289 p) := by
  decide +kernel

private theorem code_encoding_289 :
    code 289 = ∑ p : Fin 12, (rowForward 289 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_289 : code 289 < code 290 := by
  decide +kernel

private theorem row_image_290 (p : Fin 12) :
    (rows 290).val p = rowForward 290 p := by
  calc
    (rows 290).val p = rowPoint 290 p := (rowPoint_eq 290 p).symm
    _ = rowForward 290 p := by fin_cases p <;> decide +kernel

private theorem transition_check_290 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 290) (generatorPermutation s p) =
      generatorPermutation s (rowForward 290 p) := by
  decide +kernel

private theorem code_encoding_290 :
    code 290 = ∑ p : Fin 12, (rowForward 290 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_290 : code 290 < code 291 := by
  decide +kernel

private theorem row_image_291 (p : Fin 12) :
    (rows 291).val p = rowForward 291 p := by
  calc
    (rows 291).val p = rowPoint 291 p := (rowPoint_eq 291 p).symm
    _ = rowForward 291 p := by fin_cases p <;> decide +kernel

private theorem transition_check_291 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 291) (generatorPermutation s p) =
      generatorPermutation s (rowForward 291 p) := by
  decide +kernel

private theorem code_encoding_291 :
    code 291 = ∑ p : Fin 12, (rowForward 291 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_291 : code 291 < code 292 := by
  decide +kernel

private theorem row_image_292 (p : Fin 12) :
    (rows 292).val p = rowForward 292 p := by
  calc
    (rows 292).val p = rowPoint 292 p := (rowPoint_eq 292 p).symm
    _ = rowForward 292 p := by fin_cases p <;> decide +kernel

private theorem transition_check_292 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 292) (generatorPermutation s p) =
      generatorPermutation s (rowForward 292 p) := by
  decide +kernel

private theorem code_encoding_292 :
    code 292 = ∑ p : Fin 12, (rowForward 292 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_292 : code 292 < code 293 := by
  decide +kernel

private theorem row_image_293 (p : Fin 12) :
    (rows 293).val p = rowForward 293 p := by
  calc
    (rows 293).val p = rowPoint 293 p := (rowPoint_eq 293 p).symm
    _ = rowForward 293 p := by fin_cases p <;> decide +kernel

private theorem transition_check_293 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 293) (generatorPermutation s p) =
      generatorPermutation s (rowForward 293 p) := by
  decide +kernel

private theorem code_encoding_293 :
    code 293 = ∑ p : Fin 12, (rowForward 293 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_293 : code 293 < code 294 := by
  decide +kernel

private theorem row_image_294 (p : Fin 12) :
    (rows 294).val p = rowForward 294 p := by
  calc
    (rows 294).val p = rowPoint 294 p := (rowPoint_eq 294 p).symm
    _ = rowForward 294 p := by fin_cases p <;> decide +kernel

private theorem transition_check_294 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 294) (generatorPermutation s p) =
      generatorPermutation s (rowForward 294 p) := by
  decide +kernel

private theorem code_encoding_294 :
    code 294 = ∑ p : Fin 12, (rowForward 294 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_294 : code 294 < code 295 := by
  decide +kernel

private theorem row_image_295 (p : Fin 12) :
    (rows 295).val p = rowForward 295 p := by
  calc
    (rows 295).val p = rowPoint 295 p := (rowPoint_eq 295 p).symm
    _ = rowForward 295 p := by fin_cases p <;> decide +kernel

private theorem transition_check_295 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 295) (generatorPermutation s p) =
      generatorPermutation s (rowForward 295 p) := by
  decide +kernel

private theorem code_encoding_295 :
    code 295 = ∑ p : Fin 12, (rowForward 295 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_295 : code 295 < code 296 := by
  decide +kernel

private theorem row_image_296 (p : Fin 12) :
    (rows 296).val p = rowForward 296 p := by
  calc
    (rows 296).val p = rowPoint 296 p := (rowPoint_eq 296 p).symm
    _ = rowForward 296 p := by fin_cases p <;> decide +kernel

private theorem transition_check_296 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 296) (generatorPermutation s p) =
      generatorPermutation s (rowForward 296 p) := by
  decide +kernel

private theorem code_encoding_296 :
    code 296 = ∑ p : Fin 12, (rowForward 296 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_296 : code 296 < code 297 := by
  decide +kernel

private theorem row_image_297 (p : Fin 12) :
    (rows 297).val p = rowForward 297 p := by
  calc
    (rows 297).val p = rowPoint 297 p := (rowPoint_eq 297 p).symm
    _ = rowForward 297 p := by fin_cases p <;> decide +kernel

private theorem transition_check_297 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 297) (generatorPermutation s p) =
      generatorPermutation s (rowForward 297 p) := by
  decide +kernel

private theorem code_encoding_297 :
    code 297 = ∑ p : Fin 12, (rowForward 297 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_297 : code 297 < code 298 := by
  decide +kernel

private theorem row_image_298 (p : Fin 12) :
    (rows 298).val p = rowForward 298 p := by
  calc
    (rows 298).val p = rowPoint 298 p := (rowPoint_eq 298 p).symm
    _ = rowForward 298 p := by fin_cases p <;> decide +kernel

private theorem transition_check_298 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 298) (generatorPermutation s p) =
      generatorPermutation s (rowForward 298 p) := by
  decide +kernel

private theorem code_encoding_298 :
    code 298 = ∑ p : Fin 12, (rowForward 298 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_298 : code 298 < code 299 := by
  decide +kernel

private theorem row_image_299 (p : Fin 12) :
    (rows 299).val p = rowForward 299 p := by
  calc
    (rows 299).val p = rowPoint 299 p := (rowPoint_eq 299 p).symm
    _ = rowForward 299 p := by fin_cases p <;> decide +kernel

private theorem transition_check_299 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 299) (generatorPermutation s p) =
      generatorPermutation s (rowForward 299 p) := by
  decide +kernel

private theorem code_encoding_299 :
    code 299 = ∑ p : Fin 12, (rowForward 299 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_299 : code 299 < code 300 := by
  decide +kernel

private theorem row_image_300 (p : Fin 12) :
    (rows 300).val p = rowForward 300 p := by
  calc
    (rows 300).val p = rowPoint 300 p := (rowPoint_eq 300 p).symm
    _ = rowForward 300 p := by fin_cases p <;> decide +kernel

private theorem transition_check_300 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 300) (generatorPermutation s p) =
      generatorPermutation s (rowForward 300 p) := by
  decide +kernel

private theorem code_encoding_300 :
    code 300 = ∑ p : Fin 12, (rowForward 300 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_300 : code 300 < code 301 := by
  decide +kernel

private theorem row_image_301 (p : Fin 12) :
    (rows 301).val p = rowForward 301 p := by
  calc
    (rows 301).val p = rowPoint 301 p := (rowPoint_eq 301 p).symm
    _ = rowForward 301 p := by fin_cases p <;> decide +kernel

private theorem transition_check_301 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 301) (generatorPermutation s p) =
      generatorPermutation s (rowForward 301 p) := by
  decide +kernel

private theorem code_encoding_301 :
    code 301 = ∑ p : Fin 12, (rowForward 301 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_301 : code 301 < code 302 := by
  decide +kernel

private theorem row_image_302 (p : Fin 12) :
    (rows 302).val p = rowForward 302 p := by
  calc
    (rows 302).val p = rowPoint 302 p := (rowPoint_eq 302 p).symm
    _ = rowForward 302 p := by fin_cases p <;> decide +kernel

private theorem transition_check_302 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 302) (generatorPermutation s p) =
      generatorPermutation s (rowForward 302 p) := by
  decide +kernel

private theorem code_encoding_302 :
    code 302 = ∑ p : Fin 12, (rowForward 302 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_302 : code 302 < code 303 := by
  decide +kernel

private theorem row_image_303 (p : Fin 12) :
    (rows 303).val p = rowForward 303 p := by
  calc
    (rows 303).val p = rowPoint 303 p := (rowPoint_eq 303 p).symm
    _ = rowForward 303 p := by fin_cases p <;> decide +kernel

private theorem transition_check_303 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 303) (generatorPermutation s p) =
      generatorPermutation s (rowForward 303 p) := by
  decide +kernel

private theorem code_encoding_303 :
    code 303 = ∑ p : Fin 12, (rowForward 303 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_303 : code 303 < code 304 := by
  decide +kernel

private theorem row_image_304 (p : Fin 12) :
    (rows 304).val p = rowForward 304 p := by
  calc
    (rows 304).val p = rowPoint 304 p := (rowPoint_eq 304 p).symm
    _ = rowForward 304 p := by fin_cases p <;> decide +kernel

private theorem transition_check_304 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 304) (generatorPermutation s p) =
      generatorPermutation s (rowForward 304 p) := by
  decide +kernel

private theorem code_encoding_304 :
    code 304 = ∑ p : Fin 12, (rowForward 304 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_304 : code 304 < code 305 := by
  decide +kernel

private theorem row_image_305 (p : Fin 12) :
    (rows 305).val p = rowForward 305 p := by
  calc
    (rows 305).val p = rowPoint 305 p := (rowPoint_eq 305 p).symm
    _ = rowForward 305 p := by fin_cases p <;> decide +kernel

private theorem transition_check_305 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 305) (generatorPermutation s p) =
      generatorPermutation s (rowForward 305 p) := by
  decide +kernel

private theorem code_encoding_305 :
    code 305 = ∑ p : Fin 12, (rowForward 305 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_305 : code 305 < code 306 := by
  decide +kernel

private theorem row_image_306 (p : Fin 12) :
    (rows 306).val p = rowForward 306 p := by
  calc
    (rows 306).val p = rowPoint 306 p := (rowPoint_eq 306 p).symm
    _ = rowForward 306 p := by fin_cases p <;> decide +kernel

private theorem transition_check_306 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 306) (generatorPermutation s p) =
      generatorPermutation s (rowForward 306 p) := by
  decide +kernel

private theorem code_encoding_306 :
    code 306 = ∑ p : Fin 12, (rowForward 306 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_306 : code 306 < code 307 := by
  decide +kernel

private theorem row_image_307 (p : Fin 12) :
    (rows 307).val p = rowForward 307 p := by
  calc
    (rows 307).val p = rowPoint 307 p := (rowPoint_eq 307 p).symm
    _ = rowForward 307 p := by fin_cases p <;> decide +kernel

private theorem transition_check_307 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 307) (generatorPermutation s p) =
      generatorPermutation s (rowForward 307 p) := by
  decide +kernel

private theorem code_encoding_307 :
    code 307 = ∑ p : Fin 12, (rowForward 307 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_307 : code 307 < code 308 := by
  decide +kernel

private theorem row_image_308 (p : Fin 12) :
    (rows 308).val p = rowForward 308 p := by
  calc
    (rows 308).val p = rowPoint 308 p := (rowPoint_eq 308 p).symm
    _ = rowForward 308 p := by fin_cases p <;> decide +kernel

private theorem transition_check_308 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 308) (generatorPermutation s p) =
      generatorPermutation s (rowForward 308 p) := by
  decide +kernel

private theorem code_encoding_308 :
    code 308 = ∑ p : Fin 12, (rowForward 308 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_308 : code 308 < code 309 := by
  decide +kernel

private theorem row_image_309 (p : Fin 12) :
    (rows 309).val p = rowForward 309 p := by
  calc
    (rows 309).val p = rowPoint 309 p := (rowPoint_eq 309 p).symm
    _ = rowForward 309 p := by fin_cases p <;> decide +kernel

private theorem transition_check_309 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 309) (generatorPermutation s p) =
      generatorPermutation s (rowForward 309 p) := by
  decide +kernel

private theorem code_encoding_309 :
    code 309 = ∑ p : Fin 12, (rowForward 309 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_309 : code 309 < code 310 := by
  decide +kernel

private theorem row_image_310 (p : Fin 12) :
    (rows 310).val p = rowForward 310 p := by
  calc
    (rows 310).val p = rowPoint 310 p := (rowPoint_eq 310 p).symm
    _ = rowForward 310 p := by fin_cases p <;> decide +kernel

private theorem transition_check_310 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 310) (generatorPermutation s p) =
      generatorPermutation s (rowForward 310 p) := by
  decide +kernel

private theorem code_encoding_310 :
    code 310 = ∑ p : Fin 12, (rowForward 310 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_310 : code 310 < code 311 := by
  decide +kernel

private theorem row_image_311 (p : Fin 12) :
    (rows 311).val p = rowForward 311 p := by
  calc
    (rows 311).val p = rowPoint 311 p := (rowPoint_eq 311 p).symm
    _ = rowForward 311 p := by fin_cases p <;> decide +kernel

private theorem transition_check_311 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 311) (generatorPermutation s p) =
      generatorPermutation s (rowForward 311 p) := by
  decide +kernel

private theorem code_encoding_311 :
    code 311 = ∑ p : Fin 12, (rowForward 311 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_311 : code 311 < code 312 := by
  decide +kernel

private theorem row_image_312 (p : Fin 12) :
    (rows 312).val p = rowForward 312 p := by
  calc
    (rows 312).val p = rowPoint 312 p := (rowPoint_eq 312 p).symm
    _ = rowForward 312 p := by fin_cases p <;> decide +kernel

private theorem transition_check_312 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 312) (generatorPermutation s p) =
      generatorPermutation s (rowForward 312 p) := by
  decide +kernel

private theorem code_encoding_312 :
    code 312 = ∑ p : Fin 12, (rowForward 312 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_312 : code 312 < code 313 := by
  decide +kernel

private theorem row_image_313 (p : Fin 12) :
    (rows 313).val p = rowForward 313 p := by
  calc
    (rows 313).val p = rowPoint 313 p := (rowPoint_eq 313 p).symm
    _ = rowForward 313 p := by fin_cases p <;> decide +kernel

private theorem transition_check_313 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 313) (generatorPermutation s p) =
      generatorPermutation s (rowForward 313 p) := by
  decide +kernel

private theorem code_encoding_313 :
    code 313 = ∑ p : Fin 12, (rowForward 313 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_313 : code 313 < code 314 := by
  decide +kernel

private theorem row_image_314 (p : Fin 12) :
    (rows 314).val p = rowForward 314 p := by
  calc
    (rows 314).val p = rowPoint 314 p := (rowPoint_eq 314 p).symm
    _ = rowForward 314 p := by fin_cases p <;> decide +kernel

private theorem transition_check_314 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 314) (generatorPermutation s p) =
      generatorPermutation s (rowForward 314 p) := by
  decide +kernel

private theorem code_encoding_314 :
    code 314 = ∑ p : Fin 12, (rowForward 314 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_314 : code 314 < code 315 := by
  decide +kernel

private theorem row_image_315 (p : Fin 12) :
    (rows 315).val p = rowForward 315 p := by
  calc
    (rows 315).val p = rowPoint 315 p := (rowPoint_eq 315 p).symm
    _ = rowForward 315 p := by fin_cases p <;> decide +kernel

private theorem transition_check_315 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 315) (generatorPermutation s p) =
      generatorPermutation s (rowForward 315 p) := by
  decide +kernel

private theorem code_encoding_315 :
    code 315 = ∑ p : Fin 12, (rowForward 315 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_315 : code 315 < code 316 := by
  decide +kernel

private theorem row_image_316 (p : Fin 12) :
    (rows 316).val p = rowForward 316 p := by
  calc
    (rows 316).val p = rowPoint 316 p := (rowPoint_eq 316 p).symm
    _ = rowForward 316 p := by fin_cases p <;> decide +kernel

private theorem transition_check_316 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 316) (generatorPermutation s p) =
      generatorPermutation s (rowForward 316 p) := by
  decide +kernel

private theorem code_encoding_316 :
    code 316 = ∑ p : Fin 12, (rowForward 316 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_316 : code 316 < code 317 := by
  decide +kernel

private theorem row_image_317 (p : Fin 12) :
    (rows 317).val p = rowForward 317 p := by
  calc
    (rows 317).val p = rowPoint 317 p := (rowPoint_eq 317 p).symm
    _ = rowForward 317 p := by fin_cases p <;> decide +kernel

private theorem transition_check_317 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 317) (generatorPermutation s p) =
      generatorPermutation s (rowForward 317 p) := by
  decide +kernel

private theorem code_encoding_317 :
    code 317 = ∑ p : Fin 12, (rowForward 317 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_317 : code 317 < code 318 := by
  decide +kernel

private theorem row_image_318 (p : Fin 12) :
    (rows 318).val p = rowForward 318 p := by
  calc
    (rows 318).val p = rowPoint 318 p := (rowPoint_eq 318 p).symm
    _ = rowForward 318 p := by fin_cases p <;> decide +kernel

private theorem transition_check_318 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 318) (generatorPermutation s p) =
      generatorPermutation s (rowForward 318 p) := by
  decide +kernel

private theorem code_encoding_318 :
    code 318 = ∑ p : Fin 12, (rowForward 318 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_318 : code 318 < code 319 := by
  decide +kernel

private theorem row_image_319 (p : Fin 12) :
    (rows 319).val p = rowForward 319 p := by
  calc
    (rows 319).val p = rowPoint 319 p := (rowPoint_eq 319 p).symm
    _ = rowForward 319 p := by fin_cases p <;> decide +kernel

private theorem transition_check_319 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 319) (generatorPermutation s p) =
      generatorPermutation s (rowForward 319 p) := by
  decide +kernel

private theorem code_encoding_319 :
    code 319 = ∑ p : Fin 12, (rowForward 319 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_319 : code 319 < code 320 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (288 : Fin 495) from rfl))
      (row_image_288 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (289 : Fin 495) from rfl))
      (row_image_289 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (290 : Fin 495) from rfl))
      (row_image_290 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (291 : Fin 495) from rfl))
      (row_image_291 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (292 : Fin 495) from rfl))
      (row_image_292 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (293 : Fin 495) from rfl))
      (row_image_293 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (294 : Fin 495) from rfl))
      (row_image_294 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (295 : Fin 495) from rfl))
      (row_image_295 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (296 : Fin 495) from rfl))
      (row_image_296 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (297 : Fin 495) from rfl))
      (row_image_297 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (298 : Fin 495) from rfl))
      (row_image_298 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (299 : Fin 495) from rfl))
      (row_image_299 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (300 : Fin 495) from rfl))
      (row_image_300 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (301 : Fin 495) from rfl))
      (row_image_301 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (302 : Fin 495) from rfl))
      (row_image_302 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (303 : Fin 495) from rfl))
      (row_image_303 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (304 : Fin 495) from rfl))
      (row_image_304 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (305 : Fin 495) from rfl))
      (row_image_305 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (306 : Fin 495) from rfl))
      (row_image_306 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (307 : Fin 495) from rfl))
      (row_image_307 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (308 : Fin 495) from rfl))
      (row_image_308 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (309 : Fin 495) from rfl))
      (row_image_309 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (310 : Fin 495) from rfl))
      (row_image_310 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (311 : Fin 495) from rfl))
      (row_image_311 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (312 : Fin 495) from rfl))
      (row_image_312 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (313 : Fin 495) from rfl))
      (row_image_313 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (314 : Fin 495) from rfl))
      (row_image_314 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (315 : Fin 495) from rfl))
      (row_image_315 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (316 : Fin 495) from rfl))
      (row_image_316 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (317 : Fin 495) from rfl))
      (row_image_317 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (318 : Fin 495) from rfl))
      (row_image_318 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (319 : Fin 495) from rfl))
      (row_image_319 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (288 : Fin 495) from rfl))
      (transition_check_288 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (289 : Fin 495) from rfl))
      (transition_check_289 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (290 : Fin 495) from rfl))
      (transition_check_290 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (291 : Fin 495) from rfl))
      (transition_check_291 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (292 : Fin 495) from rfl))
      (transition_check_292 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (293 : Fin 495) from rfl))
      (transition_check_293 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (294 : Fin 495) from rfl))
      (transition_check_294 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (295 : Fin 495) from rfl))
      (transition_check_295 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (296 : Fin 495) from rfl))
      (transition_check_296 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (297 : Fin 495) from rfl))
      (transition_check_297 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (298 : Fin 495) from rfl))
      (transition_check_298 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (299 : Fin 495) from rfl))
      (transition_check_299 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (300 : Fin 495) from rfl))
      (transition_check_300 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (301 : Fin 495) from rfl))
      (transition_check_301 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (302 : Fin 495) from rfl))
      (transition_check_302 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (303 : Fin 495) from rfl))
      (transition_check_303 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (304 : Fin 495) from rfl))
      (transition_check_304 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (305 : Fin 495) from rfl))
      (transition_check_305 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (306 : Fin 495) from rfl))
      (transition_check_306 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (307 : Fin 495) from rfl))
      (transition_check_307 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (308 : Fin 495) from rfl))
      (transition_check_308 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (309 : Fin 495) from rfl))
      (transition_check_309 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (310 : Fin 495) from rfl))
      (transition_check_310 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (311 : Fin 495) from rfl))
      (transition_check_311 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (312 : Fin 495) from rfl))
      (transition_check_312 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (313 : Fin 495) from rfl))
      (transition_check_313 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (314 : Fin 495) from rfl))
      (transition_check_314 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (315 : Fin 495) from rfl))
      (transition_check_315 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (316 : Fin 495) from rfl))
      (transition_check_316 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (317 : Fin 495) from rfl))
      (transition_check_317 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (318 : Fin 495) from rfl))
      (transition_check_318 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (319 : Fin 495) from rfl))
      (transition_check_319 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (288 : Fin 495) from rfl))
      code_encoding_288
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (289 : Fin 495) from rfl))
      code_encoding_289
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (290 : Fin 495) from rfl))
      code_encoding_290
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (291 : Fin 495) from rfl))
      code_encoding_291
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (292 : Fin 495) from rfl))
      code_encoding_292
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (293 : Fin 495) from rfl))
      code_encoding_293
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (294 : Fin 495) from rfl))
      code_encoding_294
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (295 : Fin 495) from rfl))
      code_encoding_295
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (296 : Fin 495) from rfl))
      code_encoding_296
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (297 : Fin 495) from rfl))
      code_encoding_297
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (298 : Fin 495) from rfl))
      code_encoding_298
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (299 : Fin 495) from rfl))
      code_encoding_299
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (300 : Fin 495) from rfl))
      code_encoding_300
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (301 : Fin 495) from rfl))
      code_encoding_301
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (302 : Fin 495) from rfl))
      code_encoding_302
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (303 : Fin 495) from rfl))
      code_encoding_303
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (304 : Fin 495) from rfl))
      code_encoding_304
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (305 : Fin 495) from rfl))
      code_encoding_305
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (306 : Fin 495) from rfl))
      code_encoding_306
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (307 : Fin 495) from rfl))
      code_encoding_307
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (308 : Fin 495) from rfl))
      code_encoding_308
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (309 : Fin 495) from rfl))
      code_encoding_309
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (310 : Fin 495) from rfl))
      code_encoding_310
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (311 : Fin 495) from rfl))
      code_encoding_311
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (312 : Fin 495) from rfl))
      code_encoding_312
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (313 : Fin 495) from rfl))
      code_encoding_313
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (314 : Fin 495) from rfl))
      code_encoding_314
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (315 : Fin 495) from rfl))
      code_encoding_315
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (316 : Fin 495) from rfl))
      code_encoding_316
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (317 : Fin 495) from rfl))
      code_encoding_317
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (318 : Fin 495) from rfl))
      code_encoding_318
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (319 : Fin 495) from rfl))
      code_encoding_319

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (288 : Fin 495) from rfl))
    intro h
    exact code_adjacent_288
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (289 : Fin 495) from rfl))
    intro h
    exact code_adjacent_289
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (290 : Fin 495) from rfl))
    intro h
    exact code_adjacent_290
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (291 : Fin 495) from rfl))
    intro h
    exact code_adjacent_291
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (292 : Fin 495) from rfl))
    intro h
    exact code_adjacent_292
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (293 : Fin 495) from rfl))
    intro h
    exact code_adjacent_293
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (294 : Fin 495) from rfl))
    intro h
    exact code_adjacent_294
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (295 : Fin 495) from rfl))
    intro h
    exact code_adjacent_295
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (296 : Fin 495) from rfl))
    intro h
    exact code_adjacent_296
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (297 : Fin 495) from rfl))
    intro h
    exact code_adjacent_297
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (298 : Fin 495) from rfl))
    intro h
    exact code_adjacent_298
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (299 : Fin 495) from rfl))
    intro h
    exact code_adjacent_299
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (300 : Fin 495) from rfl))
    intro h
    exact code_adjacent_300
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (301 : Fin 495) from rfl))
    intro h
    exact code_adjacent_301
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (302 : Fin 495) from rfl))
    intro h
    exact code_adjacent_302
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (303 : Fin 495) from rfl))
    intro h
    exact code_adjacent_303
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (304 : Fin 495) from rfl))
    intro h
    exact code_adjacent_304
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (305 : Fin 495) from rfl))
    intro h
    exact code_adjacent_305
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (306 : Fin 495) from rfl))
    intro h
    exact code_adjacent_306
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (307 : Fin 495) from rfl))
    intro h
    exact code_adjacent_307
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (308 : Fin 495) from rfl))
    intro h
    exact code_adjacent_308
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (309 : Fin 495) from rfl))
    intro h
    exact code_adjacent_309
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (310 : Fin 495) from rfl))
    intro h
    exact code_adjacent_310
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (311 : Fin 495) from rfl))
    intro h
    exact code_adjacent_311
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (312 : Fin 495) from rfl))
    intro h
    exact code_adjacent_312
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (313 : Fin 495) from rfl))
    intro h
    exact code_adjacent_313
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (314 : Fin 495) from rfl))
    intro h
    exact code_adjacent_314
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (315 : Fin 495) from rfl))
    intro h
    exact code_adjacent_315
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (316 : Fin 495) from rfl))
    intro h
    exact code_adjacent_316
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (317 : Fin 495) from rfl))
    intro h
    exact code_adjacent_317
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (318 : Fin 495) from rfl))
    intro h
    exact code_adjacent_318
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (319 : Fin 495) from rfl))
    intro h
    exact code_adjacent_319

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock09
