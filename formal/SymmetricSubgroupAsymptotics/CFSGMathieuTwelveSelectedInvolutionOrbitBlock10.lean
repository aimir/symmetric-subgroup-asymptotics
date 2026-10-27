import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows320..351.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock10
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨320+i.val,by omega⟩

private theorem row_image_320 (p : Fin 12) :
    (rows 320).val p = rowForward 320 p := by
  calc
    (rows 320).val p = rowPoint 320 p := (rowPoint_eq 320 p).symm
    _ = rowForward 320 p := by fin_cases p <;> decide +kernel

private theorem transition_check_320 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 320) (generatorPermutation s p) =
      generatorPermutation s (rowForward 320 p) := by
  decide +kernel

private theorem code_encoding_320 :
    code 320 = ∑ p : Fin 12, (rowForward 320 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_320 : code 320 < code 321 := by
  decide +kernel

private theorem row_image_321 (p : Fin 12) :
    (rows 321).val p = rowForward 321 p := by
  calc
    (rows 321).val p = rowPoint 321 p := (rowPoint_eq 321 p).symm
    _ = rowForward 321 p := by fin_cases p <;> decide +kernel

private theorem transition_check_321 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 321) (generatorPermutation s p) =
      generatorPermutation s (rowForward 321 p) := by
  decide +kernel

private theorem code_encoding_321 :
    code 321 = ∑ p : Fin 12, (rowForward 321 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_321 : code 321 < code 322 := by
  decide +kernel

private theorem row_image_322 (p : Fin 12) :
    (rows 322).val p = rowForward 322 p := by
  calc
    (rows 322).val p = rowPoint 322 p := (rowPoint_eq 322 p).symm
    _ = rowForward 322 p := by fin_cases p <;> decide +kernel

private theorem transition_check_322 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 322) (generatorPermutation s p) =
      generatorPermutation s (rowForward 322 p) := by
  decide +kernel

private theorem code_encoding_322 :
    code 322 = ∑ p : Fin 12, (rowForward 322 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_322 : code 322 < code 323 := by
  decide +kernel

private theorem row_image_323 (p : Fin 12) :
    (rows 323).val p = rowForward 323 p := by
  calc
    (rows 323).val p = rowPoint 323 p := (rowPoint_eq 323 p).symm
    _ = rowForward 323 p := by fin_cases p <;> decide +kernel

private theorem transition_check_323 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 323) (generatorPermutation s p) =
      generatorPermutation s (rowForward 323 p) := by
  decide +kernel

private theorem code_encoding_323 :
    code 323 = ∑ p : Fin 12, (rowForward 323 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_323 : code 323 < code 324 := by
  decide +kernel

private theorem row_image_324 (p : Fin 12) :
    (rows 324).val p = rowForward 324 p := by
  calc
    (rows 324).val p = rowPoint 324 p := (rowPoint_eq 324 p).symm
    _ = rowForward 324 p := by fin_cases p <;> decide +kernel

private theorem transition_check_324 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 324) (generatorPermutation s p) =
      generatorPermutation s (rowForward 324 p) := by
  decide +kernel

private theorem code_encoding_324 :
    code 324 = ∑ p : Fin 12, (rowForward 324 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_324 : code 324 < code 325 := by
  decide +kernel

private theorem row_image_325 (p : Fin 12) :
    (rows 325).val p = rowForward 325 p := by
  calc
    (rows 325).val p = rowPoint 325 p := (rowPoint_eq 325 p).symm
    _ = rowForward 325 p := by fin_cases p <;> decide +kernel

private theorem transition_check_325 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 325) (generatorPermutation s p) =
      generatorPermutation s (rowForward 325 p) := by
  decide +kernel

private theorem code_encoding_325 :
    code 325 = ∑ p : Fin 12, (rowForward 325 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_325 : code 325 < code 326 := by
  decide +kernel

private theorem row_image_326 (p : Fin 12) :
    (rows 326).val p = rowForward 326 p := by
  calc
    (rows 326).val p = rowPoint 326 p := (rowPoint_eq 326 p).symm
    _ = rowForward 326 p := by fin_cases p <;> decide +kernel

private theorem transition_check_326 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 326) (generatorPermutation s p) =
      generatorPermutation s (rowForward 326 p) := by
  decide +kernel

private theorem code_encoding_326 :
    code 326 = ∑ p : Fin 12, (rowForward 326 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_326 : code 326 < code 327 := by
  decide +kernel

private theorem row_image_327 (p : Fin 12) :
    (rows 327).val p = rowForward 327 p := by
  calc
    (rows 327).val p = rowPoint 327 p := (rowPoint_eq 327 p).symm
    _ = rowForward 327 p := by fin_cases p <;> decide +kernel

private theorem transition_check_327 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 327) (generatorPermutation s p) =
      generatorPermutation s (rowForward 327 p) := by
  decide +kernel

private theorem code_encoding_327 :
    code 327 = ∑ p : Fin 12, (rowForward 327 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_327 : code 327 < code 328 := by
  decide +kernel

private theorem row_image_328 (p : Fin 12) :
    (rows 328).val p = rowForward 328 p := by
  calc
    (rows 328).val p = rowPoint 328 p := (rowPoint_eq 328 p).symm
    _ = rowForward 328 p := by fin_cases p <;> decide +kernel

private theorem transition_check_328 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 328) (generatorPermutation s p) =
      generatorPermutation s (rowForward 328 p) := by
  decide +kernel

private theorem code_encoding_328 :
    code 328 = ∑ p : Fin 12, (rowForward 328 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_328 : code 328 < code 329 := by
  decide +kernel

private theorem row_image_329 (p : Fin 12) :
    (rows 329).val p = rowForward 329 p := by
  calc
    (rows 329).val p = rowPoint 329 p := (rowPoint_eq 329 p).symm
    _ = rowForward 329 p := by fin_cases p <;> decide +kernel

private theorem transition_check_329 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 329) (generatorPermutation s p) =
      generatorPermutation s (rowForward 329 p) := by
  decide +kernel

private theorem code_encoding_329 :
    code 329 = ∑ p : Fin 12, (rowForward 329 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_329 : code 329 < code 330 := by
  decide +kernel

private theorem row_image_330 (p : Fin 12) :
    (rows 330).val p = rowForward 330 p := by
  calc
    (rows 330).val p = rowPoint 330 p := (rowPoint_eq 330 p).symm
    _ = rowForward 330 p := by fin_cases p <;> decide +kernel

private theorem transition_check_330 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 330) (generatorPermutation s p) =
      generatorPermutation s (rowForward 330 p) := by
  decide +kernel

private theorem code_encoding_330 :
    code 330 = ∑ p : Fin 12, (rowForward 330 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_330 : code 330 < code 331 := by
  decide +kernel

private theorem row_image_331 (p : Fin 12) :
    (rows 331).val p = rowForward 331 p := by
  calc
    (rows 331).val p = rowPoint 331 p := (rowPoint_eq 331 p).symm
    _ = rowForward 331 p := by fin_cases p <;> decide +kernel

private theorem transition_check_331 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 331) (generatorPermutation s p) =
      generatorPermutation s (rowForward 331 p) := by
  decide +kernel

private theorem code_encoding_331 :
    code 331 = ∑ p : Fin 12, (rowForward 331 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_331 : code 331 < code 332 := by
  decide +kernel

private theorem row_image_332 (p : Fin 12) :
    (rows 332).val p = rowForward 332 p := by
  calc
    (rows 332).val p = rowPoint 332 p := (rowPoint_eq 332 p).symm
    _ = rowForward 332 p := by fin_cases p <;> decide +kernel

private theorem transition_check_332 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 332) (generatorPermutation s p) =
      generatorPermutation s (rowForward 332 p) := by
  decide +kernel

private theorem code_encoding_332 :
    code 332 = ∑ p : Fin 12, (rowForward 332 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_332 : code 332 < code 333 := by
  decide +kernel

private theorem row_image_333 (p : Fin 12) :
    (rows 333).val p = rowForward 333 p := by
  calc
    (rows 333).val p = rowPoint 333 p := (rowPoint_eq 333 p).symm
    _ = rowForward 333 p := by fin_cases p <;> decide +kernel

private theorem transition_check_333 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 333) (generatorPermutation s p) =
      generatorPermutation s (rowForward 333 p) := by
  decide +kernel

private theorem code_encoding_333 :
    code 333 = ∑ p : Fin 12, (rowForward 333 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_333 : code 333 < code 334 := by
  decide +kernel

private theorem row_image_334 (p : Fin 12) :
    (rows 334).val p = rowForward 334 p := by
  calc
    (rows 334).val p = rowPoint 334 p := (rowPoint_eq 334 p).symm
    _ = rowForward 334 p := by fin_cases p <;> decide +kernel

private theorem transition_check_334 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 334) (generatorPermutation s p) =
      generatorPermutation s (rowForward 334 p) := by
  decide +kernel

private theorem code_encoding_334 :
    code 334 = ∑ p : Fin 12, (rowForward 334 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_334 : code 334 < code 335 := by
  decide +kernel

private theorem row_image_335 (p : Fin 12) :
    (rows 335).val p = rowForward 335 p := by
  calc
    (rows 335).val p = rowPoint 335 p := (rowPoint_eq 335 p).symm
    _ = rowForward 335 p := by fin_cases p <;> decide +kernel

private theorem transition_check_335 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 335) (generatorPermutation s p) =
      generatorPermutation s (rowForward 335 p) := by
  decide +kernel

private theorem code_encoding_335 :
    code 335 = ∑ p : Fin 12, (rowForward 335 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_335 : code 335 < code 336 := by
  decide +kernel

private theorem row_image_336 (p : Fin 12) :
    (rows 336).val p = rowForward 336 p := by
  calc
    (rows 336).val p = rowPoint 336 p := (rowPoint_eq 336 p).symm
    _ = rowForward 336 p := by fin_cases p <;> decide +kernel

private theorem transition_check_336 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 336) (generatorPermutation s p) =
      generatorPermutation s (rowForward 336 p) := by
  decide +kernel

private theorem code_encoding_336 :
    code 336 = ∑ p : Fin 12, (rowForward 336 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_336 : code 336 < code 337 := by
  decide +kernel

private theorem row_image_337 (p : Fin 12) :
    (rows 337).val p = rowForward 337 p := by
  calc
    (rows 337).val p = rowPoint 337 p := (rowPoint_eq 337 p).symm
    _ = rowForward 337 p := by fin_cases p <;> decide +kernel

private theorem transition_check_337 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 337) (generatorPermutation s p) =
      generatorPermutation s (rowForward 337 p) := by
  decide +kernel

private theorem code_encoding_337 :
    code 337 = ∑ p : Fin 12, (rowForward 337 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_337 : code 337 < code 338 := by
  decide +kernel

private theorem row_image_338 (p : Fin 12) :
    (rows 338).val p = rowForward 338 p := by
  calc
    (rows 338).val p = rowPoint 338 p := (rowPoint_eq 338 p).symm
    _ = rowForward 338 p := by fin_cases p <;> decide +kernel

private theorem transition_check_338 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 338) (generatorPermutation s p) =
      generatorPermutation s (rowForward 338 p) := by
  decide +kernel

private theorem code_encoding_338 :
    code 338 = ∑ p : Fin 12, (rowForward 338 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_338 : code 338 < code 339 := by
  decide +kernel

private theorem row_image_339 (p : Fin 12) :
    (rows 339).val p = rowForward 339 p := by
  calc
    (rows 339).val p = rowPoint 339 p := (rowPoint_eq 339 p).symm
    _ = rowForward 339 p := by fin_cases p <;> decide +kernel

private theorem transition_check_339 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 339) (generatorPermutation s p) =
      generatorPermutation s (rowForward 339 p) := by
  decide +kernel

private theorem code_encoding_339 :
    code 339 = ∑ p : Fin 12, (rowForward 339 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_339 : code 339 < code 340 := by
  decide +kernel

private theorem row_image_340 (p : Fin 12) :
    (rows 340).val p = rowForward 340 p := by
  calc
    (rows 340).val p = rowPoint 340 p := (rowPoint_eq 340 p).symm
    _ = rowForward 340 p := by fin_cases p <;> decide +kernel

private theorem transition_check_340 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 340) (generatorPermutation s p) =
      generatorPermutation s (rowForward 340 p) := by
  decide +kernel

private theorem code_encoding_340 :
    code 340 = ∑ p : Fin 12, (rowForward 340 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_340 : code 340 < code 341 := by
  decide +kernel

private theorem row_image_341 (p : Fin 12) :
    (rows 341).val p = rowForward 341 p := by
  calc
    (rows 341).val p = rowPoint 341 p := (rowPoint_eq 341 p).symm
    _ = rowForward 341 p := by fin_cases p <;> decide +kernel

private theorem transition_check_341 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 341) (generatorPermutation s p) =
      generatorPermutation s (rowForward 341 p) := by
  decide +kernel

private theorem code_encoding_341 :
    code 341 = ∑ p : Fin 12, (rowForward 341 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_341 : code 341 < code 342 := by
  decide +kernel

private theorem row_image_342 (p : Fin 12) :
    (rows 342).val p = rowForward 342 p := by
  calc
    (rows 342).val p = rowPoint 342 p := (rowPoint_eq 342 p).symm
    _ = rowForward 342 p := by fin_cases p <;> decide +kernel

private theorem transition_check_342 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 342) (generatorPermutation s p) =
      generatorPermutation s (rowForward 342 p) := by
  decide +kernel

private theorem code_encoding_342 :
    code 342 = ∑ p : Fin 12, (rowForward 342 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_342 : code 342 < code 343 := by
  decide +kernel

private theorem row_image_343 (p : Fin 12) :
    (rows 343).val p = rowForward 343 p := by
  calc
    (rows 343).val p = rowPoint 343 p := (rowPoint_eq 343 p).symm
    _ = rowForward 343 p := by fin_cases p <;> decide +kernel

private theorem transition_check_343 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 343) (generatorPermutation s p) =
      generatorPermutation s (rowForward 343 p) := by
  decide +kernel

private theorem code_encoding_343 :
    code 343 = ∑ p : Fin 12, (rowForward 343 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_343 : code 343 < code 344 := by
  decide +kernel

private theorem row_image_344 (p : Fin 12) :
    (rows 344).val p = rowForward 344 p := by
  calc
    (rows 344).val p = rowPoint 344 p := (rowPoint_eq 344 p).symm
    _ = rowForward 344 p := by fin_cases p <;> decide +kernel

private theorem transition_check_344 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 344) (generatorPermutation s p) =
      generatorPermutation s (rowForward 344 p) := by
  decide +kernel

private theorem code_encoding_344 :
    code 344 = ∑ p : Fin 12, (rowForward 344 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_344 : code 344 < code 345 := by
  decide +kernel

private theorem row_image_345 (p : Fin 12) :
    (rows 345).val p = rowForward 345 p := by
  calc
    (rows 345).val p = rowPoint 345 p := (rowPoint_eq 345 p).symm
    _ = rowForward 345 p := by fin_cases p <;> decide +kernel

private theorem transition_check_345 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 345) (generatorPermutation s p) =
      generatorPermutation s (rowForward 345 p) := by
  decide +kernel

private theorem code_encoding_345 :
    code 345 = ∑ p : Fin 12, (rowForward 345 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_345 : code 345 < code 346 := by
  decide +kernel

private theorem row_image_346 (p : Fin 12) :
    (rows 346).val p = rowForward 346 p := by
  calc
    (rows 346).val p = rowPoint 346 p := (rowPoint_eq 346 p).symm
    _ = rowForward 346 p := by fin_cases p <;> decide +kernel

private theorem transition_check_346 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 346) (generatorPermutation s p) =
      generatorPermutation s (rowForward 346 p) := by
  decide +kernel

private theorem code_encoding_346 :
    code 346 = ∑ p : Fin 12, (rowForward 346 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_346 : code 346 < code 347 := by
  decide +kernel

private theorem row_image_347 (p : Fin 12) :
    (rows 347).val p = rowForward 347 p := by
  calc
    (rows 347).val p = rowPoint 347 p := (rowPoint_eq 347 p).symm
    _ = rowForward 347 p := by fin_cases p <;> decide +kernel

private theorem transition_check_347 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 347) (generatorPermutation s p) =
      generatorPermutation s (rowForward 347 p) := by
  decide +kernel

private theorem code_encoding_347 :
    code 347 = ∑ p : Fin 12, (rowForward 347 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_347 : code 347 < code 348 := by
  decide +kernel

private theorem row_image_348 (p : Fin 12) :
    (rows 348).val p = rowForward 348 p := by
  calc
    (rows 348).val p = rowPoint 348 p := (rowPoint_eq 348 p).symm
    _ = rowForward 348 p := by fin_cases p <;> decide +kernel

private theorem transition_check_348 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 348) (generatorPermutation s p) =
      generatorPermutation s (rowForward 348 p) := by
  decide +kernel

private theorem code_encoding_348 :
    code 348 = ∑ p : Fin 12, (rowForward 348 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_348 : code 348 < code 349 := by
  decide +kernel

private theorem row_image_349 (p : Fin 12) :
    (rows 349).val p = rowForward 349 p := by
  calc
    (rows 349).val p = rowPoint 349 p := (rowPoint_eq 349 p).symm
    _ = rowForward 349 p := by fin_cases p <;> decide +kernel

private theorem transition_check_349 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 349) (generatorPermutation s p) =
      generatorPermutation s (rowForward 349 p) := by
  decide +kernel

private theorem code_encoding_349 :
    code 349 = ∑ p : Fin 12, (rowForward 349 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_349 : code 349 < code 350 := by
  decide +kernel

private theorem row_image_350 (p : Fin 12) :
    (rows 350).val p = rowForward 350 p := by
  calc
    (rows 350).val p = rowPoint 350 p := (rowPoint_eq 350 p).symm
    _ = rowForward 350 p := by fin_cases p <;> decide +kernel

private theorem transition_check_350 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 350) (generatorPermutation s p) =
      generatorPermutation s (rowForward 350 p) := by
  decide +kernel

private theorem code_encoding_350 :
    code 350 = ∑ p : Fin 12, (rowForward 350 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_350 : code 350 < code 351 := by
  decide +kernel

private theorem row_image_351 (p : Fin 12) :
    (rows 351).val p = rowForward 351 p := by
  calc
    (rows 351).val p = rowPoint 351 p := (rowPoint_eq 351 p).symm
    _ = rowForward 351 p := by fin_cases p <;> decide +kernel

private theorem transition_check_351 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 351) (generatorPermutation s p) =
      generatorPermutation s (rowForward 351 p) := by
  decide +kernel

private theorem code_encoding_351 :
    code 351 = ∑ p : Fin 12, (rowForward 351 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_351 : code 351 < code 352 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (320 : Fin 495) from rfl))
      (row_image_320 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (321 : Fin 495) from rfl))
      (row_image_321 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (322 : Fin 495) from rfl))
      (row_image_322 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (323 : Fin 495) from rfl))
      (row_image_323 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (324 : Fin 495) from rfl))
      (row_image_324 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (325 : Fin 495) from rfl))
      (row_image_325 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (326 : Fin 495) from rfl))
      (row_image_326 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (327 : Fin 495) from rfl))
      (row_image_327 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (328 : Fin 495) from rfl))
      (row_image_328 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (329 : Fin 495) from rfl))
      (row_image_329 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (330 : Fin 495) from rfl))
      (row_image_330 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (331 : Fin 495) from rfl))
      (row_image_331 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (332 : Fin 495) from rfl))
      (row_image_332 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (333 : Fin 495) from rfl))
      (row_image_333 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (334 : Fin 495) from rfl))
      (row_image_334 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (335 : Fin 495) from rfl))
      (row_image_335 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (336 : Fin 495) from rfl))
      (row_image_336 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (337 : Fin 495) from rfl))
      (row_image_337 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (338 : Fin 495) from rfl))
      (row_image_338 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (339 : Fin 495) from rfl))
      (row_image_339 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (340 : Fin 495) from rfl))
      (row_image_340 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (341 : Fin 495) from rfl))
      (row_image_341 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (342 : Fin 495) from rfl))
      (row_image_342 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (343 : Fin 495) from rfl))
      (row_image_343 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (344 : Fin 495) from rfl))
      (row_image_344 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (345 : Fin 495) from rfl))
      (row_image_345 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (346 : Fin 495) from rfl))
      (row_image_346 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (347 : Fin 495) from rfl))
      (row_image_347 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (348 : Fin 495) from rfl))
      (row_image_348 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (349 : Fin 495) from rfl))
      (row_image_349 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (350 : Fin 495) from rfl))
      (row_image_350 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (351 : Fin 495) from rfl))
      (row_image_351 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (320 : Fin 495) from rfl))
      (transition_check_320 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (321 : Fin 495) from rfl))
      (transition_check_321 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (322 : Fin 495) from rfl))
      (transition_check_322 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (323 : Fin 495) from rfl))
      (transition_check_323 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (324 : Fin 495) from rfl))
      (transition_check_324 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (325 : Fin 495) from rfl))
      (transition_check_325 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (326 : Fin 495) from rfl))
      (transition_check_326 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (327 : Fin 495) from rfl))
      (transition_check_327 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (328 : Fin 495) from rfl))
      (transition_check_328 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (329 : Fin 495) from rfl))
      (transition_check_329 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (330 : Fin 495) from rfl))
      (transition_check_330 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (331 : Fin 495) from rfl))
      (transition_check_331 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (332 : Fin 495) from rfl))
      (transition_check_332 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (333 : Fin 495) from rfl))
      (transition_check_333 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (334 : Fin 495) from rfl))
      (transition_check_334 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (335 : Fin 495) from rfl))
      (transition_check_335 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (336 : Fin 495) from rfl))
      (transition_check_336 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (337 : Fin 495) from rfl))
      (transition_check_337 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (338 : Fin 495) from rfl))
      (transition_check_338 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (339 : Fin 495) from rfl))
      (transition_check_339 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (340 : Fin 495) from rfl))
      (transition_check_340 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (341 : Fin 495) from rfl))
      (transition_check_341 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (342 : Fin 495) from rfl))
      (transition_check_342 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (343 : Fin 495) from rfl))
      (transition_check_343 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (344 : Fin 495) from rfl))
      (transition_check_344 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (345 : Fin 495) from rfl))
      (transition_check_345 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (346 : Fin 495) from rfl))
      (transition_check_346 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (347 : Fin 495) from rfl))
      (transition_check_347 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (348 : Fin 495) from rfl))
      (transition_check_348 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (349 : Fin 495) from rfl))
      (transition_check_349 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (350 : Fin 495) from rfl))
      (transition_check_350 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (351 : Fin 495) from rfl))
      (transition_check_351 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (320 : Fin 495) from rfl))
      code_encoding_320
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (321 : Fin 495) from rfl))
      code_encoding_321
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (322 : Fin 495) from rfl))
      code_encoding_322
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (323 : Fin 495) from rfl))
      code_encoding_323
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (324 : Fin 495) from rfl))
      code_encoding_324
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (325 : Fin 495) from rfl))
      code_encoding_325
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (326 : Fin 495) from rfl))
      code_encoding_326
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (327 : Fin 495) from rfl))
      code_encoding_327
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (328 : Fin 495) from rfl))
      code_encoding_328
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (329 : Fin 495) from rfl))
      code_encoding_329
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (330 : Fin 495) from rfl))
      code_encoding_330
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (331 : Fin 495) from rfl))
      code_encoding_331
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (332 : Fin 495) from rfl))
      code_encoding_332
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (333 : Fin 495) from rfl))
      code_encoding_333
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (334 : Fin 495) from rfl))
      code_encoding_334
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (335 : Fin 495) from rfl))
      code_encoding_335
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (336 : Fin 495) from rfl))
      code_encoding_336
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (337 : Fin 495) from rfl))
      code_encoding_337
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (338 : Fin 495) from rfl))
      code_encoding_338
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (339 : Fin 495) from rfl))
      code_encoding_339
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (340 : Fin 495) from rfl))
      code_encoding_340
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (341 : Fin 495) from rfl))
      code_encoding_341
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (342 : Fin 495) from rfl))
      code_encoding_342
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (343 : Fin 495) from rfl))
      code_encoding_343
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (344 : Fin 495) from rfl))
      code_encoding_344
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (345 : Fin 495) from rfl))
      code_encoding_345
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (346 : Fin 495) from rfl))
      code_encoding_346
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (347 : Fin 495) from rfl))
      code_encoding_347
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (348 : Fin 495) from rfl))
      code_encoding_348
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (349 : Fin 495) from rfl))
      code_encoding_349
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (350 : Fin 495) from rfl))
      code_encoding_350
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (351 : Fin 495) from rfl))
      code_encoding_351

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (320 : Fin 495) from rfl))
    intro h
    exact code_adjacent_320
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (321 : Fin 495) from rfl))
    intro h
    exact code_adjacent_321
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (322 : Fin 495) from rfl))
    intro h
    exact code_adjacent_322
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (323 : Fin 495) from rfl))
    intro h
    exact code_adjacent_323
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (324 : Fin 495) from rfl))
    intro h
    exact code_adjacent_324
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (325 : Fin 495) from rfl))
    intro h
    exact code_adjacent_325
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (326 : Fin 495) from rfl))
    intro h
    exact code_adjacent_326
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (327 : Fin 495) from rfl))
    intro h
    exact code_adjacent_327
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (328 : Fin 495) from rfl))
    intro h
    exact code_adjacent_328
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (329 : Fin 495) from rfl))
    intro h
    exact code_adjacent_329
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (330 : Fin 495) from rfl))
    intro h
    exact code_adjacent_330
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (331 : Fin 495) from rfl))
    intro h
    exact code_adjacent_331
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (332 : Fin 495) from rfl))
    intro h
    exact code_adjacent_332
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (333 : Fin 495) from rfl))
    intro h
    exact code_adjacent_333
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (334 : Fin 495) from rfl))
    intro h
    exact code_adjacent_334
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (335 : Fin 495) from rfl))
    intro h
    exact code_adjacent_335
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (336 : Fin 495) from rfl))
    intro h
    exact code_adjacent_336
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (337 : Fin 495) from rfl))
    intro h
    exact code_adjacent_337
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (338 : Fin 495) from rfl))
    intro h
    exact code_adjacent_338
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (339 : Fin 495) from rfl))
    intro h
    exact code_adjacent_339
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (340 : Fin 495) from rfl))
    intro h
    exact code_adjacent_340
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (341 : Fin 495) from rfl))
    intro h
    exact code_adjacent_341
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (342 : Fin 495) from rfl))
    intro h
    exact code_adjacent_342
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (343 : Fin 495) from rfl))
    intro h
    exact code_adjacent_343
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (344 : Fin 495) from rfl))
    intro h
    exact code_adjacent_344
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (345 : Fin 495) from rfl))
    intro h
    exact code_adjacent_345
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (346 : Fin 495) from rfl))
    intro h
    exact code_adjacent_346
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (347 : Fin 495) from rfl))
    intro h
    exact code_adjacent_347
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (348 : Fin 495) from rfl))
    intro h
    exact code_adjacent_348
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (349 : Fin 495) from rfl))
    intro h
    exact code_adjacent_349
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (350 : Fin 495) from rfl))
    intro h
    exact code_adjacent_350
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (351 : Fin 495) from rfl))
    intro h
    exact code_adjacent_351

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock10
