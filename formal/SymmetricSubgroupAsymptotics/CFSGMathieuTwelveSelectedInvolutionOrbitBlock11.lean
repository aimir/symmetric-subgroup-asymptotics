import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows352..383.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock11
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨352+i.val,by omega⟩

private theorem row_image_352 (p : Fin 12) :
    (rows 352).val p = rowForward 352 p := by
  calc
    (rows 352).val p = rowPoint 352 p := (rowPoint_eq 352 p).symm
    _ = rowForward 352 p := by fin_cases p <;> decide +kernel

private theorem transition_check_352 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 352) (generatorPermutation s p) =
      generatorPermutation s (rowForward 352 p) := by
  decide +kernel

private theorem code_encoding_352 :
    code 352 = ∑ p : Fin 12, (rowForward 352 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_352 : code 352 < code 353 := by
  decide +kernel

private theorem row_image_353 (p : Fin 12) :
    (rows 353).val p = rowForward 353 p := by
  calc
    (rows 353).val p = rowPoint 353 p := (rowPoint_eq 353 p).symm
    _ = rowForward 353 p := by fin_cases p <;> decide +kernel

private theorem transition_check_353 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 353) (generatorPermutation s p) =
      generatorPermutation s (rowForward 353 p) := by
  decide +kernel

private theorem code_encoding_353 :
    code 353 = ∑ p : Fin 12, (rowForward 353 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_353 : code 353 < code 354 := by
  decide +kernel

private theorem row_image_354 (p : Fin 12) :
    (rows 354).val p = rowForward 354 p := by
  calc
    (rows 354).val p = rowPoint 354 p := (rowPoint_eq 354 p).symm
    _ = rowForward 354 p := by fin_cases p <;> decide +kernel

private theorem transition_check_354 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 354) (generatorPermutation s p) =
      generatorPermutation s (rowForward 354 p) := by
  decide +kernel

private theorem code_encoding_354 :
    code 354 = ∑ p : Fin 12, (rowForward 354 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_354 : code 354 < code 355 := by
  decide +kernel

private theorem row_image_355 (p : Fin 12) :
    (rows 355).val p = rowForward 355 p := by
  calc
    (rows 355).val p = rowPoint 355 p := (rowPoint_eq 355 p).symm
    _ = rowForward 355 p := by fin_cases p <;> decide +kernel

private theorem transition_check_355 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 355) (generatorPermutation s p) =
      generatorPermutation s (rowForward 355 p) := by
  decide +kernel

private theorem code_encoding_355 :
    code 355 = ∑ p : Fin 12, (rowForward 355 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_355 : code 355 < code 356 := by
  decide +kernel

private theorem row_image_356 (p : Fin 12) :
    (rows 356).val p = rowForward 356 p := by
  calc
    (rows 356).val p = rowPoint 356 p := (rowPoint_eq 356 p).symm
    _ = rowForward 356 p := by fin_cases p <;> decide +kernel

private theorem transition_check_356 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 356) (generatorPermutation s p) =
      generatorPermutation s (rowForward 356 p) := by
  decide +kernel

private theorem code_encoding_356 :
    code 356 = ∑ p : Fin 12, (rowForward 356 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_356 : code 356 < code 357 := by
  decide +kernel

private theorem row_image_357 (p : Fin 12) :
    (rows 357).val p = rowForward 357 p := by
  calc
    (rows 357).val p = rowPoint 357 p := (rowPoint_eq 357 p).symm
    _ = rowForward 357 p := by fin_cases p <;> decide +kernel

private theorem transition_check_357 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 357) (generatorPermutation s p) =
      generatorPermutation s (rowForward 357 p) := by
  decide +kernel

private theorem code_encoding_357 :
    code 357 = ∑ p : Fin 12, (rowForward 357 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_357 : code 357 < code 358 := by
  decide +kernel

private theorem row_image_358 (p : Fin 12) :
    (rows 358).val p = rowForward 358 p := by
  calc
    (rows 358).val p = rowPoint 358 p := (rowPoint_eq 358 p).symm
    _ = rowForward 358 p := by fin_cases p <;> decide +kernel

private theorem transition_check_358 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 358) (generatorPermutation s p) =
      generatorPermutation s (rowForward 358 p) := by
  decide +kernel

private theorem code_encoding_358 :
    code 358 = ∑ p : Fin 12, (rowForward 358 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_358 : code 358 < code 359 := by
  decide +kernel

private theorem row_image_359 (p : Fin 12) :
    (rows 359).val p = rowForward 359 p := by
  calc
    (rows 359).val p = rowPoint 359 p := (rowPoint_eq 359 p).symm
    _ = rowForward 359 p := by fin_cases p <;> decide +kernel

private theorem transition_check_359 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 359) (generatorPermutation s p) =
      generatorPermutation s (rowForward 359 p) := by
  decide +kernel

private theorem code_encoding_359 :
    code 359 = ∑ p : Fin 12, (rowForward 359 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_359 : code 359 < code 360 := by
  decide +kernel

private theorem row_image_360 (p : Fin 12) :
    (rows 360).val p = rowForward 360 p := by
  calc
    (rows 360).val p = rowPoint 360 p := (rowPoint_eq 360 p).symm
    _ = rowForward 360 p := by fin_cases p <;> decide +kernel

private theorem transition_check_360 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 360) (generatorPermutation s p) =
      generatorPermutation s (rowForward 360 p) := by
  decide +kernel

private theorem code_encoding_360 :
    code 360 = ∑ p : Fin 12, (rowForward 360 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_360 : code 360 < code 361 := by
  decide +kernel

private theorem row_image_361 (p : Fin 12) :
    (rows 361).val p = rowForward 361 p := by
  calc
    (rows 361).val p = rowPoint 361 p := (rowPoint_eq 361 p).symm
    _ = rowForward 361 p := by fin_cases p <;> decide +kernel

private theorem transition_check_361 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 361) (generatorPermutation s p) =
      generatorPermutation s (rowForward 361 p) := by
  decide +kernel

private theorem code_encoding_361 :
    code 361 = ∑ p : Fin 12, (rowForward 361 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_361 : code 361 < code 362 := by
  decide +kernel

private theorem row_image_362 (p : Fin 12) :
    (rows 362).val p = rowForward 362 p := by
  calc
    (rows 362).val p = rowPoint 362 p := (rowPoint_eq 362 p).symm
    _ = rowForward 362 p := by fin_cases p <;> decide +kernel

private theorem transition_check_362 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 362) (generatorPermutation s p) =
      generatorPermutation s (rowForward 362 p) := by
  decide +kernel

private theorem code_encoding_362 :
    code 362 = ∑ p : Fin 12, (rowForward 362 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_362 : code 362 < code 363 := by
  decide +kernel

private theorem row_image_363 (p : Fin 12) :
    (rows 363).val p = rowForward 363 p := by
  calc
    (rows 363).val p = rowPoint 363 p := (rowPoint_eq 363 p).symm
    _ = rowForward 363 p := by fin_cases p <;> decide +kernel

private theorem transition_check_363 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 363) (generatorPermutation s p) =
      generatorPermutation s (rowForward 363 p) := by
  decide +kernel

private theorem code_encoding_363 :
    code 363 = ∑ p : Fin 12, (rowForward 363 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_363 : code 363 < code 364 := by
  decide +kernel

private theorem row_image_364 (p : Fin 12) :
    (rows 364).val p = rowForward 364 p := by
  calc
    (rows 364).val p = rowPoint 364 p := (rowPoint_eq 364 p).symm
    _ = rowForward 364 p := by fin_cases p <;> decide +kernel

private theorem transition_check_364 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 364) (generatorPermutation s p) =
      generatorPermutation s (rowForward 364 p) := by
  decide +kernel

private theorem code_encoding_364 :
    code 364 = ∑ p : Fin 12, (rowForward 364 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_364 : code 364 < code 365 := by
  decide +kernel

private theorem row_image_365 (p : Fin 12) :
    (rows 365).val p = rowForward 365 p := by
  calc
    (rows 365).val p = rowPoint 365 p := (rowPoint_eq 365 p).symm
    _ = rowForward 365 p := by fin_cases p <;> decide +kernel

private theorem transition_check_365 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 365) (generatorPermutation s p) =
      generatorPermutation s (rowForward 365 p) := by
  decide +kernel

private theorem code_encoding_365 :
    code 365 = ∑ p : Fin 12, (rowForward 365 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_365 : code 365 < code 366 := by
  decide +kernel

private theorem row_image_366 (p : Fin 12) :
    (rows 366).val p = rowForward 366 p := by
  calc
    (rows 366).val p = rowPoint 366 p := (rowPoint_eq 366 p).symm
    _ = rowForward 366 p := by fin_cases p <;> decide +kernel

private theorem transition_check_366 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 366) (generatorPermutation s p) =
      generatorPermutation s (rowForward 366 p) := by
  decide +kernel

private theorem code_encoding_366 :
    code 366 = ∑ p : Fin 12, (rowForward 366 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_366 : code 366 < code 367 := by
  decide +kernel

private theorem row_image_367 (p : Fin 12) :
    (rows 367).val p = rowForward 367 p := by
  calc
    (rows 367).val p = rowPoint 367 p := (rowPoint_eq 367 p).symm
    _ = rowForward 367 p := by fin_cases p <;> decide +kernel

private theorem transition_check_367 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 367) (generatorPermutation s p) =
      generatorPermutation s (rowForward 367 p) := by
  decide +kernel

private theorem code_encoding_367 :
    code 367 = ∑ p : Fin 12, (rowForward 367 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_367 : code 367 < code 368 := by
  decide +kernel

private theorem row_image_368 (p : Fin 12) :
    (rows 368).val p = rowForward 368 p := by
  calc
    (rows 368).val p = rowPoint 368 p := (rowPoint_eq 368 p).symm
    _ = rowForward 368 p := by fin_cases p <;> decide +kernel

private theorem transition_check_368 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 368) (generatorPermutation s p) =
      generatorPermutation s (rowForward 368 p) := by
  decide +kernel

private theorem code_encoding_368 :
    code 368 = ∑ p : Fin 12, (rowForward 368 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_368 : code 368 < code 369 := by
  decide +kernel

private theorem row_image_369 (p : Fin 12) :
    (rows 369).val p = rowForward 369 p := by
  calc
    (rows 369).val p = rowPoint 369 p := (rowPoint_eq 369 p).symm
    _ = rowForward 369 p := by fin_cases p <;> decide +kernel

private theorem transition_check_369 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 369) (generatorPermutation s p) =
      generatorPermutation s (rowForward 369 p) := by
  decide +kernel

private theorem code_encoding_369 :
    code 369 = ∑ p : Fin 12, (rowForward 369 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_369 : code 369 < code 370 := by
  decide +kernel

private theorem row_image_370 (p : Fin 12) :
    (rows 370).val p = rowForward 370 p := by
  calc
    (rows 370).val p = rowPoint 370 p := (rowPoint_eq 370 p).symm
    _ = rowForward 370 p := by fin_cases p <;> decide +kernel

private theorem transition_check_370 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 370) (generatorPermutation s p) =
      generatorPermutation s (rowForward 370 p) := by
  decide +kernel

private theorem code_encoding_370 :
    code 370 = ∑ p : Fin 12, (rowForward 370 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_370 : code 370 < code 371 := by
  decide +kernel

private theorem row_image_371 (p : Fin 12) :
    (rows 371).val p = rowForward 371 p := by
  calc
    (rows 371).val p = rowPoint 371 p := (rowPoint_eq 371 p).symm
    _ = rowForward 371 p := by fin_cases p <;> decide +kernel

private theorem transition_check_371 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 371) (generatorPermutation s p) =
      generatorPermutation s (rowForward 371 p) := by
  decide +kernel

private theorem code_encoding_371 :
    code 371 = ∑ p : Fin 12, (rowForward 371 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_371 : code 371 < code 372 := by
  decide +kernel

private theorem row_image_372 (p : Fin 12) :
    (rows 372).val p = rowForward 372 p := by
  calc
    (rows 372).val p = rowPoint 372 p := (rowPoint_eq 372 p).symm
    _ = rowForward 372 p := by fin_cases p <;> decide +kernel

private theorem transition_check_372 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 372) (generatorPermutation s p) =
      generatorPermutation s (rowForward 372 p) := by
  decide +kernel

private theorem code_encoding_372 :
    code 372 = ∑ p : Fin 12, (rowForward 372 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_372 : code 372 < code 373 := by
  decide +kernel

private theorem row_image_373 (p : Fin 12) :
    (rows 373).val p = rowForward 373 p := by
  calc
    (rows 373).val p = rowPoint 373 p := (rowPoint_eq 373 p).symm
    _ = rowForward 373 p := by fin_cases p <;> decide +kernel

private theorem transition_check_373 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 373) (generatorPermutation s p) =
      generatorPermutation s (rowForward 373 p) := by
  decide +kernel

private theorem code_encoding_373 :
    code 373 = ∑ p : Fin 12, (rowForward 373 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_373 : code 373 < code 374 := by
  decide +kernel

private theorem row_image_374 (p : Fin 12) :
    (rows 374).val p = rowForward 374 p := by
  calc
    (rows 374).val p = rowPoint 374 p := (rowPoint_eq 374 p).symm
    _ = rowForward 374 p := by fin_cases p <;> decide +kernel

private theorem transition_check_374 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 374) (generatorPermutation s p) =
      generatorPermutation s (rowForward 374 p) := by
  decide +kernel

private theorem code_encoding_374 :
    code 374 = ∑ p : Fin 12, (rowForward 374 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_374 : code 374 < code 375 := by
  decide +kernel

private theorem row_image_375 (p : Fin 12) :
    (rows 375).val p = rowForward 375 p := by
  calc
    (rows 375).val p = rowPoint 375 p := (rowPoint_eq 375 p).symm
    _ = rowForward 375 p := by fin_cases p <;> decide +kernel

private theorem transition_check_375 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 375) (generatorPermutation s p) =
      generatorPermutation s (rowForward 375 p) := by
  decide +kernel

private theorem code_encoding_375 :
    code 375 = ∑ p : Fin 12, (rowForward 375 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_375 : code 375 < code 376 := by
  decide +kernel

private theorem row_image_376 (p : Fin 12) :
    (rows 376).val p = rowForward 376 p := by
  calc
    (rows 376).val p = rowPoint 376 p := (rowPoint_eq 376 p).symm
    _ = rowForward 376 p := by fin_cases p <;> decide +kernel

private theorem transition_check_376 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 376) (generatorPermutation s p) =
      generatorPermutation s (rowForward 376 p) := by
  decide +kernel

private theorem code_encoding_376 :
    code 376 = ∑ p : Fin 12, (rowForward 376 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_376 : code 376 < code 377 := by
  decide +kernel

private theorem row_image_377 (p : Fin 12) :
    (rows 377).val p = rowForward 377 p := by
  calc
    (rows 377).val p = rowPoint 377 p := (rowPoint_eq 377 p).symm
    _ = rowForward 377 p := by fin_cases p <;> decide +kernel

private theorem transition_check_377 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 377) (generatorPermutation s p) =
      generatorPermutation s (rowForward 377 p) := by
  decide +kernel

private theorem code_encoding_377 :
    code 377 = ∑ p : Fin 12, (rowForward 377 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_377 : code 377 < code 378 := by
  decide +kernel

private theorem row_image_378 (p : Fin 12) :
    (rows 378).val p = rowForward 378 p := by
  calc
    (rows 378).val p = rowPoint 378 p := (rowPoint_eq 378 p).symm
    _ = rowForward 378 p := by fin_cases p <;> decide +kernel

private theorem transition_check_378 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 378) (generatorPermutation s p) =
      generatorPermutation s (rowForward 378 p) := by
  decide +kernel

private theorem code_encoding_378 :
    code 378 = ∑ p : Fin 12, (rowForward 378 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_378 : code 378 < code 379 := by
  decide +kernel

private theorem row_image_379 (p : Fin 12) :
    (rows 379).val p = rowForward 379 p := by
  calc
    (rows 379).val p = rowPoint 379 p := (rowPoint_eq 379 p).symm
    _ = rowForward 379 p := by fin_cases p <;> decide +kernel

private theorem transition_check_379 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 379) (generatorPermutation s p) =
      generatorPermutation s (rowForward 379 p) := by
  decide +kernel

private theorem code_encoding_379 :
    code 379 = ∑ p : Fin 12, (rowForward 379 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_379 : code 379 < code 380 := by
  decide +kernel

private theorem row_image_380 (p : Fin 12) :
    (rows 380).val p = rowForward 380 p := by
  calc
    (rows 380).val p = rowPoint 380 p := (rowPoint_eq 380 p).symm
    _ = rowForward 380 p := by fin_cases p <;> decide +kernel

private theorem transition_check_380 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 380) (generatorPermutation s p) =
      generatorPermutation s (rowForward 380 p) := by
  decide +kernel

private theorem code_encoding_380 :
    code 380 = ∑ p : Fin 12, (rowForward 380 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_380 : code 380 < code 381 := by
  decide +kernel

private theorem row_image_381 (p : Fin 12) :
    (rows 381).val p = rowForward 381 p := by
  calc
    (rows 381).val p = rowPoint 381 p := (rowPoint_eq 381 p).symm
    _ = rowForward 381 p := by fin_cases p <;> decide +kernel

private theorem transition_check_381 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 381) (generatorPermutation s p) =
      generatorPermutation s (rowForward 381 p) := by
  decide +kernel

private theorem code_encoding_381 :
    code 381 = ∑ p : Fin 12, (rowForward 381 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_381 : code 381 < code 382 := by
  decide +kernel

private theorem row_image_382 (p : Fin 12) :
    (rows 382).val p = rowForward 382 p := by
  calc
    (rows 382).val p = rowPoint 382 p := (rowPoint_eq 382 p).symm
    _ = rowForward 382 p := by fin_cases p <;> decide +kernel

private theorem transition_check_382 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 382) (generatorPermutation s p) =
      generatorPermutation s (rowForward 382 p) := by
  decide +kernel

private theorem code_encoding_382 :
    code 382 = ∑ p : Fin 12, (rowForward 382 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_382 : code 382 < code 383 := by
  decide +kernel

private theorem row_image_383 (p : Fin 12) :
    (rows 383).val p = rowForward 383 p := by
  calc
    (rows 383).val p = rowPoint 383 p := (rowPoint_eq 383 p).symm
    _ = rowForward 383 p := by fin_cases p <;> decide +kernel

private theorem transition_check_383 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 383) (generatorPermutation s p) =
      generatorPermutation s (rowForward 383 p) := by
  decide +kernel

private theorem code_encoding_383 :
    code 383 = ∑ p : Fin 12, (rowForward 383 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_383 : code 383 < code 384 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (352 : Fin 495) from rfl))
      (row_image_352 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (353 : Fin 495) from rfl))
      (row_image_353 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (354 : Fin 495) from rfl))
      (row_image_354 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (355 : Fin 495) from rfl))
      (row_image_355 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (356 : Fin 495) from rfl))
      (row_image_356 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (357 : Fin 495) from rfl))
      (row_image_357 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (358 : Fin 495) from rfl))
      (row_image_358 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (359 : Fin 495) from rfl))
      (row_image_359 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (360 : Fin 495) from rfl))
      (row_image_360 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (361 : Fin 495) from rfl))
      (row_image_361 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (362 : Fin 495) from rfl))
      (row_image_362 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (363 : Fin 495) from rfl))
      (row_image_363 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (364 : Fin 495) from rfl))
      (row_image_364 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (365 : Fin 495) from rfl))
      (row_image_365 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (366 : Fin 495) from rfl))
      (row_image_366 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (367 : Fin 495) from rfl))
      (row_image_367 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (368 : Fin 495) from rfl))
      (row_image_368 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (369 : Fin 495) from rfl))
      (row_image_369 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (370 : Fin 495) from rfl))
      (row_image_370 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (371 : Fin 495) from rfl))
      (row_image_371 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (372 : Fin 495) from rfl))
      (row_image_372 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (373 : Fin 495) from rfl))
      (row_image_373 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (374 : Fin 495) from rfl))
      (row_image_374 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (375 : Fin 495) from rfl))
      (row_image_375 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (376 : Fin 495) from rfl))
      (row_image_376 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (377 : Fin 495) from rfl))
      (row_image_377 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (378 : Fin 495) from rfl))
      (row_image_378 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (379 : Fin 495) from rfl))
      (row_image_379 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (380 : Fin 495) from rfl))
      (row_image_380 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (381 : Fin 495) from rfl))
      (row_image_381 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (382 : Fin 495) from rfl))
      (row_image_382 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (383 : Fin 495) from rfl))
      (row_image_383 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (352 : Fin 495) from rfl))
      (transition_check_352 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (353 : Fin 495) from rfl))
      (transition_check_353 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (354 : Fin 495) from rfl))
      (transition_check_354 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (355 : Fin 495) from rfl))
      (transition_check_355 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (356 : Fin 495) from rfl))
      (transition_check_356 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (357 : Fin 495) from rfl))
      (transition_check_357 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (358 : Fin 495) from rfl))
      (transition_check_358 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (359 : Fin 495) from rfl))
      (transition_check_359 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (360 : Fin 495) from rfl))
      (transition_check_360 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (361 : Fin 495) from rfl))
      (transition_check_361 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (362 : Fin 495) from rfl))
      (transition_check_362 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (363 : Fin 495) from rfl))
      (transition_check_363 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (364 : Fin 495) from rfl))
      (transition_check_364 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (365 : Fin 495) from rfl))
      (transition_check_365 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (366 : Fin 495) from rfl))
      (transition_check_366 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (367 : Fin 495) from rfl))
      (transition_check_367 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (368 : Fin 495) from rfl))
      (transition_check_368 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (369 : Fin 495) from rfl))
      (transition_check_369 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (370 : Fin 495) from rfl))
      (transition_check_370 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (371 : Fin 495) from rfl))
      (transition_check_371 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (372 : Fin 495) from rfl))
      (transition_check_372 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (373 : Fin 495) from rfl))
      (transition_check_373 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (374 : Fin 495) from rfl))
      (transition_check_374 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (375 : Fin 495) from rfl))
      (transition_check_375 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (376 : Fin 495) from rfl))
      (transition_check_376 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (377 : Fin 495) from rfl))
      (transition_check_377 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (378 : Fin 495) from rfl))
      (transition_check_378 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (379 : Fin 495) from rfl))
      (transition_check_379 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (380 : Fin 495) from rfl))
      (transition_check_380 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (381 : Fin 495) from rfl))
      (transition_check_381 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (382 : Fin 495) from rfl))
      (transition_check_382 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (383 : Fin 495) from rfl))
      (transition_check_383 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (352 : Fin 495) from rfl))
      code_encoding_352
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (353 : Fin 495) from rfl))
      code_encoding_353
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (354 : Fin 495) from rfl))
      code_encoding_354
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (355 : Fin 495) from rfl))
      code_encoding_355
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (356 : Fin 495) from rfl))
      code_encoding_356
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (357 : Fin 495) from rfl))
      code_encoding_357
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (358 : Fin 495) from rfl))
      code_encoding_358
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (359 : Fin 495) from rfl))
      code_encoding_359
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (360 : Fin 495) from rfl))
      code_encoding_360
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (361 : Fin 495) from rfl))
      code_encoding_361
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (362 : Fin 495) from rfl))
      code_encoding_362
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (363 : Fin 495) from rfl))
      code_encoding_363
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (364 : Fin 495) from rfl))
      code_encoding_364
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (365 : Fin 495) from rfl))
      code_encoding_365
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (366 : Fin 495) from rfl))
      code_encoding_366
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (367 : Fin 495) from rfl))
      code_encoding_367
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (368 : Fin 495) from rfl))
      code_encoding_368
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (369 : Fin 495) from rfl))
      code_encoding_369
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (370 : Fin 495) from rfl))
      code_encoding_370
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (371 : Fin 495) from rfl))
      code_encoding_371
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (372 : Fin 495) from rfl))
      code_encoding_372
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (373 : Fin 495) from rfl))
      code_encoding_373
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (374 : Fin 495) from rfl))
      code_encoding_374
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (375 : Fin 495) from rfl))
      code_encoding_375
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (376 : Fin 495) from rfl))
      code_encoding_376
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (377 : Fin 495) from rfl))
      code_encoding_377
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (378 : Fin 495) from rfl))
      code_encoding_378
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (379 : Fin 495) from rfl))
      code_encoding_379
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (380 : Fin 495) from rfl))
      code_encoding_380
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (381 : Fin 495) from rfl))
      code_encoding_381
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (382 : Fin 495) from rfl))
      code_encoding_382
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (383 : Fin 495) from rfl))
      code_encoding_383

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (352 : Fin 495) from rfl))
    intro h
    exact code_adjacent_352
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (353 : Fin 495) from rfl))
    intro h
    exact code_adjacent_353
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (354 : Fin 495) from rfl))
    intro h
    exact code_adjacent_354
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (355 : Fin 495) from rfl))
    intro h
    exact code_adjacent_355
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (356 : Fin 495) from rfl))
    intro h
    exact code_adjacent_356
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (357 : Fin 495) from rfl))
    intro h
    exact code_adjacent_357
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (358 : Fin 495) from rfl))
    intro h
    exact code_adjacent_358
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (359 : Fin 495) from rfl))
    intro h
    exact code_adjacent_359
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (360 : Fin 495) from rfl))
    intro h
    exact code_adjacent_360
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (361 : Fin 495) from rfl))
    intro h
    exact code_adjacent_361
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (362 : Fin 495) from rfl))
    intro h
    exact code_adjacent_362
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (363 : Fin 495) from rfl))
    intro h
    exact code_adjacent_363
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (364 : Fin 495) from rfl))
    intro h
    exact code_adjacent_364
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (365 : Fin 495) from rfl))
    intro h
    exact code_adjacent_365
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (366 : Fin 495) from rfl))
    intro h
    exact code_adjacent_366
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (367 : Fin 495) from rfl))
    intro h
    exact code_adjacent_367
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (368 : Fin 495) from rfl))
    intro h
    exact code_adjacent_368
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (369 : Fin 495) from rfl))
    intro h
    exact code_adjacent_369
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (370 : Fin 495) from rfl))
    intro h
    exact code_adjacent_370
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (371 : Fin 495) from rfl))
    intro h
    exact code_adjacent_371
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (372 : Fin 495) from rfl))
    intro h
    exact code_adjacent_372
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (373 : Fin 495) from rfl))
    intro h
    exact code_adjacent_373
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (374 : Fin 495) from rfl))
    intro h
    exact code_adjacent_374
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (375 : Fin 495) from rfl))
    intro h
    exact code_adjacent_375
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (376 : Fin 495) from rfl))
    intro h
    exact code_adjacent_376
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (377 : Fin 495) from rfl))
    intro h
    exact code_adjacent_377
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (378 : Fin 495) from rfl))
    intro h
    exact code_adjacent_378
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (379 : Fin 495) from rfl))
    intro h
    exact code_adjacent_379
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (380 : Fin 495) from rfl))
    intro h
    exact code_adjacent_380
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (381 : Fin 495) from rfl))
    intro h
    exact code_adjacent_381
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (382 : Fin 495) from rfl))
    intro h
    exact code_adjacent_382
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (383 : Fin 495) from rfl))
    intro h
    exact code_adjacent_383

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock11
