import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows384..415.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock12
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨384+i.val,by omega⟩

private theorem row_image_384 (p : Fin 12) :
    (rows 384).val p = rowForward 384 p := by
  calc
    (rows 384).val p = rowPoint 384 p := (rowPoint_eq 384 p).symm
    _ = rowForward 384 p := by fin_cases p <;> decide +kernel

private theorem transition_check_384 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 384) (generatorPermutation s p) =
      generatorPermutation s (rowForward 384 p) := by
  decide +kernel

private theorem code_encoding_384 :
    code 384 = ∑ p : Fin 12, (rowForward 384 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_384 : code 384 < code 385 := by
  decide +kernel

private theorem row_image_385 (p : Fin 12) :
    (rows 385).val p = rowForward 385 p := by
  calc
    (rows 385).val p = rowPoint 385 p := (rowPoint_eq 385 p).symm
    _ = rowForward 385 p := by fin_cases p <;> decide +kernel

private theorem transition_check_385 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 385) (generatorPermutation s p) =
      generatorPermutation s (rowForward 385 p) := by
  decide +kernel

private theorem code_encoding_385 :
    code 385 = ∑ p : Fin 12, (rowForward 385 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_385 : code 385 < code 386 := by
  decide +kernel

private theorem row_image_386 (p : Fin 12) :
    (rows 386).val p = rowForward 386 p := by
  calc
    (rows 386).val p = rowPoint 386 p := (rowPoint_eq 386 p).symm
    _ = rowForward 386 p := by fin_cases p <;> decide +kernel

private theorem transition_check_386 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 386) (generatorPermutation s p) =
      generatorPermutation s (rowForward 386 p) := by
  decide +kernel

private theorem code_encoding_386 :
    code 386 = ∑ p : Fin 12, (rowForward 386 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_386 : code 386 < code 387 := by
  decide +kernel

private theorem row_image_387 (p : Fin 12) :
    (rows 387).val p = rowForward 387 p := by
  calc
    (rows 387).val p = rowPoint 387 p := (rowPoint_eq 387 p).symm
    _ = rowForward 387 p := by fin_cases p <;> decide +kernel

private theorem transition_check_387 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 387) (generatorPermutation s p) =
      generatorPermutation s (rowForward 387 p) := by
  decide +kernel

private theorem code_encoding_387 :
    code 387 = ∑ p : Fin 12, (rowForward 387 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_387 : code 387 < code 388 := by
  decide +kernel

private theorem row_image_388 (p : Fin 12) :
    (rows 388).val p = rowForward 388 p := by
  calc
    (rows 388).val p = rowPoint 388 p := (rowPoint_eq 388 p).symm
    _ = rowForward 388 p := by fin_cases p <;> decide +kernel

private theorem transition_check_388 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 388) (generatorPermutation s p) =
      generatorPermutation s (rowForward 388 p) := by
  decide +kernel

private theorem code_encoding_388 :
    code 388 = ∑ p : Fin 12, (rowForward 388 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_388 : code 388 < code 389 := by
  decide +kernel

private theorem row_image_389 (p : Fin 12) :
    (rows 389).val p = rowForward 389 p := by
  calc
    (rows 389).val p = rowPoint 389 p := (rowPoint_eq 389 p).symm
    _ = rowForward 389 p := by fin_cases p <;> decide +kernel

private theorem transition_check_389 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 389) (generatorPermutation s p) =
      generatorPermutation s (rowForward 389 p) := by
  decide +kernel

private theorem code_encoding_389 :
    code 389 = ∑ p : Fin 12, (rowForward 389 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_389 : code 389 < code 390 := by
  decide +kernel

private theorem row_image_390 (p : Fin 12) :
    (rows 390).val p = rowForward 390 p := by
  calc
    (rows 390).val p = rowPoint 390 p := (rowPoint_eq 390 p).symm
    _ = rowForward 390 p := by fin_cases p <;> decide +kernel

private theorem transition_check_390 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 390) (generatorPermutation s p) =
      generatorPermutation s (rowForward 390 p) := by
  decide +kernel

private theorem code_encoding_390 :
    code 390 = ∑ p : Fin 12, (rowForward 390 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_390 : code 390 < code 391 := by
  decide +kernel

private theorem row_image_391 (p : Fin 12) :
    (rows 391).val p = rowForward 391 p := by
  calc
    (rows 391).val p = rowPoint 391 p := (rowPoint_eq 391 p).symm
    _ = rowForward 391 p := by fin_cases p <;> decide +kernel

private theorem transition_check_391 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 391) (generatorPermutation s p) =
      generatorPermutation s (rowForward 391 p) := by
  decide +kernel

private theorem code_encoding_391 :
    code 391 = ∑ p : Fin 12, (rowForward 391 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_391 : code 391 < code 392 := by
  decide +kernel

private theorem row_image_392 (p : Fin 12) :
    (rows 392).val p = rowForward 392 p := by
  calc
    (rows 392).val p = rowPoint 392 p := (rowPoint_eq 392 p).symm
    _ = rowForward 392 p := by fin_cases p <;> decide +kernel

private theorem transition_check_392 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 392) (generatorPermutation s p) =
      generatorPermutation s (rowForward 392 p) := by
  decide +kernel

private theorem code_encoding_392 :
    code 392 = ∑ p : Fin 12, (rowForward 392 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_392 : code 392 < code 393 := by
  decide +kernel

private theorem row_image_393 (p : Fin 12) :
    (rows 393).val p = rowForward 393 p := by
  calc
    (rows 393).val p = rowPoint 393 p := (rowPoint_eq 393 p).symm
    _ = rowForward 393 p := by fin_cases p <;> decide +kernel

private theorem transition_check_393 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 393) (generatorPermutation s p) =
      generatorPermutation s (rowForward 393 p) := by
  decide +kernel

private theorem code_encoding_393 :
    code 393 = ∑ p : Fin 12, (rowForward 393 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_393 : code 393 < code 394 := by
  decide +kernel

private theorem row_image_394 (p : Fin 12) :
    (rows 394).val p = rowForward 394 p := by
  calc
    (rows 394).val p = rowPoint 394 p := (rowPoint_eq 394 p).symm
    _ = rowForward 394 p := by fin_cases p <;> decide +kernel

private theorem transition_check_394 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 394) (generatorPermutation s p) =
      generatorPermutation s (rowForward 394 p) := by
  decide +kernel

private theorem code_encoding_394 :
    code 394 = ∑ p : Fin 12, (rowForward 394 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_394 : code 394 < code 395 := by
  decide +kernel

private theorem row_image_395 (p : Fin 12) :
    (rows 395).val p = rowForward 395 p := by
  calc
    (rows 395).val p = rowPoint 395 p := (rowPoint_eq 395 p).symm
    _ = rowForward 395 p := by fin_cases p <;> decide +kernel

private theorem transition_check_395 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 395) (generatorPermutation s p) =
      generatorPermutation s (rowForward 395 p) := by
  decide +kernel

private theorem code_encoding_395 :
    code 395 = ∑ p : Fin 12, (rowForward 395 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_395 : code 395 < code 396 := by
  decide +kernel

private theorem row_image_396 (p : Fin 12) :
    (rows 396).val p = rowForward 396 p := by
  calc
    (rows 396).val p = rowPoint 396 p := (rowPoint_eq 396 p).symm
    _ = rowForward 396 p := by fin_cases p <;> decide +kernel

private theorem transition_check_396 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 396) (generatorPermutation s p) =
      generatorPermutation s (rowForward 396 p) := by
  decide +kernel

private theorem code_encoding_396 :
    code 396 = ∑ p : Fin 12, (rowForward 396 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_396 : code 396 < code 397 := by
  decide +kernel

private theorem row_image_397 (p : Fin 12) :
    (rows 397).val p = rowForward 397 p := by
  calc
    (rows 397).val p = rowPoint 397 p := (rowPoint_eq 397 p).symm
    _ = rowForward 397 p := by fin_cases p <;> decide +kernel

private theorem transition_check_397 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 397) (generatorPermutation s p) =
      generatorPermutation s (rowForward 397 p) := by
  decide +kernel

private theorem code_encoding_397 :
    code 397 = ∑ p : Fin 12, (rowForward 397 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_397 : code 397 < code 398 := by
  decide +kernel

private theorem row_image_398 (p : Fin 12) :
    (rows 398).val p = rowForward 398 p := by
  calc
    (rows 398).val p = rowPoint 398 p := (rowPoint_eq 398 p).symm
    _ = rowForward 398 p := by fin_cases p <;> decide +kernel

private theorem transition_check_398 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 398) (generatorPermutation s p) =
      generatorPermutation s (rowForward 398 p) := by
  decide +kernel

private theorem code_encoding_398 :
    code 398 = ∑ p : Fin 12, (rowForward 398 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_398 : code 398 < code 399 := by
  decide +kernel

private theorem row_image_399 (p : Fin 12) :
    (rows 399).val p = rowForward 399 p := by
  calc
    (rows 399).val p = rowPoint 399 p := (rowPoint_eq 399 p).symm
    _ = rowForward 399 p := by fin_cases p <;> decide +kernel

private theorem transition_check_399 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 399) (generatorPermutation s p) =
      generatorPermutation s (rowForward 399 p) := by
  decide +kernel

private theorem code_encoding_399 :
    code 399 = ∑ p : Fin 12, (rowForward 399 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_399 : code 399 < code 400 := by
  decide +kernel

private theorem row_image_400 (p : Fin 12) :
    (rows 400).val p = rowForward 400 p := by
  calc
    (rows 400).val p = rowPoint 400 p := (rowPoint_eq 400 p).symm
    _ = rowForward 400 p := by fin_cases p <;> decide +kernel

private theorem transition_check_400 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 400) (generatorPermutation s p) =
      generatorPermutation s (rowForward 400 p) := by
  decide +kernel

private theorem code_encoding_400 :
    code 400 = ∑ p : Fin 12, (rowForward 400 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_400 : code 400 < code 401 := by
  decide +kernel

private theorem row_image_401 (p : Fin 12) :
    (rows 401).val p = rowForward 401 p := by
  calc
    (rows 401).val p = rowPoint 401 p := (rowPoint_eq 401 p).symm
    _ = rowForward 401 p := by fin_cases p <;> decide +kernel

private theorem transition_check_401 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 401) (generatorPermutation s p) =
      generatorPermutation s (rowForward 401 p) := by
  decide +kernel

private theorem code_encoding_401 :
    code 401 = ∑ p : Fin 12, (rowForward 401 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_401 : code 401 < code 402 := by
  decide +kernel

private theorem row_image_402 (p : Fin 12) :
    (rows 402).val p = rowForward 402 p := by
  calc
    (rows 402).val p = rowPoint 402 p := (rowPoint_eq 402 p).symm
    _ = rowForward 402 p := by fin_cases p <;> decide +kernel

private theorem transition_check_402 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 402) (generatorPermutation s p) =
      generatorPermutation s (rowForward 402 p) := by
  decide +kernel

private theorem code_encoding_402 :
    code 402 = ∑ p : Fin 12, (rowForward 402 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_402 : code 402 < code 403 := by
  decide +kernel

private theorem row_image_403 (p : Fin 12) :
    (rows 403).val p = rowForward 403 p := by
  calc
    (rows 403).val p = rowPoint 403 p := (rowPoint_eq 403 p).symm
    _ = rowForward 403 p := by fin_cases p <;> decide +kernel

private theorem transition_check_403 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 403) (generatorPermutation s p) =
      generatorPermutation s (rowForward 403 p) := by
  decide +kernel

private theorem code_encoding_403 :
    code 403 = ∑ p : Fin 12, (rowForward 403 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_403 : code 403 < code 404 := by
  decide +kernel

private theorem row_image_404 (p : Fin 12) :
    (rows 404).val p = rowForward 404 p := by
  calc
    (rows 404).val p = rowPoint 404 p := (rowPoint_eq 404 p).symm
    _ = rowForward 404 p := by fin_cases p <;> decide +kernel

private theorem transition_check_404 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 404) (generatorPermutation s p) =
      generatorPermutation s (rowForward 404 p) := by
  decide +kernel

private theorem code_encoding_404 :
    code 404 = ∑ p : Fin 12, (rowForward 404 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_404 : code 404 < code 405 := by
  decide +kernel

private theorem row_image_405 (p : Fin 12) :
    (rows 405).val p = rowForward 405 p := by
  calc
    (rows 405).val p = rowPoint 405 p := (rowPoint_eq 405 p).symm
    _ = rowForward 405 p := by fin_cases p <;> decide +kernel

private theorem transition_check_405 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 405) (generatorPermutation s p) =
      generatorPermutation s (rowForward 405 p) := by
  decide +kernel

private theorem code_encoding_405 :
    code 405 = ∑ p : Fin 12, (rowForward 405 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_405 : code 405 < code 406 := by
  decide +kernel

private theorem row_image_406 (p : Fin 12) :
    (rows 406).val p = rowForward 406 p := by
  calc
    (rows 406).val p = rowPoint 406 p := (rowPoint_eq 406 p).symm
    _ = rowForward 406 p := by fin_cases p <;> decide +kernel

private theorem transition_check_406 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 406) (generatorPermutation s p) =
      generatorPermutation s (rowForward 406 p) := by
  decide +kernel

private theorem code_encoding_406 :
    code 406 = ∑ p : Fin 12, (rowForward 406 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_406 : code 406 < code 407 := by
  decide +kernel

private theorem row_image_407 (p : Fin 12) :
    (rows 407).val p = rowForward 407 p := by
  calc
    (rows 407).val p = rowPoint 407 p := (rowPoint_eq 407 p).symm
    _ = rowForward 407 p := by fin_cases p <;> decide +kernel

private theorem transition_check_407 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 407) (generatorPermutation s p) =
      generatorPermutation s (rowForward 407 p) := by
  decide +kernel

private theorem code_encoding_407 :
    code 407 = ∑ p : Fin 12, (rowForward 407 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_407 : code 407 < code 408 := by
  decide +kernel

private theorem row_image_408 (p : Fin 12) :
    (rows 408).val p = rowForward 408 p := by
  calc
    (rows 408).val p = rowPoint 408 p := (rowPoint_eq 408 p).symm
    _ = rowForward 408 p := by fin_cases p <;> decide +kernel

private theorem transition_check_408 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 408) (generatorPermutation s p) =
      generatorPermutation s (rowForward 408 p) := by
  decide +kernel

private theorem code_encoding_408 :
    code 408 = ∑ p : Fin 12, (rowForward 408 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_408 : code 408 < code 409 := by
  decide +kernel

private theorem row_image_409 (p : Fin 12) :
    (rows 409).val p = rowForward 409 p := by
  calc
    (rows 409).val p = rowPoint 409 p := (rowPoint_eq 409 p).symm
    _ = rowForward 409 p := by fin_cases p <;> decide +kernel

private theorem transition_check_409 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 409) (generatorPermutation s p) =
      generatorPermutation s (rowForward 409 p) := by
  decide +kernel

private theorem code_encoding_409 :
    code 409 = ∑ p : Fin 12, (rowForward 409 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_409 : code 409 < code 410 := by
  decide +kernel

private theorem row_image_410 (p : Fin 12) :
    (rows 410).val p = rowForward 410 p := by
  calc
    (rows 410).val p = rowPoint 410 p := (rowPoint_eq 410 p).symm
    _ = rowForward 410 p := by fin_cases p <;> decide +kernel

private theorem transition_check_410 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 410) (generatorPermutation s p) =
      generatorPermutation s (rowForward 410 p) := by
  decide +kernel

private theorem code_encoding_410 :
    code 410 = ∑ p : Fin 12, (rowForward 410 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_410 : code 410 < code 411 := by
  decide +kernel

private theorem row_image_411 (p : Fin 12) :
    (rows 411).val p = rowForward 411 p := by
  calc
    (rows 411).val p = rowPoint 411 p := (rowPoint_eq 411 p).symm
    _ = rowForward 411 p := by fin_cases p <;> decide +kernel

private theorem transition_check_411 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 411) (generatorPermutation s p) =
      generatorPermutation s (rowForward 411 p) := by
  decide +kernel

private theorem code_encoding_411 :
    code 411 = ∑ p : Fin 12, (rowForward 411 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_411 : code 411 < code 412 := by
  decide +kernel

private theorem row_image_412 (p : Fin 12) :
    (rows 412).val p = rowForward 412 p := by
  calc
    (rows 412).val p = rowPoint 412 p := (rowPoint_eq 412 p).symm
    _ = rowForward 412 p := by fin_cases p <;> decide +kernel

private theorem transition_check_412 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 412) (generatorPermutation s p) =
      generatorPermutation s (rowForward 412 p) := by
  decide +kernel

private theorem code_encoding_412 :
    code 412 = ∑ p : Fin 12, (rowForward 412 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_412 : code 412 < code 413 := by
  decide +kernel

private theorem row_image_413 (p : Fin 12) :
    (rows 413).val p = rowForward 413 p := by
  calc
    (rows 413).val p = rowPoint 413 p := (rowPoint_eq 413 p).symm
    _ = rowForward 413 p := by fin_cases p <;> decide +kernel

private theorem transition_check_413 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 413) (generatorPermutation s p) =
      generatorPermutation s (rowForward 413 p) := by
  decide +kernel

private theorem code_encoding_413 :
    code 413 = ∑ p : Fin 12, (rowForward 413 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_413 : code 413 < code 414 := by
  decide +kernel

private theorem row_image_414 (p : Fin 12) :
    (rows 414).val p = rowForward 414 p := by
  calc
    (rows 414).val p = rowPoint 414 p := (rowPoint_eq 414 p).symm
    _ = rowForward 414 p := by fin_cases p <;> decide +kernel

private theorem transition_check_414 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 414) (generatorPermutation s p) =
      generatorPermutation s (rowForward 414 p) := by
  decide +kernel

private theorem code_encoding_414 :
    code 414 = ∑ p : Fin 12, (rowForward 414 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_414 : code 414 < code 415 := by
  decide +kernel

private theorem row_image_415 (p : Fin 12) :
    (rows 415).val p = rowForward 415 p := by
  calc
    (rows 415).val p = rowPoint 415 p := (rowPoint_eq 415 p).symm
    _ = rowForward 415 p := by fin_cases p <;> decide +kernel

private theorem transition_check_415 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 415) (generatorPermutation s p) =
      generatorPermutation s (rowForward 415 p) := by
  decide +kernel

private theorem code_encoding_415 :
    code 415 = ∑ p : Fin 12, (rowForward 415 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_415 : code 415 < code 416 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (384 : Fin 495) from rfl))
      (row_image_384 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (385 : Fin 495) from rfl))
      (row_image_385 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (386 : Fin 495) from rfl))
      (row_image_386 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (387 : Fin 495) from rfl))
      (row_image_387 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (388 : Fin 495) from rfl))
      (row_image_388 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (389 : Fin 495) from rfl))
      (row_image_389 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (390 : Fin 495) from rfl))
      (row_image_390 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (391 : Fin 495) from rfl))
      (row_image_391 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (392 : Fin 495) from rfl))
      (row_image_392 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (393 : Fin 495) from rfl))
      (row_image_393 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (394 : Fin 495) from rfl))
      (row_image_394 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (395 : Fin 495) from rfl))
      (row_image_395 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (396 : Fin 495) from rfl))
      (row_image_396 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (397 : Fin 495) from rfl))
      (row_image_397 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (398 : Fin 495) from rfl))
      (row_image_398 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (399 : Fin 495) from rfl))
      (row_image_399 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (400 : Fin 495) from rfl))
      (row_image_400 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (401 : Fin 495) from rfl))
      (row_image_401 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (402 : Fin 495) from rfl))
      (row_image_402 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (403 : Fin 495) from rfl))
      (row_image_403 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (404 : Fin 495) from rfl))
      (row_image_404 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (405 : Fin 495) from rfl))
      (row_image_405 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (406 : Fin 495) from rfl))
      (row_image_406 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (407 : Fin 495) from rfl))
      (row_image_407 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (408 : Fin 495) from rfl))
      (row_image_408 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (409 : Fin 495) from rfl))
      (row_image_409 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (410 : Fin 495) from rfl))
      (row_image_410 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (411 : Fin 495) from rfl))
      (row_image_411 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (412 : Fin 495) from rfl))
      (row_image_412 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (413 : Fin 495) from rfl))
      (row_image_413 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (414 : Fin 495) from rfl))
      (row_image_414 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (415 : Fin 495) from rfl))
      (row_image_415 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (384 : Fin 495) from rfl))
      (transition_check_384 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (385 : Fin 495) from rfl))
      (transition_check_385 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (386 : Fin 495) from rfl))
      (transition_check_386 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (387 : Fin 495) from rfl))
      (transition_check_387 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (388 : Fin 495) from rfl))
      (transition_check_388 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (389 : Fin 495) from rfl))
      (transition_check_389 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (390 : Fin 495) from rfl))
      (transition_check_390 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (391 : Fin 495) from rfl))
      (transition_check_391 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (392 : Fin 495) from rfl))
      (transition_check_392 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (393 : Fin 495) from rfl))
      (transition_check_393 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (394 : Fin 495) from rfl))
      (transition_check_394 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (395 : Fin 495) from rfl))
      (transition_check_395 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (396 : Fin 495) from rfl))
      (transition_check_396 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (397 : Fin 495) from rfl))
      (transition_check_397 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (398 : Fin 495) from rfl))
      (transition_check_398 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (399 : Fin 495) from rfl))
      (transition_check_399 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (400 : Fin 495) from rfl))
      (transition_check_400 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (401 : Fin 495) from rfl))
      (transition_check_401 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (402 : Fin 495) from rfl))
      (transition_check_402 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (403 : Fin 495) from rfl))
      (transition_check_403 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (404 : Fin 495) from rfl))
      (transition_check_404 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (405 : Fin 495) from rfl))
      (transition_check_405 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (406 : Fin 495) from rfl))
      (transition_check_406 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (407 : Fin 495) from rfl))
      (transition_check_407 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (408 : Fin 495) from rfl))
      (transition_check_408 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (409 : Fin 495) from rfl))
      (transition_check_409 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (410 : Fin 495) from rfl))
      (transition_check_410 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (411 : Fin 495) from rfl))
      (transition_check_411 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (412 : Fin 495) from rfl))
      (transition_check_412 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (413 : Fin 495) from rfl))
      (transition_check_413 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (414 : Fin 495) from rfl))
      (transition_check_414 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (415 : Fin 495) from rfl))
      (transition_check_415 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (384 : Fin 495) from rfl))
      code_encoding_384
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (385 : Fin 495) from rfl))
      code_encoding_385
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (386 : Fin 495) from rfl))
      code_encoding_386
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (387 : Fin 495) from rfl))
      code_encoding_387
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (388 : Fin 495) from rfl))
      code_encoding_388
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (389 : Fin 495) from rfl))
      code_encoding_389
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (390 : Fin 495) from rfl))
      code_encoding_390
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (391 : Fin 495) from rfl))
      code_encoding_391
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (392 : Fin 495) from rfl))
      code_encoding_392
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (393 : Fin 495) from rfl))
      code_encoding_393
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (394 : Fin 495) from rfl))
      code_encoding_394
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (395 : Fin 495) from rfl))
      code_encoding_395
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (396 : Fin 495) from rfl))
      code_encoding_396
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (397 : Fin 495) from rfl))
      code_encoding_397
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (398 : Fin 495) from rfl))
      code_encoding_398
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (399 : Fin 495) from rfl))
      code_encoding_399
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (400 : Fin 495) from rfl))
      code_encoding_400
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (401 : Fin 495) from rfl))
      code_encoding_401
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (402 : Fin 495) from rfl))
      code_encoding_402
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (403 : Fin 495) from rfl))
      code_encoding_403
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (404 : Fin 495) from rfl))
      code_encoding_404
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (405 : Fin 495) from rfl))
      code_encoding_405
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (406 : Fin 495) from rfl))
      code_encoding_406
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (407 : Fin 495) from rfl))
      code_encoding_407
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (408 : Fin 495) from rfl))
      code_encoding_408
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (409 : Fin 495) from rfl))
      code_encoding_409
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (410 : Fin 495) from rfl))
      code_encoding_410
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (411 : Fin 495) from rfl))
      code_encoding_411
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (412 : Fin 495) from rfl))
      code_encoding_412
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (413 : Fin 495) from rfl))
      code_encoding_413
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (414 : Fin 495) from rfl))
      code_encoding_414
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (415 : Fin 495) from rfl))
      code_encoding_415

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (384 : Fin 495) from rfl))
    intro h
    exact code_adjacent_384
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (385 : Fin 495) from rfl))
    intro h
    exact code_adjacent_385
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (386 : Fin 495) from rfl))
    intro h
    exact code_adjacent_386
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (387 : Fin 495) from rfl))
    intro h
    exact code_adjacent_387
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (388 : Fin 495) from rfl))
    intro h
    exact code_adjacent_388
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (389 : Fin 495) from rfl))
    intro h
    exact code_adjacent_389
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (390 : Fin 495) from rfl))
    intro h
    exact code_adjacent_390
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (391 : Fin 495) from rfl))
    intro h
    exact code_adjacent_391
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (392 : Fin 495) from rfl))
    intro h
    exact code_adjacent_392
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (393 : Fin 495) from rfl))
    intro h
    exact code_adjacent_393
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (394 : Fin 495) from rfl))
    intro h
    exact code_adjacent_394
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (395 : Fin 495) from rfl))
    intro h
    exact code_adjacent_395
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (396 : Fin 495) from rfl))
    intro h
    exact code_adjacent_396
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (397 : Fin 495) from rfl))
    intro h
    exact code_adjacent_397
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (398 : Fin 495) from rfl))
    intro h
    exact code_adjacent_398
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (399 : Fin 495) from rfl))
    intro h
    exact code_adjacent_399
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (400 : Fin 495) from rfl))
    intro h
    exact code_adjacent_400
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (401 : Fin 495) from rfl))
    intro h
    exact code_adjacent_401
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (402 : Fin 495) from rfl))
    intro h
    exact code_adjacent_402
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (403 : Fin 495) from rfl))
    intro h
    exact code_adjacent_403
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (404 : Fin 495) from rfl))
    intro h
    exact code_adjacent_404
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (405 : Fin 495) from rfl))
    intro h
    exact code_adjacent_405
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (406 : Fin 495) from rfl))
    intro h
    exact code_adjacent_406
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (407 : Fin 495) from rfl))
    intro h
    exact code_adjacent_407
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (408 : Fin 495) from rfl))
    intro h
    exact code_adjacent_408
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (409 : Fin 495) from rfl))
    intro h
    exact code_adjacent_409
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (410 : Fin 495) from rfl))
    intro h
    exact code_adjacent_410
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (411 : Fin 495) from rfl))
    intro h
    exact code_adjacent_411
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (412 : Fin 495) from rfl))
    intro h
    exact code_adjacent_412
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (413 : Fin 495) from rfl))
    intro h
    exact code_adjacent_413
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (414 : Fin 495) from rfl))
    intro h
    exact code_adjacent_414
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (415 : Fin 495) from rfl))
    intro h
    exact code_adjacent_415

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock12
