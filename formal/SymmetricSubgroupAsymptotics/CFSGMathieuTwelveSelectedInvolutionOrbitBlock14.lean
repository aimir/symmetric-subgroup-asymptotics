import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows448..479.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock14
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨448+i.val,by omega⟩

private theorem row_image_448 (p : Fin 12) :
    (rows 448).val p = rowForward 448 p := by
  calc
    (rows 448).val p = rowPoint 448 p := (rowPoint_eq 448 p).symm
    _ = rowForward 448 p := by fin_cases p <;> decide +kernel

private theorem transition_check_448 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 448) (generatorPermutation s p) =
      generatorPermutation s (rowForward 448 p) := by
  decide +kernel

private theorem code_encoding_448 :
    code 448 = ∑ p : Fin 12, (rowForward 448 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_448 : code 448 < code 449 := by
  decide +kernel

private theorem row_image_449 (p : Fin 12) :
    (rows 449).val p = rowForward 449 p := by
  calc
    (rows 449).val p = rowPoint 449 p := (rowPoint_eq 449 p).symm
    _ = rowForward 449 p := by fin_cases p <;> decide +kernel

private theorem transition_check_449 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 449) (generatorPermutation s p) =
      generatorPermutation s (rowForward 449 p) := by
  decide +kernel

private theorem code_encoding_449 :
    code 449 = ∑ p : Fin 12, (rowForward 449 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_449 : code 449 < code 450 := by
  decide +kernel

private theorem row_image_450 (p : Fin 12) :
    (rows 450).val p = rowForward 450 p := by
  calc
    (rows 450).val p = rowPoint 450 p := (rowPoint_eq 450 p).symm
    _ = rowForward 450 p := by fin_cases p <;> decide +kernel

private theorem transition_check_450 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 450) (generatorPermutation s p) =
      generatorPermutation s (rowForward 450 p) := by
  decide +kernel

private theorem code_encoding_450 :
    code 450 = ∑ p : Fin 12, (rowForward 450 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_450 : code 450 < code 451 := by
  decide +kernel

private theorem row_image_451 (p : Fin 12) :
    (rows 451).val p = rowForward 451 p := by
  calc
    (rows 451).val p = rowPoint 451 p := (rowPoint_eq 451 p).symm
    _ = rowForward 451 p := by fin_cases p <;> decide +kernel

private theorem transition_check_451 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 451) (generatorPermutation s p) =
      generatorPermutation s (rowForward 451 p) := by
  decide +kernel

private theorem code_encoding_451 :
    code 451 = ∑ p : Fin 12, (rowForward 451 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_451 : code 451 < code 452 := by
  decide +kernel

private theorem row_image_452 (p : Fin 12) :
    (rows 452).val p = rowForward 452 p := by
  calc
    (rows 452).val p = rowPoint 452 p := (rowPoint_eq 452 p).symm
    _ = rowForward 452 p := by fin_cases p <;> decide +kernel

private theorem transition_check_452 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 452) (generatorPermutation s p) =
      generatorPermutation s (rowForward 452 p) := by
  decide +kernel

private theorem code_encoding_452 :
    code 452 = ∑ p : Fin 12, (rowForward 452 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_452 : code 452 < code 453 := by
  decide +kernel

private theorem row_image_453 (p : Fin 12) :
    (rows 453).val p = rowForward 453 p := by
  calc
    (rows 453).val p = rowPoint 453 p := (rowPoint_eq 453 p).symm
    _ = rowForward 453 p := by fin_cases p <;> decide +kernel

private theorem transition_check_453 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 453) (generatorPermutation s p) =
      generatorPermutation s (rowForward 453 p) := by
  decide +kernel

private theorem code_encoding_453 :
    code 453 = ∑ p : Fin 12, (rowForward 453 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_453 : code 453 < code 454 := by
  decide +kernel

private theorem row_image_454 (p : Fin 12) :
    (rows 454).val p = rowForward 454 p := by
  calc
    (rows 454).val p = rowPoint 454 p := (rowPoint_eq 454 p).symm
    _ = rowForward 454 p := by fin_cases p <;> decide +kernel

private theorem transition_check_454 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 454) (generatorPermutation s p) =
      generatorPermutation s (rowForward 454 p) := by
  decide +kernel

private theorem code_encoding_454 :
    code 454 = ∑ p : Fin 12, (rowForward 454 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_454 : code 454 < code 455 := by
  decide +kernel

private theorem row_image_455 (p : Fin 12) :
    (rows 455).val p = rowForward 455 p := by
  calc
    (rows 455).val p = rowPoint 455 p := (rowPoint_eq 455 p).symm
    _ = rowForward 455 p := by fin_cases p <;> decide +kernel

private theorem transition_check_455 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 455) (generatorPermutation s p) =
      generatorPermutation s (rowForward 455 p) := by
  decide +kernel

private theorem code_encoding_455 :
    code 455 = ∑ p : Fin 12, (rowForward 455 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_455 : code 455 < code 456 := by
  decide +kernel

private theorem row_image_456 (p : Fin 12) :
    (rows 456).val p = rowForward 456 p := by
  calc
    (rows 456).val p = rowPoint 456 p := (rowPoint_eq 456 p).symm
    _ = rowForward 456 p := by fin_cases p <;> decide +kernel

private theorem transition_check_456 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 456) (generatorPermutation s p) =
      generatorPermutation s (rowForward 456 p) := by
  decide +kernel

private theorem code_encoding_456 :
    code 456 = ∑ p : Fin 12, (rowForward 456 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_456 : code 456 < code 457 := by
  decide +kernel

private theorem row_image_457 (p : Fin 12) :
    (rows 457).val p = rowForward 457 p := by
  calc
    (rows 457).val p = rowPoint 457 p := (rowPoint_eq 457 p).symm
    _ = rowForward 457 p := by fin_cases p <;> decide +kernel

private theorem transition_check_457 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 457) (generatorPermutation s p) =
      generatorPermutation s (rowForward 457 p) := by
  decide +kernel

private theorem code_encoding_457 :
    code 457 = ∑ p : Fin 12, (rowForward 457 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_457 : code 457 < code 458 := by
  decide +kernel

private theorem row_image_458 (p : Fin 12) :
    (rows 458).val p = rowForward 458 p := by
  calc
    (rows 458).val p = rowPoint 458 p := (rowPoint_eq 458 p).symm
    _ = rowForward 458 p := by fin_cases p <;> decide +kernel

private theorem transition_check_458 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 458) (generatorPermutation s p) =
      generatorPermutation s (rowForward 458 p) := by
  decide +kernel

private theorem code_encoding_458 :
    code 458 = ∑ p : Fin 12, (rowForward 458 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_458 : code 458 < code 459 := by
  decide +kernel

private theorem row_image_459 (p : Fin 12) :
    (rows 459).val p = rowForward 459 p := by
  calc
    (rows 459).val p = rowPoint 459 p := (rowPoint_eq 459 p).symm
    _ = rowForward 459 p := by fin_cases p <;> decide +kernel

private theorem transition_check_459 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 459) (generatorPermutation s p) =
      generatorPermutation s (rowForward 459 p) := by
  decide +kernel

private theorem code_encoding_459 :
    code 459 = ∑ p : Fin 12, (rowForward 459 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_459 : code 459 < code 460 := by
  decide +kernel

private theorem row_image_460 (p : Fin 12) :
    (rows 460).val p = rowForward 460 p := by
  calc
    (rows 460).val p = rowPoint 460 p := (rowPoint_eq 460 p).symm
    _ = rowForward 460 p := by fin_cases p <;> decide +kernel

private theorem transition_check_460 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 460) (generatorPermutation s p) =
      generatorPermutation s (rowForward 460 p) := by
  decide +kernel

private theorem code_encoding_460 :
    code 460 = ∑ p : Fin 12, (rowForward 460 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_460 : code 460 < code 461 := by
  decide +kernel

private theorem row_image_461 (p : Fin 12) :
    (rows 461).val p = rowForward 461 p := by
  calc
    (rows 461).val p = rowPoint 461 p := (rowPoint_eq 461 p).symm
    _ = rowForward 461 p := by fin_cases p <;> decide +kernel

private theorem transition_check_461 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 461) (generatorPermutation s p) =
      generatorPermutation s (rowForward 461 p) := by
  decide +kernel

private theorem code_encoding_461 :
    code 461 = ∑ p : Fin 12, (rowForward 461 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_461 : code 461 < code 462 := by
  decide +kernel

private theorem row_image_462 (p : Fin 12) :
    (rows 462).val p = rowForward 462 p := by
  calc
    (rows 462).val p = rowPoint 462 p := (rowPoint_eq 462 p).symm
    _ = rowForward 462 p := by fin_cases p <;> decide +kernel

private theorem transition_check_462 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 462) (generatorPermutation s p) =
      generatorPermutation s (rowForward 462 p) := by
  decide +kernel

private theorem code_encoding_462 :
    code 462 = ∑ p : Fin 12, (rowForward 462 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_462 : code 462 < code 463 := by
  decide +kernel

private theorem row_image_463 (p : Fin 12) :
    (rows 463).val p = rowForward 463 p := by
  calc
    (rows 463).val p = rowPoint 463 p := (rowPoint_eq 463 p).symm
    _ = rowForward 463 p := by fin_cases p <;> decide +kernel

private theorem transition_check_463 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 463) (generatorPermutation s p) =
      generatorPermutation s (rowForward 463 p) := by
  decide +kernel

private theorem code_encoding_463 :
    code 463 = ∑ p : Fin 12, (rowForward 463 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_463 : code 463 < code 464 := by
  decide +kernel

private theorem row_image_464 (p : Fin 12) :
    (rows 464).val p = rowForward 464 p := by
  calc
    (rows 464).val p = rowPoint 464 p := (rowPoint_eq 464 p).symm
    _ = rowForward 464 p := by fin_cases p <;> decide +kernel

private theorem transition_check_464 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 464) (generatorPermutation s p) =
      generatorPermutation s (rowForward 464 p) := by
  decide +kernel

private theorem code_encoding_464 :
    code 464 = ∑ p : Fin 12, (rowForward 464 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_464 : code 464 < code 465 := by
  decide +kernel

private theorem row_image_465 (p : Fin 12) :
    (rows 465).val p = rowForward 465 p := by
  calc
    (rows 465).val p = rowPoint 465 p := (rowPoint_eq 465 p).symm
    _ = rowForward 465 p := by fin_cases p <;> decide +kernel

private theorem transition_check_465 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 465) (generatorPermutation s p) =
      generatorPermutation s (rowForward 465 p) := by
  decide +kernel

private theorem code_encoding_465 :
    code 465 = ∑ p : Fin 12, (rowForward 465 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_465 : code 465 < code 466 := by
  decide +kernel

private theorem row_image_466 (p : Fin 12) :
    (rows 466).val p = rowForward 466 p := by
  calc
    (rows 466).val p = rowPoint 466 p := (rowPoint_eq 466 p).symm
    _ = rowForward 466 p := by fin_cases p <;> decide +kernel

private theorem transition_check_466 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 466) (generatorPermutation s p) =
      generatorPermutation s (rowForward 466 p) := by
  decide +kernel

private theorem code_encoding_466 :
    code 466 = ∑ p : Fin 12, (rowForward 466 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_466 : code 466 < code 467 := by
  decide +kernel

private theorem row_image_467 (p : Fin 12) :
    (rows 467).val p = rowForward 467 p := by
  calc
    (rows 467).val p = rowPoint 467 p := (rowPoint_eq 467 p).symm
    _ = rowForward 467 p := by fin_cases p <;> decide +kernel

private theorem transition_check_467 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 467) (generatorPermutation s p) =
      generatorPermutation s (rowForward 467 p) := by
  decide +kernel

private theorem code_encoding_467 :
    code 467 = ∑ p : Fin 12, (rowForward 467 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_467 : code 467 < code 468 := by
  decide +kernel

private theorem row_image_468 (p : Fin 12) :
    (rows 468).val p = rowForward 468 p := by
  calc
    (rows 468).val p = rowPoint 468 p := (rowPoint_eq 468 p).symm
    _ = rowForward 468 p := by fin_cases p <;> decide +kernel

private theorem transition_check_468 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 468) (generatorPermutation s p) =
      generatorPermutation s (rowForward 468 p) := by
  decide +kernel

private theorem code_encoding_468 :
    code 468 = ∑ p : Fin 12, (rowForward 468 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_468 : code 468 < code 469 := by
  decide +kernel

private theorem row_image_469 (p : Fin 12) :
    (rows 469).val p = rowForward 469 p := by
  calc
    (rows 469).val p = rowPoint 469 p := (rowPoint_eq 469 p).symm
    _ = rowForward 469 p := by fin_cases p <;> decide +kernel

private theorem transition_check_469 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 469) (generatorPermutation s p) =
      generatorPermutation s (rowForward 469 p) := by
  decide +kernel

private theorem code_encoding_469 :
    code 469 = ∑ p : Fin 12, (rowForward 469 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_469 : code 469 < code 470 := by
  decide +kernel

private theorem row_image_470 (p : Fin 12) :
    (rows 470).val p = rowForward 470 p := by
  calc
    (rows 470).val p = rowPoint 470 p := (rowPoint_eq 470 p).symm
    _ = rowForward 470 p := by fin_cases p <;> decide +kernel

private theorem transition_check_470 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 470) (generatorPermutation s p) =
      generatorPermutation s (rowForward 470 p) := by
  decide +kernel

private theorem code_encoding_470 :
    code 470 = ∑ p : Fin 12, (rowForward 470 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_470 : code 470 < code 471 := by
  decide +kernel

private theorem row_image_471 (p : Fin 12) :
    (rows 471).val p = rowForward 471 p := by
  calc
    (rows 471).val p = rowPoint 471 p := (rowPoint_eq 471 p).symm
    _ = rowForward 471 p := by fin_cases p <;> decide +kernel

private theorem transition_check_471 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 471) (generatorPermutation s p) =
      generatorPermutation s (rowForward 471 p) := by
  decide +kernel

private theorem code_encoding_471 :
    code 471 = ∑ p : Fin 12, (rowForward 471 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_471 : code 471 < code 472 := by
  decide +kernel

private theorem row_image_472 (p : Fin 12) :
    (rows 472).val p = rowForward 472 p := by
  calc
    (rows 472).val p = rowPoint 472 p := (rowPoint_eq 472 p).symm
    _ = rowForward 472 p := by fin_cases p <;> decide +kernel

private theorem transition_check_472 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 472) (generatorPermutation s p) =
      generatorPermutation s (rowForward 472 p) := by
  decide +kernel

private theorem code_encoding_472 :
    code 472 = ∑ p : Fin 12, (rowForward 472 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_472 : code 472 < code 473 := by
  decide +kernel

private theorem row_image_473 (p : Fin 12) :
    (rows 473).val p = rowForward 473 p := by
  calc
    (rows 473).val p = rowPoint 473 p := (rowPoint_eq 473 p).symm
    _ = rowForward 473 p := by fin_cases p <;> decide +kernel

private theorem transition_check_473 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 473) (generatorPermutation s p) =
      generatorPermutation s (rowForward 473 p) := by
  decide +kernel

private theorem code_encoding_473 :
    code 473 = ∑ p : Fin 12, (rowForward 473 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_473 : code 473 < code 474 := by
  decide +kernel

private theorem row_image_474 (p : Fin 12) :
    (rows 474).val p = rowForward 474 p := by
  calc
    (rows 474).val p = rowPoint 474 p := (rowPoint_eq 474 p).symm
    _ = rowForward 474 p := by fin_cases p <;> decide +kernel

private theorem transition_check_474 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 474) (generatorPermutation s p) =
      generatorPermutation s (rowForward 474 p) := by
  decide +kernel

private theorem code_encoding_474 :
    code 474 = ∑ p : Fin 12, (rowForward 474 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_474 : code 474 < code 475 := by
  decide +kernel

private theorem row_image_475 (p : Fin 12) :
    (rows 475).val p = rowForward 475 p := by
  calc
    (rows 475).val p = rowPoint 475 p := (rowPoint_eq 475 p).symm
    _ = rowForward 475 p := by fin_cases p <;> decide +kernel

private theorem transition_check_475 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 475) (generatorPermutation s p) =
      generatorPermutation s (rowForward 475 p) := by
  decide +kernel

private theorem code_encoding_475 :
    code 475 = ∑ p : Fin 12, (rowForward 475 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_475 : code 475 < code 476 := by
  decide +kernel

private theorem row_image_476 (p : Fin 12) :
    (rows 476).val p = rowForward 476 p := by
  calc
    (rows 476).val p = rowPoint 476 p := (rowPoint_eq 476 p).symm
    _ = rowForward 476 p := by fin_cases p <;> decide +kernel

private theorem transition_check_476 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 476) (generatorPermutation s p) =
      generatorPermutation s (rowForward 476 p) := by
  decide +kernel

private theorem code_encoding_476 :
    code 476 = ∑ p : Fin 12, (rowForward 476 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_476 : code 476 < code 477 := by
  decide +kernel

private theorem row_image_477 (p : Fin 12) :
    (rows 477).val p = rowForward 477 p := by
  calc
    (rows 477).val p = rowPoint 477 p := (rowPoint_eq 477 p).symm
    _ = rowForward 477 p := by fin_cases p <;> decide +kernel

private theorem transition_check_477 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 477) (generatorPermutation s p) =
      generatorPermutation s (rowForward 477 p) := by
  decide +kernel

private theorem code_encoding_477 :
    code 477 = ∑ p : Fin 12, (rowForward 477 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_477 : code 477 < code 478 := by
  decide +kernel

private theorem row_image_478 (p : Fin 12) :
    (rows 478).val p = rowForward 478 p := by
  calc
    (rows 478).val p = rowPoint 478 p := (rowPoint_eq 478 p).symm
    _ = rowForward 478 p := by fin_cases p <;> decide +kernel

private theorem transition_check_478 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 478) (generatorPermutation s p) =
      generatorPermutation s (rowForward 478 p) := by
  decide +kernel

private theorem code_encoding_478 :
    code 478 = ∑ p : Fin 12, (rowForward 478 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_478 : code 478 < code 479 := by
  decide +kernel

private theorem row_image_479 (p : Fin 12) :
    (rows 479).val p = rowForward 479 p := by
  calc
    (rows 479).val p = rowPoint 479 p := (rowPoint_eq 479 p).symm
    _ = rowForward 479 p := by fin_cases p <;> decide +kernel

private theorem transition_check_479 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 479) (generatorPermutation s p) =
      generatorPermutation s (rowForward 479 p) := by
  decide +kernel

private theorem code_encoding_479 :
    code 479 = ∑ p : Fin 12, (rowForward 479 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_479 : code 479 < code 480 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (448 : Fin 495) from rfl))
      (row_image_448 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (449 : Fin 495) from rfl))
      (row_image_449 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (450 : Fin 495) from rfl))
      (row_image_450 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (451 : Fin 495) from rfl))
      (row_image_451 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (452 : Fin 495) from rfl))
      (row_image_452 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (453 : Fin 495) from rfl))
      (row_image_453 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (454 : Fin 495) from rfl))
      (row_image_454 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (455 : Fin 495) from rfl))
      (row_image_455 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (456 : Fin 495) from rfl))
      (row_image_456 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (457 : Fin 495) from rfl))
      (row_image_457 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (458 : Fin 495) from rfl))
      (row_image_458 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (459 : Fin 495) from rfl))
      (row_image_459 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (460 : Fin 495) from rfl))
      (row_image_460 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (461 : Fin 495) from rfl))
      (row_image_461 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (462 : Fin 495) from rfl))
      (row_image_462 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (463 : Fin 495) from rfl))
      (row_image_463 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (464 : Fin 495) from rfl))
      (row_image_464 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (465 : Fin 495) from rfl))
      (row_image_465 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (466 : Fin 495) from rfl))
      (row_image_466 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (467 : Fin 495) from rfl))
      (row_image_467 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (468 : Fin 495) from rfl))
      (row_image_468 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (469 : Fin 495) from rfl))
      (row_image_469 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (470 : Fin 495) from rfl))
      (row_image_470 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (471 : Fin 495) from rfl))
      (row_image_471 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (472 : Fin 495) from rfl))
      (row_image_472 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (473 : Fin 495) from rfl))
      (row_image_473 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (474 : Fin 495) from rfl))
      (row_image_474 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (475 : Fin 495) from rfl))
      (row_image_475 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (476 : Fin 495) from rfl))
      (row_image_476 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (477 : Fin 495) from rfl))
      (row_image_477 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (478 : Fin 495) from rfl))
      (row_image_478 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (479 : Fin 495) from rfl))
      (row_image_479 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (448 : Fin 495) from rfl))
      (transition_check_448 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (449 : Fin 495) from rfl))
      (transition_check_449 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (450 : Fin 495) from rfl))
      (transition_check_450 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (451 : Fin 495) from rfl))
      (transition_check_451 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (452 : Fin 495) from rfl))
      (transition_check_452 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (453 : Fin 495) from rfl))
      (transition_check_453 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (454 : Fin 495) from rfl))
      (transition_check_454 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (455 : Fin 495) from rfl))
      (transition_check_455 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (456 : Fin 495) from rfl))
      (transition_check_456 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (457 : Fin 495) from rfl))
      (transition_check_457 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (458 : Fin 495) from rfl))
      (transition_check_458 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (459 : Fin 495) from rfl))
      (transition_check_459 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (460 : Fin 495) from rfl))
      (transition_check_460 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (461 : Fin 495) from rfl))
      (transition_check_461 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (462 : Fin 495) from rfl))
      (transition_check_462 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (463 : Fin 495) from rfl))
      (transition_check_463 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (464 : Fin 495) from rfl))
      (transition_check_464 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (465 : Fin 495) from rfl))
      (transition_check_465 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (466 : Fin 495) from rfl))
      (transition_check_466 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (467 : Fin 495) from rfl))
      (transition_check_467 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (468 : Fin 495) from rfl))
      (transition_check_468 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (469 : Fin 495) from rfl))
      (transition_check_469 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (470 : Fin 495) from rfl))
      (transition_check_470 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (471 : Fin 495) from rfl))
      (transition_check_471 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (472 : Fin 495) from rfl))
      (transition_check_472 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (473 : Fin 495) from rfl))
      (transition_check_473 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (474 : Fin 495) from rfl))
      (transition_check_474 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (475 : Fin 495) from rfl))
      (transition_check_475 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (476 : Fin 495) from rfl))
      (transition_check_476 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (477 : Fin 495) from rfl))
      (transition_check_477 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (478 : Fin 495) from rfl))
      (transition_check_478 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (479 : Fin 495) from rfl))
      (transition_check_479 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (448 : Fin 495) from rfl))
      code_encoding_448
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (449 : Fin 495) from rfl))
      code_encoding_449
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (450 : Fin 495) from rfl))
      code_encoding_450
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (451 : Fin 495) from rfl))
      code_encoding_451
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (452 : Fin 495) from rfl))
      code_encoding_452
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (453 : Fin 495) from rfl))
      code_encoding_453
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (454 : Fin 495) from rfl))
      code_encoding_454
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (455 : Fin 495) from rfl))
      code_encoding_455
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (456 : Fin 495) from rfl))
      code_encoding_456
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (457 : Fin 495) from rfl))
      code_encoding_457
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (458 : Fin 495) from rfl))
      code_encoding_458
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (459 : Fin 495) from rfl))
      code_encoding_459
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (460 : Fin 495) from rfl))
      code_encoding_460
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (461 : Fin 495) from rfl))
      code_encoding_461
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (462 : Fin 495) from rfl))
      code_encoding_462
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (463 : Fin 495) from rfl))
      code_encoding_463
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (464 : Fin 495) from rfl))
      code_encoding_464
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (465 : Fin 495) from rfl))
      code_encoding_465
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (466 : Fin 495) from rfl))
      code_encoding_466
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (467 : Fin 495) from rfl))
      code_encoding_467
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (468 : Fin 495) from rfl))
      code_encoding_468
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (469 : Fin 495) from rfl))
      code_encoding_469
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (470 : Fin 495) from rfl))
      code_encoding_470
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (471 : Fin 495) from rfl))
      code_encoding_471
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (472 : Fin 495) from rfl))
      code_encoding_472
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (473 : Fin 495) from rfl))
      code_encoding_473
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (474 : Fin 495) from rfl))
      code_encoding_474
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (475 : Fin 495) from rfl))
      code_encoding_475
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (476 : Fin 495) from rfl))
      code_encoding_476
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (477 : Fin 495) from rfl))
      code_encoding_477
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (478 : Fin 495) from rfl))
      code_encoding_478
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (479 : Fin 495) from rfl))
      code_encoding_479

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (448 : Fin 495) from rfl))
    intro h
    exact code_adjacent_448
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (449 : Fin 495) from rfl))
    intro h
    exact code_adjacent_449
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (450 : Fin 495) from rfl))
    intro h
    exact code_adjacent_450
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (451 : Fin 495) from rfl))
    intro h
    exact code_adjacent_451
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (452 : Fin 495) from rfl))
    intro h
    exact code_adjacent_452
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (453 : Fin 495) from rfl))
    intro h
    exact code_adjacent_453
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (454 : Fin 495) from rfl))
    intro h
    exact code_adjacent_454
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (455 : Fin 495) from rfl))
    intro h
    exact code_adjacent_455
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (456 : Fin 495) from rfl))
    intro h
    exact code_adjacent_456
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (457 : Fin 495) from rfl))
    intro h
    exact code_adjacent_457
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (458 : Fin 495) from rfl))
    intro h
    exact code_adjacent_458
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (459 : Fin 495) from rfl))
    intro h
    exact code_adjacent_459
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (460 : Fin 495) from rfl))
    intro h
    exact code_adjacent_460
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (461 : Fin 495) from rfl))
    intro h
    exact code_adjacent_461
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (462 : Fin 495) from rfl))
    intro h
    exact code_adjacent_462
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (463 : Fin 495) from rfl))
    intro h
    exact code_adjacent_463
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (464 : Fin 495) from rfl))
    intro h
    exact code_adjacent_464
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (465 : Fin 495) from rfl))
    intro h
    exact code_adjacent_465
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (466 : Fin 495) from rfl))
    intro h
    exact code_adjacent_466
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (467 : Fin 495) from rfl))
    intro h
    exact code_adjacent_467
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (468 : Fin 495) from rfl))
    intro h
    exact code_adjacent_468
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (469 : Fin 495) from rfl))
    intro h
    exact code_adjacent_469
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (470 : Fin 495) from rfl))
    intro h
    exact code_adjacent_470
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (471 : Fin 495) from rfl))
    intro h
    exact code_adjacent_471
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (472 : Fin 495) from rfl))
    intro h
    exact code_adjacent_472
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (473 : Fin 495) from rfl))
    intro h
    exact code_adjacent_473
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (474 : Fin 495) from rfl))
    intro h
    exact code_adjacent_474
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (475 : Fin 495) from rfl))
    intro h
    exact code_adjacent_475
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (476 : Fin 495) from rfl))
    intro h
    exact code_adjacent_476
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (477 : Fin 495) from rfl))
    intro h
    exact code_adjacent_477
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (478 : Fin 495) from rfl))
    intro h
    exact code_adjacent_478
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (479 : Fin 495) from rfl))
    intro h
    exact code_adjacent_479

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock14
