import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows416..447.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock13
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 32) : Fin 495 := ⟨416+i.val,by omega⟩

private theorem row_image_416 (p : Fin 12) :
    (rows 416).val p = rowForward 416 p := by
  calc
    (rows 416).val p = rowPoint 416 p := (rowPoint_eq 416 p).symm
    _ = rowForward 416 p := by fin_cases p <;> decide +kernel

private theorem transition_check_416 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 416) (generatorPermutation s p) =
      generatorPermutation s (rowForward 416 p) := by
  decide +kernel

private theorem code_encoding_416 :
    code 416 = ∑ p : Fin 12, (rowForward 416 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_416 : code 416 < code 417 := by
  decide +kernel

private theorem row_image_417 (p : Fin 12) :
    (rows 417).val p = rowForward 417 p := by
  calc
    (rows 417).val p = rowPoint 417 p := (rowPoint_eq 417 p).symm
    _ = rowForward 417 p := by fin_cases p <;> decide +kernel

private theorem transition_check_417 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 417) (generatorPermutation s p) =
      generatorPermutation s (rowForward 417 p) := by
  decide +kernel

private theorem code_encoding_417 :
    code 417 = ∑ p : Fin 12, (rowForward 417 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_417 : code 417 < code 418 := by
  decide +kernel

private theorem row_image_418 (p : Fin 12) :
    (rows 418).val p = rowForward 418 p := by
  calc
    (rows 418).val p = rowPoint 418 p := (rowPoint_eq 418 p).symm
    _ = rowForward 418 p := by fin_cases p <;> decide +kernel

private theorem transition_check_418 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 418) (generatorPermutation s p) =
      generatorPermutation s (rowForward 418 p) := by
  decide +kernel

private theorem code_encoding_418 :
    code 418 = ∑ p : Fin 12, (rowForward 418 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_418 : code 418 < code 419 := by
  decide +kernel

private theorem row_image_419 (p : Fin 12) :
    (rows 419).val p = rowForward 419 p := by
  calc
    (rows 419).val p = rowPoint 419 p := (rowPoint_eq 419 p).symm
    _ = rowForward 419 p := by fin_cases p <;> decide +kernel

private theorem transition_check_419 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 419) (generatorPermutation s p) =
      generatorPermutation s (rowForward 419 p) := by
  decide +kernel

private theorem code_encoding_419 :
    code 419 = ∑ p : Fin 12, (rowForward 419 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_419 : code 419 < code 420 := by
  decide +kernel

private theorem row_image_420 (p : Fin 12) :
    (rows 420).val p = rowForward 420 p := by
  calc
    (rows 420).val p = rowPoint 420 p := (rowPoint_eq 420 p).symm
    _ = rowForward 420 p := by fin_cases p <;> decide +kernel

private theorem transition_check_420 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 420) (generatorPermutation s p) =
      generatorPermutation s (rowForward 420 p) := by
  decide +kernel

private theorem code_encoding_420 :
    code 420 = ∑ p : Fin 12, (rowForward 420 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_420 : code 420 < code 421 := by
  decide +kernel

private theorem row_image_421 (p : Fin 12) :
    (rows 421).val p = rowForward 421 p := by
  calc
    (rows 421).val p = rowPoint 421 p := (rowPoint_eq 421 p).symm
    _ = rowForward 421 p := by fin_cases p <;> decide +kernel

private theorem transition_check_421 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 421) (generatorPermutation s p) =
      generatorPermutation s (rowForward 421 p) := by
  decide +kernel

private theorem code_encoding_421 :
    code 421 = ∑ p : Fin 12, (rowForward 421 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_421 : code 421 < code 422 := by
  decide +kernel

private theorem row_image_422 (p : Fin 12) :
    (rows 422).val p = rowForward 422 p := by
  calc
    (rows 422).val p = rowPoint 422 p := (rowPoint_eq 422 p).symm
    _ = rowForward 422 p := by fin_cases p <;> decide +kernel

private theorem transition_check_422 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 422) (generatorPermutation s p) =
      generatorPermutation s (rowForward 422 p) := by
  decide +kernel

private theorem code_encoding_422 :
    code 422 = ∑ p : Fin 12, (rowForward 422 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_422 : code 422 < code 423 := by
  decide +kernel

private theorem row_image_423 (p : Fin 12) :
    (rows 423).val p = rowForward 423 p := by
  calc
    (rows 423).val p = rowPoint 423 p := (rowPoint_eq 423 p).symm
    _ = rowForward 423 p := by fin_cases p <;> decide +kernel

private theorem transition_check_423 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 423) (generatorPermutation s p) =
      generatorPermutation s (rowForward 423 p) := by
  decide +kernel

private theorem code_encoding_423 :
    code 423 = ∑ p : Fin 12, (rowForward 423 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_423 : code 423 < code 424 := by
  decide +kernel

private theorem row_image_424 (p : Fin 12) :
    (rows 424).val p = rowForward 424 p := by
  calc
    (rows 424).val p = rowPoint 424 p := (rowPoint_eq 424 p).symm
    _ = rowForward 424 p := by fin_cases p <;> decide +kernel

private theorem transition_check_424 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 424) (generatorPermutation s p) =
      generatorPermutation s (rowForward 424 p) := by
  decide +kernel

private theorem code_encoding_424 :
    code 424 = ∑ p : Fin 12, (rowForward 424 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_424 : code 424 < code 425 := by
  decide +kernel

private theorem row_image_425 (p : Fin 12) :
    (rows 425).val p = rowForward 425 p := by
  calc
    (rows 425).val p = rowPoint 425 p := (rowPoint_eq 425 p).symm
    _ = rowForward 425 p := by fin_cases p <;> decide +kernel

private theorem transition_check_425 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 425) (generatorPermutation s p) =
      generatorPermutation s (rowForward 425 p) := by
  decide +kernel

private theorem code_encoding_425 :
    code 425 = ∑ p : Fin 12, (rowForward 425 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_425 : code 425 < code 426 := by
  decide +kernel

private theorem row_image_426 (p : Fin 12) :
    (rows 426).val p = rowForward 426 p := by
  calc
    (rows 426).val p = rowPoint 426 p := (rowPoint_eq 426 p).symm
    _ = rowForward 426 p := by fin_cases p <;> decide +kernel

private theorem transition_check_426 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 426) (generatorPermutation s p) =
      generatorPermutation s (rowForward 426 p) := by
  decide +kernel

private theorem code_encoding_426 :
    code 426 = ∑ p : Fin 12, (rowForward 426 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_426 : code 426 < code 427 := by
  decide +kernel

private theorem row_image_427 (p : Fin 12) :
    (rows 427).val p = rowForward 427 p := by
  calc
    (rows 427).val p = rowPoint 427 p := (rowPoint_eq 427 p).symm
    _ = rowForward 427 p := by fin_cases p <;> decide +kernel

private theorem transition_check_427 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 427) (generatorPermutation s p) =
      generatorPermutation s (rowForward 427 p) := by
  decide +kernel

private theorem code_encoding_427 :
    code 427 = ∑ p : Fin 12, (rowForward 427 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_427 : code 427 < code 428 := by
  decide +kernel

private theorem row_image_428 (p : Fin 12) :
    (rows 428).val p = rowForward 428 p := by
  calc
    (rows 428).val p = rowPoint 428 p := (rowPoint_eq 428 p).symm
    _ = rowForward 428 p := by fin_cases p <;> decide +kernel

private theorem transition_check_428 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 428) (generatorPermutation s p) =
      generatorPermutation s (rowForward 428 p) := by
  decide +kernel

private theorem code_encoding_428 :
    code 428 = ∑ p : Fin 12, (rowForward 428 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_428 : code 428 < code 429 := by
  decide +kernel

private theorem row_image_429 (p : Fin 12) :
    (rows 429).val p = rowForward 429 p := by
  calc
    (rows 429).val p = rowPoint 429 p := (rowPoint_eq 429 p).symm
    _ = rowForward 429 p := by fin_cases p <;> decide +kernel

private theorem transition_check_429 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 429) (generatorPermutation s p) =
      generatorPermutation s (rowForward 429 p) := by
  decide +kernel

private theorem code_encoding_429 :
    code 429 = ∑ p : Fin 12, (rowForward 429 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_429 : code 429 < code 430 := by
  decide +kernel

private theorem row_image_430 (p : Fin 12) :
    (rows 430).val p = rowForward 430 p := by
  calc
    (rows 430).val p = rowPoint 430 p := (rowPoint_eq 430 p).symm
    _ = rowForward 430 p := by fin_cases p <;> decide +kernel

private theorem transition_check_430 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 430) (generatorPermutation s p) =
      generatorPermutation s (rowForward 430 p) := by
  decide +kernel

private theorem code_encoding_430 :
    code 430 = ∑ p : Fin 12, (rowForward 430 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_430 : code 430 < code 431 := by
  decide +kernel

private theorem row_image_431 (p : Fin 12) :
    (rows 431).val p = rowForward 431 p := by
  calc
    (rows 431).val p = rowPoint 431 p := (rowPoint_eq 431 p).symm
    _ = rowForward 431 p := by fin_cases p <;> decide +kernel

private theorem transition_check_431 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 431) (generatorPermutation s p) =
      generatorPermutation s (rowForward 431 p) := by
  decide +kernel

private theorem code_encoding_431 :
    code 431 = ∑ p : Fin 12, (rowForward 431 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_431 : code 431 < code 432 := by
  decide +kernel

private theorem row_image_432 (p : Fin 12) :
    (rows 432).val p = rowForward 432 p := by
  calc
    (rows 432).val p = rowPoint 432 p := (rowPoint_eq 432 p).symm
    _ = rowForward 432 p := by fin_cases p <;> decide +kernel

private theorem transition_check_432 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 432) (generatorPermutation s p) =
      generatorPermutation s (rowForward 432 p) := by
  decide +kernel

private theorem code_encoding_432 :
    code 432 = ∑ p : Fin 12, (rowForward 432 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_432 : code 432 < code 433 := by
  decide +kernel

private theorem row_image_433 (p : Fin 12) :
    (rows 433).val p = rowForward 433 p := by
  calc
    (rows 433).val p = rowPoint 433 p := (rowPoint_eq 433 p).symm
    _ = rowForward 433 p := by fin_cases p <;> decide +kernel

private theorem transition_check_433 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 433) (generatorPermutation s p) =
      generatorPermutation s (rowForward 433 p) := by
  decide +kernel

private theorem code_encoding_433 :
    code 433 = ∑ p : Fin 12, (rowForward 433 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_433 : code 433 < code 434 := by
  decide +kernel

private theorem row_image_434 (p : Fin 12) :
    (rows 434).val p = rowForward 434 p := by
  calc
    (rows 434).val p = rowPoint 434 p := (rowPoint_eq 434 p).symm
    _ = rowForward 434 p := by fin_cases p <;> decide +kernel

private theorem transition_check_434 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 434) (generatorPermutation s p) =
      generatorPermutation s (rowForward 434 p) := by
  decide +kernel

private theorem code_encoding_434 :
    code 434 = ∑ p : Fin 12, (rowForward 434 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_434 : code 434 < code 435 := by
  decide +kernel

private theorem row_image_435 (p : Fin 12) :
    (rows 435).val p = rowForward 435 p := by
  calc
    (rows 435).val p = rowPoint 435 p := (rowPoint_eq 435 p).symm
    _ = rowForward 435 p := by fin_cases p <;> decide +kernel

private theorem transition_check_435 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 435) (generatorPermutation s p) =
      generatorPermutation s (rowForward 435 p) := by
  decide +kernel

private theorem code_encoding_435 :
    code 435 = ∑ p : Fin 12, (rowForward 435 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_435 : code 435 < code 436 := by
  decide +kernel

private theorem row_image_436 (p : Fin 12) :
    (rows 436).val p = rowForward 436 p := by
  calc
    (rows 436).val p = rowPoint 436 p := (rowPoint_eq 436 p).symm
    _ = rowForward 436 p := by fin_cases p <;> decide +kernel

private theorem transition_check_436 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 436) (generatorPermutation s p) =
      generatorPermutation s (rowForward 436 p) := by
  decide +kernel

private theorem code_encoding_436 :
    code 436 = ∑ p : Fin 12, (rowForward 436 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_436 : code 436 < code 437 := by
  decide +kernel

private theorem row_image_437 (p : Fin 12) :
    (rows 437).val p = rowForward 437 p := by
  calc
    (rows 437).val p = rowPoint 437 p := (rowPoint_eq 437 p).symm
    _ = rowForward 437 p := by fin_cases p <;> decide +kernel

private theorem transition_check_437 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 437) (generatorPermutation s p) =
      generatorPermutation s (rowForward 437 p) := by
  decide +kernel

private theorem code_encoding_437 :
    code 437 = ∑ p : Fin 12, (rowForward 437 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_437 : code 437 < code 438 := by
  decide +kernel

private theorem row_image_438 (p : Fin 12) :
    (rows 438).val p = rowForward 438 p := by
  calc
    (rows 438).val p = rowPoint 438 p := (rowPoint_eq 438 p).symm
    _ = rowForward 438 p := by fin_cases p <;> decide +kernel

private theorem transition_check_438 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 438) (generatorPermutation s p) =
      generatorPermutation s (rowForward 438 p) := by
  decide +kernel

private theorem code_encoding_438 :
    code 438 = ∑ p : Fin 12, (rowForward 438 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_438 : code 438 < code 439 := by
  decide +kernel

private theorem row_image_439 (p : Fin 12) :
    (rows 439).val p = rowForward 439 p := by
  calc
    (rows 439).val p = rowPoint 439 p := (rowPoint_eq 439 p).symm
    _ = rowForward 439 p := by fin_cases p <;> decide +kernel

private theorem transition_check_439 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 439) (generatorPermutation s p) =
      generatorPermutation s (rowForward 439 p) := by
  decide +kernel

private theorem code_encoding_439 :
    code 439 = ∑ p : Fin 12, (rowForward 439 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_439 : code 439 < code 440 := by
  decide +kernel

private theorem row_image_440 (p : Fin 12) :
    (rows 440).val p = rowForward 440 p := by
  calc
    (rows 440).val p = rowPoint 440 p := (rowPoint_eq 440 p).symm
    _ = rowForward 440 p := by fin_cases p <;> decide +kernel

private theorem transition_check_440 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 440) (generatorPermutation s p) =
      generatorPermutation s (rowForward 440 p) := by
  decide +kernel

private theorem code_encoding_440 :
    code 440 = ∑ p : Fin 12, (rowForward 440 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_440 : code 440 < code 441 := by
  decide +kernel

private theorem row_image_441 (p : Fin 12) :
    (rows 441).val p = rowForward 441 p := by
  calc
    (rows 441).val p = rowPoint 441 p := (rowPoint_eq 441 p).symm
    _ = rowForward 441 p := by fin_cases p <;> decide +kernel

private theorem transition_check_441 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 441) (generatorPermutation s p) =
      generatorPermutation s (rowForward 441 p) := by
  decide +kernel

private theorem code_encoding_441 :
    code 441 = ∑ p : Fin 12, (rowForward 441 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_441 : code 441 < code 442 := by
  decide +kernel

private theorem row_image_442 (p : Fin 12) :
    (rows 442).val p = rowForward 442 p := by
  calc
    (rows 442).val p = rowPoint 442 p := (rowPoint_eq 442 p).symm
    _ = rowForward 442 p := by fin_cases p <;> decide +kernel

private theorem transition_check_442 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 442) (generatorPermutation s p) =
      generatorPermutation s (rowForward 442 p) := by
  decide +kernel

private theorem code_encoding_442 :
    code 442 = ∑ p : Fin 12, (rowForward 442 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_442 : code 442 < code 443 := by
  decide +kernel

private theorem row_image_443 (p : Fin 12) :
    (rows 443).val p = rowForward 443 p := by
  calc
    (rows 443).val p = rowPoint 443 p := (rowPoint_eq 443 p).symm
    _ = rowForward 443 p := by fin_cases p <;> decide +kernel

private theorem transition_check_443 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 443) (generatorPermutation s p) =
      generatorPermutation s (rowForward 443 p) := by
  decide +kernel

private theorem code_encoding_443 :
    code 443 = ∑ p : Fin 12, (rowForward 443 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_443 : code 443 < code 444 := by
  decide +kernel

private theorem row_image_444 (p : Fin 12) :
    (rows 444).val p = rowForward 444 p := by
  calc
    (rows 444).val p = rowPoint 444 p := (rowPoint_eq 444 p).symm
    _ = rowForward 444 p := by fin_cases p <;> decide +kernel

private theorem transition_check_444 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 444) (generatorPermutation s p) =
      generatorPermutation s (rowForward 444 p) := by
  decide +kernel

private theorem code_encoding_444 :
    code 444 = ∑ p : Fin 12, (rowForward 444 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_444 : code 444 < code 445 := by
  decide +kernel

private theorem row_image_445 (p : Fin 12) :
    (rows 445).val p = rowForward 445 p := by
  calc
    (rows 445).val p = rowPoint 445 p := (rowPoint_eq 445 p).symm
    _ = rowForward 445 p := by fin_cases p <;> decide +kernel

private theorem transition_check_445 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 445) (generatorPermutation s p) =
      generatorPermutation s (rowForward 445 p) := by
  decide +kernel

private theorem code_encoding_445 :
    code 445 = ∑ p : Fin 12, (rowForward 445 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_445 : code 445 < code 446 := by
  decide +kernel

private theorem row_image_446 (p : Fin 12) :
    (rows 446).val p = rowForward 446 p := by
  calc
    (rows 446).val p = rowPoint 446 p := (rowPoint_eq 446 p).symm
    _ = rowForward 446 p := by fin_cases p <;> decide +kernel

private theorem transition_check_446 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 446) (generatorPermutation s p) =
      generatorPermutation s (rowForward 446 p) := by
  decide +kernel

private theorem code_encoding_446 :
    code 446 = ∑ p : Fin 12, (rowForward 446 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_446 : code 446 < code 447 := by
  decide +kernel

private theorem row_image_447 (p : Fin 12) :
    (rows 447).val p = rowForward 447 p := by
  calc
    (rows 447).val p = rowPoint 447 p := (rowPoint_eq 447 p).symm
    _ = rowForward 447 p := by fin_cases p <;> decide +kernel

private theorem transition_check_447 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 447) (generatorPermutation s p) =
      generatorPermutation s (rowForward 447 p) := by
  decide +kernel

private theorem code_encoding_447 :
    code 447 = ∑ p : Fin 12, (rowForward 447 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_447 : code 447 < code 448 := by
  decide +kernel

theorem row_image (i : Fin 32) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (416 : Fin 495) from rfl))
      (row_image_416 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (417 : Fin 495) from rfl))
      (row_image_417 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (418 : Fin 495) from rfl))
      (row_image_418 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (419 : Fin 495) from rfl))
      (row_image_419 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (420 : Fin 495) from rfl))
      (row_image_420 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (421 : Fin 495) from rfl))
      (row_image_421 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (422 : Fin 495) from rfl))
      (row_image_422 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (423 : Fin 495) from rfl))
      (row_image_423 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (424 : Fin 495) from rfl))
      (row_image_424 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (425 : Fin 495) from rfl))
      (row_image_425 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (426 : Fin 495) from rfl))
      (row_image_426 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (427 : Fin 495) from rfl))
      (row_image_427 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (428 : Fin 495) from rfl))
      (row_image_428 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (429 : Fin 495) from rfl))
      (row_image_429 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (430 : Fin 495) from rfl))
      (row_image_430 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (431 : Fin 495) from rfl))
      (row_image_431 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (432 : Fin 495) from rfl))
      (row_image_432 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (433 : Fin 495) from rfl))
      (row_image_433 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (434 : Fin 495) from rfl))
      (row_image_434 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (435 : Fin 495) from rfl))
      (row_image_435 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (436 : Fin 495) from rfl))
      (row_image_436 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (437 : Fin 495) from rfl))
      (row_image_437 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (438 : Fin 495) from rfl))
      (row_image_438 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (439 : Fin 495) from rfl))
      (row_image_439 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (440 : Fin 495) from rfl))
      (row_image_440 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (441 : Fin 495) from rfl))
      (row_image_441 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (442 : Fin 495) from rfl))
      (row_image_442 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (443 : Fin 495) from rfl))
      (row_image_443 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (444 : Fin 495) from rfl))
      (row_image_444 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (445 : Fin 495) from rfl))
      (row_image_445 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (446 : Fin 495) from rfl))
      (row_image_446 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (447 : Fin 495) from rfl))
      (row_image_447 p)

theorem transition_check (s : Fin 4) (i : Fin 32) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (416 : Fin 495) from rfl))
      (transition_check_416 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (417 : Fin 495) from rfl))
      (transition_check_417 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (418 : Fin 495) from rfl))
      (transition_check_418 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (419 : Fin 495) from rfl))
      (transition_check_419 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (420 : Fin 495) from rfl))
      (transition_check_420 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (421 : Fin 495) from rfl))
      (transition_check_421 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (422 : Fin 495) from rfl))
      (transition_check_422 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (423 : Fin 495) from rfl))
      (transition_check_423 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (424 : Fin 495) from rfl))
      (transition_check_424 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (425 : Fin 495) from rfl))
      (transition_check_425 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (426 : Fin 495) from rfl))
      (transition_check_426 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (427 : Fin 495) from rfl))
      (transition_check_427 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (428 : Fin 495) from rfl))
      (transition_check_428 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (429 : Fin 495) from rfl))
      (transition_check_429 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (430 : Fin 495) from rfl))
      (transition_check_430 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (431 : Fin 495) from rfl))
      (transition_check_431 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (432 : Fin 495) from rfl))
      (transition_check_432 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (433 : Fin 495) from rfl))
      (transition_check_433 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (434 : Fin 495) from rfl))
      (transition_check_434 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (435 : Fin 495) from rfl))
      (transition_check_435 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (436 : Fin 495) from rfl))
      (transition_check_436 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (437 : Fin 495) from rfl))
      (transition_check_437 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (438 : Fin 495) from rfl))
      (transition_check_438 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (439 : Fin 495) from rfl))
      (transition_check_439 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (440 : Fin 495) from rfl))
      (transition_check_440 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (441 : Fin 495) from rfl))
      (transition_check_441 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (442 : Fin 495) from rfl))
      (transition_check_442 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (443 : Fin 495) from rfl))
      (transition_check_443 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (444 : Fin 495) from rfl))
      (transition_check_444 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (445 : Fin 495) from rfl))
      (transition_check_445 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (446 : Fin 495) from rfl))
      (transition_check_446 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (447 : Fin 495) from rfl))
      (transition_check_447 s p)

theorem code_encoding (i : Fin 32) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (416 : Fin 495) from rfl))
      code_encoding_416
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (417 : Fin 495) from rfl))
      code_encoding_417
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (418 : Fin 495) from rfl))
      code_encoding_418
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (419 : Fin 495) from rfl))
      code_encoding_419
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (420 : Fin 495) from rfl))
      code_encoding_420
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (421 : Fin 495) from rfl))
      code_encoding_421
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (422 : Fin 495) from rfl))
      code_encoding_422
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (423 : Fin 495) from rfl))
      code_encoding_423
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (424 : Fin 495) from rfl))
      code_encoding_424
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (425 : Fin 495) from rfl))
      code_encoding_425
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (426 : Fin 495) from rfl))
      code_encoding_426
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (427 : Fin 495) from rfl))
      code_encoding_427
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (428 : Fin 495) from rfl))
      code_encoding_428
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (429 : Fin 495) from rfl))
      code_encoding_429
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (430 : Fin 495) from rfl))
      code_encoding_430
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (431 : Fin 495) from rfl))
      code_encoding_431
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (432 : Fin 495) from rfl))
      code_encoding_432
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (433 : Fin 495) from rfl))
      code_encoding_433
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (434 : Fin 495) from rfl))
      code_encoding_434
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (435 : Fin 495) from rfl))
      code_encoding_435
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (436 : Fin 495) from rfl))
      code_encoding_436
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (437 : Fin 495) from rfl))
      code_encoding_437
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (438 : Fin 495) from rfl))
      code_encoding_438
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (439 : Fin 495) from rfl))
      code_encoding_439
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (440 : Fin 495) from rfl))
      code_encoding_440
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (441 : Fin 495) from rfl))
      code_encoding_441
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (442 : Fin 495) from rfl))
      code_encoding_442
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (443 : Fin 495) from rfl))
      code_encoding_443
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (444 : Fin 495) from rfl))
      code_encoding_444
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (445 : Fin 495) from rfl))
      code_encoding_445
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (446 : Fin 495) from rfl))
      code_encoding_446
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (447 : Fin 495) from rfl))
      code_encoding_447

theorem code_adjacent (i : Fin 32) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 32) = (416 : Fin 495) from rfl))
    intro h
    exact code_adjacent_416
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 32) = (417 : Fin 495) from rfl))
    intro h
    exact code_adjacent_417
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 32) = (418 : Fin 495) from rfl))
    intro h
    exact code_adjacent_418
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 32) = (419 : Fin 495) from rfl))
    intro h
    exact code_adjacent_419
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 32) = (420 : Fin 495) from rfl))
    intro h
    exact code_adjacent_420
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 32) = (421 : Fin 495) from rfl))
    intro h
    exact code_adjacent_421
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 32) = (422 : Fin 495) from rfl))
    intro h
    exact code_adjacent_422
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 32) = (423 : Fin 495) from rfl))
    intro h
    exact code_adjacent_423
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 32) = (424 : Fin 495) from rfl))
    intro h
    exact code_adjacent_424
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 32) = (425 : Fin 495) from rfl))
    intro h
    exact code_adjacent_425
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 32) = (426 : Fin 495) from rfl))
    intro h
    exact code_adjacent_426
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 32) = (427 : Fin 495) from rfl))
    intro h
    exact code_adjacent_427
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 32) = (428 : Fin 495) from rfl))
    intro h
    exact code_adjacent_428
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 32) = (429 : Fin 495) from rfl))
    intro h
    exact code_adjacent_429
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 32) = (430 : Fin 495) from rfl))
    intro h
    exact code_adjacent_430
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨15,by omega⟩ : Fin 32) = (431 : Fin 495) from rfl))
    intro h
    exact code_adjacent_431
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨16,by omega⟩ : Fin 32) = (432 : Fin 495) from rfl))
    intro h
    exact code_adjacent_432
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨17,by omega⟩ : Fin 32) = (433 : Fin 495) from rfl))
    intro h
    exact code_adjacent_433
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨18,by omega⟩ : Fin 32) = (434 : Fin 495) from rfl))
    intro h
    exact code_adjacent_434
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨19,by omega⟩ : Fin 32) = (435 : Fin 495) from rfl))
    intro h
    exact code_adjacent_435
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨20,by omega⟩ : Fin 32) = (436 : Fin 495) from rfl))
    intro h
    exact code_adjacent_436
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨21,by omega⟩ : Fin 32) = (437 : Fin 495) from rfl))
    intro h
    exact code_adjacent_437
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨22,by omega⟩ : Fin 32) = (438 : Fin 495) from rfl))
    intro h
    exact code_adjacent_438
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨23,by omega⟩ : Fin 32) = (439 : Fin 495) from rfl))
    intro h
    exact code_adjacent_439
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨24,by omega⟩ : Fin 32) = (440 : Fin 495) from rfl))
    intro h
    exact code_adjacent_440
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨25,by omega⟩ : Fin 32) = (441 : Fin 495) from rfl))
    intro h
    exact code_adjacent_441
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨26,by omega⟩ : Fin 32) = (442 : Fin 495) from rfl))
    intro h
    exact code_adjacent_442
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨27,by omega⟩ : Fin 32) = (443 : Fin 495) from rfl))
    intro h
    exact code_adjacent_443
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨28,by omega⟩ : Fin 32) = (444 : Fin 495) from rfl))
    intro h
    exact code_adjacent_444
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨29,by omega⟩ : Fin 32) = (445 : Fin 495) from rfl))
    intro h
    exact code_adjacent_445
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨30,by omega⟩ : Fin 32) = (446 : Fin 495) from rfl))
    intro h
    exact code_adjacent_446
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨31,by omega⟩ : Fin 32) = (447 : Fin 495) from rfl))
    intro h
    exact code_adjacent_447

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock13
