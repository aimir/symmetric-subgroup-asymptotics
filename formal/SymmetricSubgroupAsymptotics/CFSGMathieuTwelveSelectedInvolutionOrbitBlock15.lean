import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitData

/-! ONE fixed proof block of the SAME original x495 orbit: rows480..494.
No fresh data, orbit search, capacity premise or full-class claim. Every
numerical command is independent per row; wrappers use explicit index transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock15
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSelectedInvolutionOrbitData

def blockIndex (i : Fin 15) : Fin 495 := ⟨480+i.val,by omega⟩

private theorem row_image_480 (p : Fin 12) :
    (rows 480).val p = rowForward 480 p := by
  calc
    (rows 480).val p = rowPoint 480 p := (rowPoint_eq 480 p).symm
    _ = rowForward 480 p := by fin_cases p <;> decide +kernel

private theorem transition_check_480 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 480) (generatorPermutation s p) =
      generatorPermutation s (rowForward 480 p) := by
  decide +kernel

private theorem code_encoding_480 :
    code 480 = ∑ p : Fin 12, (rowForward 480 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_480 : code 480 < code 481 := by
  decide +kernel

private theorem row_image_481 (p : Fin 12) :
    (rows 481).val p = rowForward 481 p := by
  calc
    (rows 481).val p = rowPoint 481 p := (rowPoint_eq 481 p).symm
    _ = rowForward 481 p := by fin_cases p <;> decide +kernel

private theorem transition_check_481 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 481) (generatorPermutation s p) =
      generatorPermutation s (rowForward 481 p) := by
  decide +kernel

private theorem code_encoding_481 :
    code 481 = ∑ p : Fin 12, (rowForward 481 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_481 : code 481 < code 482 := by
  decide +kernel

private theorem row_image_482 (p : Fin 12) :
    (rows 482).val p = rowForward 482 p := by
  calc
    (rows 482).val p = rowPoint 482 p := (rowPoint_eq 482 p).symm
    _ = rowForward 482 p := by fin_cases p <;> decide +kernel

private theorem transition_check_482 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 482) (generatorPermutation s p) =
      generatorPermutation s (rowForward 482 p) := by
  decide +kernel

private theorem code_encoding_482 :
    code 482 = ∑ p : Fin 12, (rowForward 482 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_482 : code 482 < code 483 := by
  decide +kernel

private theorem row_image_483 (p : Fin 12) :
    (rows 483).val p = rowForward 483 p := by
  calc
    (rows 483).val p = rowPoint 483 p := (rowPoint_eq 483 p).symm
    _ = rowForward 483 p := by fin_cases p <;> decide +kernel

private theorem transition_check_483 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 483) (generatorPermutation s p) =
      generatorPermutation s (rowForward 483 p) := by
  decide +kernel

private theorem code_encoding_483 :
    code 483 = ∑ p : Fin 12, (rowForward 483 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_483 : code 483 < code 484 := by
  decide +kernel

private theorem row_image_484 (p : Fin 12) :
    (rows 484).val p = rowForward 484 p := by
  calc
    (rows 484).val p = rowPoint 484 p := (rowPoint_eq 484 p).symm
    _ = rowForward 484 p := by fin_cases p <;> decide +kernel

private theorem transition_check_484 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 484) (generatorPermutation s p) =
      generatorPermutation s (rowForward 484 p) := by
  decide +kernel

private theorem code_encoding_484 :
    code 484 = ∑ p : Fin 12, (rowForward 484 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_484 : code 484 < code 485 := by
  decide +kernel

private theorem row_image_485 (p : Fin 12) :
    (rows 485).val p = rowForward 485 p := by
  calc
    (rows 485).val p = rowPoint 485 p := (rowPoint_eq 485 p).symm
    _ = rowForward 485 p := by fin_cases p <;> decide +kernel

private theorem transition_check_485 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 485) (generatorPermutation s p) =
      generatorPermutation s (rowForward 485 p) := by
  decide +kernel

private theorem code_encoding_485 :
    code 485 = ∑ p : Fin 12, (rowForward 485 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_485 : code 485 < code 486 := by
  decide +kernel

private theorem row_image_486 (p : Fin 12) :
    (rows 486).val p = rowForward 486 p := by
  calc
    (rows 486).val p = rowPoint 486 p := (rowPoint_eq 486 p).symm
    _ = rowForward 486 p := by fin_cases p <;> decide +kernel

private theorem transition_check_486 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 486) (generatorPermutation s p) =
      generatorPermutation s (rowForward 486 p) := by
  decide +kernel

private theorem code_encoding_486 :
    code 486 = ∑ p : Fin 12, (rowForward 486 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_486 : code 486 < code 487 := by
  decide +kernel

private theorem row_image_487 (p : Fin 12) :
    (rows 487).val p = rowForward 487 p := by
  calc
    (rows 487).val p = rowPoint 487 p := (rowPoint_eq 487 p).symm
    _ = rowForward 487 p := by fin_cases p <;> decide +kernel

private theorem transition_check_487 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 487) (generatorPermutation s p) =
      generatorPermutation s (rowForward 487 p) := by
  decide +kernel

private theorem code_encoding_487 :
    code 487 = ∑ p : Fin 12, (rowForward 487 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_487 : code 487 < code 488 := by
  decide +kernel

private theorem row_image_488 (p : Fin 12) :
    (rows 488).val p = rowForward 488 p := by
  calc
    (rows 488).val p = rowPoint 488 p := (rowPoint_eq 488 p).symm
    _ = rowForward 488 p := by fin_cases p <;> decide +kernel

private theorem transition_check_488 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 488) (generatorPermutation s p) =
      generatorPermutation s (rowForward 488 p) := by
  decide +kernel

private theorem code_encoding_488 :
    code 488 = ∑ p : Fin 12, (rowForward 488 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_488 : code 488 < code 489 := by
  decide +kernel

private theorem row_image_489 (p : Fin 12) :
    (rows 489).val p = rowForward 489 p := by
  calc
    (rows 489).val p = rowPoint 489 p := (rowPoint_eq 489 p).symm
    _ = rowForward 489 p := by fin_cases p <;> decide +kernel

private theorem transition_check_489 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 489) (generatorPermutation s p) =
      generatorPermutation s (rowForward 489 p) := by
  decide +kernel

private theorem code_encoding_489 :
    code 489 = ∑ p : Fin 12, (rowForward 489 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_489 : code 489 < code 490 := by
  decide +kernel

private theorem row_image_490 (p : Fin 12) :
    (rows 490).val p = rowForward 490 p := by
  calc
    (rows 490).val p = rowPoint 490 p := (rowPoint_eq 490 p).symm
    _ = rowForward 490 p := by fin_cases p <;> decide +kernel

private theorem transition_check_490 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 490) (generatorPermutation s p) =
      generatorPermutation s (rowForward 490 p) := by
  decide +kernel

private theorem code_encoding_490 :
    code 490 = ∑ p : Fin 12, (rowForward 490 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_490 : code 490 < code 491 := by
  decide +kernel

private theorem row_image_491 (p : Fin 12) :
    (rows 491).val p = rowForward 491 p := by
  calc
    (rows 491).val p = rowPoint 491 p := (rowPoint_eq 491 p).symm
    _ = rowForward 491 p := by fin_cases p <;> decide +kernel

private theorem transition_check_491 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 491) (generatorPermutation s p) =
      generatorPermutation s (rowForward 491 p) := by
  decide +kernel

private theorem code_encoding_491 :
    code 491 = ∑ p : Fin 12, (rowForward 491 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_491 : code 491 < code 492 := by
  decide +kernel

private theorem row_image_492 (p : Fin 12) :
    (rows 492).val p = rowForward 492 p := by
  calc
    (rows 492).val p = rowPoint 492 p := (rowPoint_eq 492 p).symm
    _ = rowForward 492 p := by fin_cases p <;> decide +kernel

private theorem transition_check_492 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 492) (generatorPermutation s p) =
      generatorPermutation s (rowForward 492 p) := by
  decide +kernel

private theorem code_encoding_492 :
    code 492 = ∑ p : Fin 12, (rowForward 492 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_492 : code 492 < code 493 := by
  decide +kernel

private theorem row_image_493 (p : Fin 12) :
    (rows 493).val p = rowForward 493 p := by
  calc
    (rows 493).val p = rowPoint 493 p := (rowPoint_eq 493 p).symm
    _ = rowForward 493 p := by fin_cases p <;> decide +kernel

private theorem transition_check_493 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 493) (generatorPermutation s p) =
      generatorPermutation s (rowForward 493 p) := by
  decide +kernel

private theorem code_encoding_493 :
    code 493 = ∑ p : Fin 12, (rowForward 493 p).val * 2^(4*p.val) := by
  decide +kernel

private theorem code_adjacent_493 : code 493 < code 494 := by
  decide +kernel

private theorem row_image_494 (p : Fin 12) :
    (rows 494).val p = rowForward 494 p := by
  calc
    (rows 494).val p = rowPoint 494 p := (rowPoint_eq 494 p).symm
    _ = rowForward 494 p := by fin_cases p <;> decide +kernel

private theorem transition_check_494 : ∀ (s : Fin 4) (p : Fin 12),
    rowForward (nextIndex s 494) (generatorPermutation s p) =
      generatorPermutation s (rowForward 494 p) := by
  decide +kernel

private theorem code_encoding_494 :
    code 494 = ∑ p : Fin 12, (rowForward 494 p).val * 2^(4*p.val) := by
  decide +kernel

theorem row_image (i : Fin 15) (p : Fin 12) :
    (rows (blockIndex i)).val p = rowForward (blockIndex i) p := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨0,by omega⟩ : Fin 15) = (480 : Fin 495) from rfl))
      (row_image_480 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨1,by omega⟩ : Fin 15) = (481 : Fin 495) from rfl))
      (row_image_481 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨2,by omega⟩ : Fin 15) = (482 : Fin 495) from rfl))
      (row_image_482 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨3,by omega⟩ : Fin 15) = (483 : Fin 495) from rfl))
      (row_image_483 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨4,by omega⟩ : Fin 15) = (484 : Fin 495) from rfl))
      (row_image_484 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨5,by omega⟩ : Fin 15) = (485 : Fin 495) from rfl))
      (row_image_485 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨6,by omega⟩ : Fin 15) = (486 : Fin 495) from rfl))
      (row_image_486 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨7,by omega⟩ : Fin 15) = (487 : Fin 495) from rfl))
      (row_image_487 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨8,by omega⟩ : Fin 15) = (488 : Fin 495) from rfl))
      (row_image_488 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨9,by omega⟩ : Fin 15) = (489 : Fin 495) from rfl))
      (row_image_489 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨10,by omega⟩ : Fin 15) = (490 : Fin 495) from rfl))
      (row_image_490 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨11,by omega⟩ : Fin 15) = (491 : Fin 495) from rfl))
      (row_image_491 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨12,by omega⟩ : Fin 15) = (492 : Fin 495) from rfl))
      (row_image_492 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨13,by omega⟩ : Fin 15) = (493 : Fin 495) from rfl))
      (row_image_493 p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => (rows j).val p = rowForward j p)
        (show blockIndex (⟨14,by omega⟩ : Fin 15) = (494 : Fin 495) from rfl))
      (row_image_494 p)

theorem transition_check (s : Fin 4) (i : Fin 15) (p : Fin 12) :
    rowForward (nextIndex s (blockIndex i)) (generatorPermutation s p) =
      generatorPermutation s (rowForward (blockIndex i) p) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨0,by omega⟩ : Fin 15) = (480 : Fin 495) from rfl))
      (transition_check_480 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨1,by omega⟩ : Fin 15) = (481 : Fin 495) from rfl))
      (transition_check_481 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨2,by omega⟩ : Fin 15) = (482 : Fin 495) from rfl))
      (transition_check_482 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨3,by omega⟩ : Fin 15) = (483 : Fin 495) from rfl))
      (transition_check_483 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨4,by omega⟩ : Fin 15) = (484 : Fin 495) from rfl))
      (transition_check_484 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨5,by omega⟩ : Fin 15) = (485 : Fin 495) from rfl))
      (transition_check_485 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨6,by omega⟩ : Fin 15) = (486 : Fin 495) from rfl))
      (transition_check_486 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨7,by omega⟩ : Fin 15) = (487 : Fin 495) from rfl))
      (transition_check_487 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨8,by omega⟩ : Fin 15) = (488 : Fin 495) from rfl))
      (transition_check_488 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨9,by omega⟩ : Fin 15) = (489 : Fin 495) from rfl))
      (transition_check_489 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨10,by omega⟩ : Fin 15) = (490 : Fin 495) from rfl))
      (transition_check_490 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨11,by omega⟩ : Fin 15) = (491 : Fin 495) from rfl))
      (transition_check_491 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨12,by omega⟩ : Fin 15) = (492 : Fin 495) from rfl))
      (transition_check_492 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨13,by omega⟩ : Fin 15) = (493 : Fin 495) from rfl))
      (transition_check_493 s p)
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => rowForward (nextIndex s j) (generatorPermutation s p) = generatorPermutation s (rowForward j p))
        (show blockIndex (⟨14,by omega⟩ : Fin 15) = (494 : Fin 495) from rfl))
      (transition_check_494 s p)

theorem code_encoding (i : Fin 15) :
    code (blockIndex i) = ∑ p : Fin 12, (rowForward (blockIndex i) p).val * 2^(4*p.val) := by
  fin_cases i <;> dsimp only
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨0,by omega⟩ : Fin 15) = (480 : Fin 495) from rfl))
      code_encoding_480
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨1,by omega⟩ : Fin 15) = (481 : Fin 495) from rfl))
      code_encoding_481
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨2,by omega⟩ : Fin 15) = (482 : Fin 495) from rfl))
      code_encoding_482
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨3,by omega⟩ : Fin 15) = (483 : Fin 495) from rfl))
      code_encoding_483
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨4,by omega⟩ : Fin 15) = (484 : Fin 495) from rfl))
      code_encoding_484
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨5,by omega⟩ : Fin 15) = (485 : Fin 495) from rfl))
      code_encoding_485
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨6,by omega⟩ : Fin 15) = (486 : Fin 495) from rfl))
      code_encoding_486
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨7,by omega⟩ : Fin 15) = (487 : Fin 495) from rfl))
      code_encoding_487
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨8,by omega⟩ : Fin 15) = (488 : Fin 495) from rfl))
      code_encoding_488
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨9,by omega⟩ : Fin 15) = (489 : Fin 495) from rfl))
      code_encoding_489
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨10,by omega⟩ : Fin 15) = (490 : Fin 495) from rfl))
      code_encoding_490
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨11,by omega⟩ : Fin 15) = (491 : Fin 495) from rfl))
      code_encoding_491
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨12,by omega⟩ : Fin 15) = (492 : Fin 495) from rfl))
      code_encoding_492
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨13,by omega⟩ : Fin 15) = (493 : Fin 495) from rfl))
      code_encoding_493
  · exact Eq.mpr
      (congrArg (fun j : Fin 495 => code j = ∑ p : Fin 12, (rowForward j p).val * 2^(4*p.val))
        (show blockIndex (⟨14,by omega⟩ : Fin 15) = (494 : Fin 495) from rfl))
      code_encoding_494

theorem code_adjacent (i : Fin 15) :
    ∀ h : (blockIndex i).val+1 < 495,
      code (blockIndex i) < code ⟨(blockIndex i).val+1,h⟩ := by
  fin_cases i <;> dsimp only
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨0,by omega⟩ : Fin 15) = (480 : Fin 495) from rfl))
    intro h
    exact code_adjacent_480
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨1,by omega⟩ : Fin 15) = (481 : Fin 495) from rfl))
    intro h
    exact code_adjacent_481
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨2,by omega⟩ : Fin 15) = (482 : Fin 495) from rfl))
    intro h
    exact code_adjacent_482
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨3,by omega⟩ : Fin 15) = (483 : Fin 495) from rfl))
    intro h
    exact code_adjacent_483
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨4,by omega⟩ : Fin 15) = (484 : Fin 495) from rfl))
    intro h
    exact code_adjacent_484
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨5,by omega⟩ : Fin 15) = (485 : Fin 495) from rfl))
    intro h
    exact code_adjacent_485
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨6,by omega⟩ : Fin 15) = (486 : Fin 495) from rfl))
    intro h
    exact code_adjacent_486
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨7,by omega⟩ : Fin 15) = (487 : Fin 495) from rfl))
    intro h
    exact code_adjacent_487
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨8,by omega⟩ : Fin 15) = (488 : Fin 495) from rfl))
    intro h
    exact code_adjacent_488
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨9,by omega⟩ : Fin 15) = (489 : Fin 495) from rfl))
    intro h
    exact code_adjacent_489
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨10,by omega⟩ : Fin 15) = (490 : Fin 495) from rfl))
    intro h
    exact code_adjacent_490
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨11,by omega⟩ : Fin 15) = (491 : Fin 495) from rfl))
    intro h
    exact code_adjacent_491
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨12,by omega⟩ : Fin 15) = (492 : Fin 495) from rfl))
    intro h
    exact code_adjacent_492
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨13,by omega⟩ : Fin 15) = (493 : Fin 495) from rfl))
    intro h
    exact code_adjacent_493
  · apply Eq.mpr
      (congrArg (fun j : Fin 495 => ∀ h : j.val+1 < 495, code j < code ⟨j.val+1,h⟩)
        (show blockIndex (⟨14,by omega⟩ : Fin 15) = (494 : Fin 495) from rfl))
    intro h
    omega

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSelectedInvolutionOrbitBlock15
