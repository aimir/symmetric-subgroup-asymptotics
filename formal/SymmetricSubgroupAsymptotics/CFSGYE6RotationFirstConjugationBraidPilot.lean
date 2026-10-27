import SymmetricSubgroupAsymptotics.CFSGYE6SelectedWords

/-! ONE actual rotation conjugation from literal braid moves only. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6RotationFirstConjugationBraidPilot
open CFSG.Models.YGroups InvolutionBraidTrace CFSGYE6SelectedWords

def rotationWord : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4]

def start0 : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 1, 2, 4, 3, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3]

def trace0 : List (Step (Fin 6)) := [
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3], suffixWord := [2, 4, 3, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 1], suffixWord := [4, 3, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 4, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 1, 2], suffixWord := [3, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 4, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0], suffixWord := [2, 3, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1], suffixWord := [3, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 3, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 2], suffixWord := [0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0], suffixWord := [0, 1, 2, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 1, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 5], suffixWord := [2, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 1, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 5, 0, 1], suffixWord := [0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 0, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 5, 0, 1, 2], suffixWord := [5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 0, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3], suffixWord := [1, 2, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 0, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 5, 0], suffixWord := [2, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 5, 0, 1], suffixWord := [5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 5, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 5, 0, 1, 2], suffixWord := [1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 5, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 5, 0], suffixWord := [0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 1, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 5, 0, 2, 1], suffixWord := [3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 2, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 5, 0, 2, 1, 0], suffixWord := [2, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 2, j := 3 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 5, 0, 2, 1, 0, 3], suffixWord := [1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 2, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1], suffixWord := [5, 0, 2, 1, 0, 3, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 2, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3], suffixWord := [0, 2, 1, 0, 3, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 2, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 5], suffixWord := [2, 1, 0, 3, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 5, 0], suffixWord := [1, 0, 3, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 2, j := 2 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 5], suffixWord := [3, 1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 5, 1, 0], suffixWord := [1, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 1, j := 3 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 5, 1, 0, 3], suffixWord := [0, 5, 4, 3, 0, 1, 2, 4, 3], i := 1, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0], suffixWord := [5, 1, 0, 3, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 1, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3], suffixWord := [1, 0, 3, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 1, j := 5 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 5], suffixWord := [0, 3, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 1, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0], suffixWord := [0, 3, 0, 5, 4, 3, 0, 1, 2, 4, 3], i := 3, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 5], suffixWord := [0, 5, 4, 3, 0, 1, 2, 4, 3], i := 3, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 5, 0, 3], suffixWord := [5, 4, 3, 0, 1, 2, 4, 3], i := 0, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4], suffixWord := [0, 3, 5, 4, 3, 0, 1, 2, 4, 3], i := 5, j := 0 }
]

def start1 : List (Fin 6) := [2, 1, 0, 3, 4, 0, 5, 0, 0, 3, 5, 4, 3, 0, 1, 2, 4, 3]

theorem certificate0 : checkTo adjacent start0 trace0 start1 = true := by
  decide +kernel

theorem chunk0 (arms : Arms) : eval arms start0 = eval arms start1 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate0

def trace1 : List (Step (Fin 6)) := [
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 0, 5], suffixWord := [3, 5, 4, 3, 0, 1, 2, 4, 3], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 0], suffixWord := [5, 4, 3, 0, 1, 2, 4, 3], i := 5, j := 3 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 0, 3], suffixWord := [4, 3, 0, 1, 2, 4, 3], i := 5, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3], suffixWord := [3, 4, 3, 0, 1, 2, 4, 3], i := 4, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 0], suffixWord := [3, 0, 1, 2, 4, 3], i := 4, j := 3 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 0, 3, 4], suffixWord := [0, 1, 2, 4, 3], i := 3, j := 3 },
  { kind := .braid, prefixWord := [2, 1], suffixWord := [3, 4, 0, 1, 2, 4, 3], i := 0, j := 3 },
  { kind := .cancel, prefixWord := [2, 1, 3, 0], suffixWord := [4, 0, 1, 2, 4, 3], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 3], suffixWord := [0, 1, 2, 4, 3], i := 0, j := 4 },
  { kind := .cancel, prefixWord := [2, 1, 3, 4], suffixWord := [1, 2, 4, 3], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2], suffixWord := [4, 1, 2, 4, 3], i := 1, j := 3 },
  { kind := .commute, prefixWord := [2, 3], suffixWord := [1, 2, 4, 3], i := 1, j := 4 },
  { kind := .cancel, prefixWord := [2, 3, 4], suffixWord := [2, 4, 3], i := 1, j := 1 },
  { kind := .commute, prefixWord := [2, 3], suffixWord := [4, 3], i := 4, j := 2 },
  { kind := .cancel, prefixWord := [2, 3, 2], suffixWord := [3], i := 4, j := 4 },
  { kind := .commute, prefixWord := [], suffixWord := [2, 3], i := 2, j := 3 },
  { kind := .cancel, prefixWord := [3], suffixWord := [3], i := 2, j := 2 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 3, j := 3 }
]

def start2 : List (Fin 6) := []

theorem certificate1 : checkTo adjacent start1 trace1 start2 = true := by
  decide +kernel

theorem chunk1 (arms : Arms) : eval arms start1 = eval arms start2 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate1

theorem selected_identity (arms : Arms) : eval arms start0 = 1 := by
  calc
    eval arms start0 = eval arms start1 := chunk0 arms
    _ = eval arms start2 := chunk1 arms
    _ = 1 := rfl

theorem source_word : start0 =
    rotationWord ++ wordA ++ rotationWord.reverse ++ wordB.reverse := rfl

theorem actual_conjugation (arms : Arms) :
    eval arms rotationWord * eval arms wordA * (eval arms rotationWord)⁻¹ =
      eval arms wordB := by
  have h := selected_identity arms
  rw [source_word] at h
  change value (generator arms)
    (rotationWord ++ wordA ++ rotationWord.reverse ++ wordB.reverse) = 1 at h
  rw [value_append,value_append,value_append,
    value_reverse (generator arms) (generator_square arms) rotationWord,
    value_reverse (generator arms) (generator_square arms) wordB] at h
  have hh : (eval arms rotationWord * eval arms wordA *
      (eval arms rotationWord)⁻¹) * (eval arms wordB)⁻¹ = 1 := by
    simpa only [eval,mul_assoc] using h
  exact mul_inv_eq_one.mp hh

end SymmetricSubgroupAsymptotics.CFSGYE6RotationFirstConjugationBraidPilot
