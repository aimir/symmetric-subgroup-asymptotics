import SymmetricSubgroupAsymptotics.CFSGYE6SelectedWords

/-! ONE selected literal E6 braid trace. No root-image inference. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6SecondConjugationBraidPilot
open CFSG.Models.YGroups InvolutionBraidTrace CFSGYE6SelectedWords

def start0 : List (Fin 6) := [0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 3]

def trace0 : List (Step (Fin 6)) := [
  { kind := .commute, prefixWord := [0, 1, 2, 3, 4, 0, 1, 3, 0], suffixWord := [5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 3], i := 5, j := 2 },
  { kind := .cancel, prefixWord := [0, 1, 2, 3, 4, 0, 1, 3, 0, 2], suffixWord := [0, 3, 1, 0, 4, 3, 2, 1, 0, 3], i := 5, j := 5 },
  { kind := .commute, prefixWord := [0, 1, 2, 3, 4, 0, 1, 3], suffixWord := [0, 3, 1, 0, 4, 3, 2, 1, 0, 3], i := 0, j := 2 },
  { kind := .cancel, prefixWord := [0, 1, 2, 3, 4, 0, 1, 3, 2], suffixWord := [3, 1, 0, 4, 3, 2, 1, 0, 3], i := 0, j := 0 },
  { kind := .commute, prefixWord := [0, 1, 2, 3, 4, 0, 1], suffixWord := [3, 1, 0, 4, 3, 2, 1, 0, 3], i := 3, j := 2 },
  { kind := .cancel, prefixWord := [0, 1, 2, 3, 4, 0, 1, 2], suffixWord := [1, 0, 4, 3, 2, 1, 0, 3], i := 3, j := 3 },
  { kind := .commute, prefixWord := [0, 1], suffixWord := [4, 0, 1, 2, 1, 0, 4, 3, 2, 1, 0, 3], i := 2, j := 3 },
  { kind := .commute, prefixWord := [0, 1, 3], suffixWord := [0, 1, 2, 1, 0, 4, 3, 2, 1, 0, 3], i := 2, j := 4 },
  { kind := .commute, prefixWord := [0, 1, 3, 4], suffixWord := [1, 2, 1, 0, 4, 3, 2, 1, 0, 3], i := 2, j := 0 },
  { kind := .braid, prefixWord := [0, 1, 3, 4, 0], suffixWord := [1, 0, 4, 3, 2, 1, 0, 3], i := 2, j := 1 },
  { kind := .cancel, prefixWord := [0, 1, 3, 4, 0, 1, 2], suffixWord := [0, 4, 3, 2, 1, 0, 3], i := 1, j := 1 },
  { kind := .commute, prefixWord := [0, 1, 3, 4, 0, 1], suffixWord := [4, 3, 2, 1, 0, 3], i := 2, j := 0 },
  { kind := .commute, prefixWord := [0, 1, 3, 4, 0, 1, 0], suffixWord := [3, 2, 1, 0, 3], i := 2, j := 4 },
  { kind := .commute, prefixWord := [0, 1, 3, 4, 0, 1, 0, 4], suffixWord := [2, 1, 0, 3], i := 2, j := 3 },
  { kind := .cancel, prefixWord := [0, 1, 3, 4, 0, 1, 0, 4, 3], suffixWord := [1, 0, 3], i := 2, j := 2 },
  { kind := .commute, prefixWord := [0], suffixWord := [4, 0, 1, 0, 4, 3, 1, 0, 3], i := 1, j := 3 },
  { kind := .commute, prefixWord := [0, 3], suffixWord := [0, 1, 0, 4, 3, 1, 0, 3], i := 1, j := 4 },
  { kind := .braid, prefixWord := [0, 3, 4], suffixWord := [0, 4, 3, 1, 0, 3], i := 1, j := 0 },
  { kind := .cancel, prefixWord := [0, 3, 4, 0, 1], suffixWord := [4, 3, 1, 0, 3], i := 0, j := 0 },
  { kind := .commute, prefixWord := [0, 3], suffixWord := [1, 4, 3, 1, 0, 3], i := 4, j := 0 },
  { kind := .commute, prefixWord := [0, 3, 0], suffixWord := [4, 3, 1, 0, 3], i := 4, j := 1 },
  { kind := .cancel, prefixWord := [0, 3, 0, 1], suffixWord := [3, 1, 0, 3], i := 4, j := 4 },
  { kind := .commute, prefixWord := [0, 3, 0], suffixWord := [1, 0, 3], i := 1, j := 3 },
  { kind := .cancel, prefixWord := [0, 3, 0, 3], suffixWord := [0, 3], i := 1, j := 1 },
  { kind := .braid, prefixWord := [], suffixWord := [3, 0, 3], i := 0, j := 3 },
  { kind := .cancel, prefixWord := [3, 0], suffixWord := [0, 3], i := 3, j := 3 },
  { kind := .cancel, prefixWord := [3], suffixWord := [3], i := 0, j := 0 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 3, j := 3 }
]

def start1 : List (Fin 6) := []

theorem certificate0 : checkTo adjacent start0 trace0 start1 = true := by
  decide +kernel

theorem chunk0 (arms : Arms) : eval arms start0 = eval arms start1 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate0

theorem selected_identity (arms : Arms) : eval arms start0 = 1 := by
  calc
    eval arms start0 = eval arms start1 := chunk0 arms
    _ = 1 := rfl

theorem source_word : start0 = guideW.reverse ++ [2] ++ guideW ++ [3] := rfl

end SymmetricSubgroupAsymptotics.CFSGYE6SecondConjugationBraidPilot
