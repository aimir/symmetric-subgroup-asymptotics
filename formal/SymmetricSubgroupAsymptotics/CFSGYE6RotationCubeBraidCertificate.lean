import SymmetricSubgroupAsymptotics.CFSGYE6RotationFirstConjugationBraidPilot

/-! ONE actual rotation identity from literal braid moves only. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6RotationCubeBraidCertificate
open CFSG.Models.YGroups InvolutionBraidTrace CFSGYE6SelectedWords
open CFSGYE6RotationFirstConjugationBraidPilot (rotationWord)

def start0 : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4]

def trace0 : List (Step (Fin 6)) := [
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3], suffixWord := [1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0], suffixWord := [4, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5], suffixWord := [3, 4, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1], suffixWord := [0, 3, 4, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 3], suffixWord := [0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0], suffixWord := [4, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3], suffixWord := [3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3], suffixWord := [1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0], suffixWord := [4, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5], suffixWord := [3, 4, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1], suffixWord := [0, 3, 4, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 3], suffixWord := [0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0], suffixWord := [4, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3], suffixWord := [3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1], suffixWord := [0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3], suffixWord := [1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0], suffixWord := [5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2], suffixWord := [0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5], suffixWord := [3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1], suffixWord := [4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0], suffixWord := [4, 5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 4 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3], suffixWord := [5, 0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4], suffixWord := [0, 1, 2, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 3, 0, 1], suffixWord := [0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 3, 0], suffixWord := [2, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 3, 0, 3, 1], suffixWord := [1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5], suffixWord := [1, 0, 2, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 0, 3], suffixWord := [2, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 0], suffixWord := [0, 1, 2, 1, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 1 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 0, 1, 3, 0], suffixWord := [2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 0, 1, 3], suffixWord := [1, 2, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 0, 1], suffixWord := [0, 1, 2, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 2 }
]

def start1 : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 2, 2, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4]

theorem certificate0 : checkTo adjacent start0 trace0 start1 = true := by
  decide +kernel

theorem chunk0 (arms : Arms) : eval arms start0 = eval arms start1 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate0

def trace1 : List (Step (Fin 6)) := [
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1], suffixWord := [5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0], suffixWord := [0, 1, 2, 5, 0, 1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3], suffixWord := [2, 5, 0, 1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 0], suffixWord := [0, 1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 0, 5], suffixWord := [1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1], suffixWord := [2, 1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 5, 0], suffixWord := [1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 5], suffixWord := [5, 1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1], suffixWord := [0, 5, 1, 3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0], suffixWord := [3, 0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1], suffixWord := [0, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 5], suffixWord := [5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3], suffixWord := [0, 5, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 4], suffixWord := [0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3], suffixWord := [5, 0, 0, 1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 5], suffixWord := [1, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4], suffixWord := [2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0], suffixWord := [5, 2, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 4], suffixWord := [3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1], suffixWord := [5, 3, 0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4], suffixWord := [0, 1, 5, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 5, 0], suffixWord := [0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3], suffixWord := [1, 0, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 5], suffixWord := [1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0], suffixWord := [0, 1, 1, 3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 1, 5, 0], suffixWord := [3, 0, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 1 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 1, 5], suffixWord := [4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 1], suffixWord := [0, 3, 4, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 1, 3, 5, 0], suffixWord := [4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 1, 3, 5], suffixWord := [3, 4, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 1, 3], suffixWord := [0, 3, 4, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 4 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 1, 3, 4, 5, 0, 3], suffixWord := [5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 4 }
]

def start2 : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4]

theorem certificate1 : checkTo adjacent start1 trace1 start2 = true := by
  decide +kernel

theorem chunk1 (arms : Arms) : eval arms start1 = eval arms start2 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate1

def trace2 : List (Step (Fin 6)) := [
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0], suffixWord := [0, 1, 2, 4, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 3], suffixWord := [2, 4, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 3, 0, 1], suffixWord := [4, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 3, 0, 1, 2], suffixWord := [3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 3, 0, 1, 2, 4], suffixWord := [1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 3, 0, 1, 2, 4, 3, 0], suffixWord := [3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 3, 0, 1, 2, 5, 0, 3, 0, 1, 2, 4, 3, 0, 1], suffixWord := [4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5], suffixWord := [1, 2, 5, 0, 3, 0, 1, 2, 4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4], suffixWord := [0, 3, 1, 2, 5, 0, 3, 0, 1, 2, 4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0], suffixWord := [2, 5, 0, 3, 0, 1, 2, 4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1], suffixWord := [5, 0, 3, 0, 1, 2, 4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2], suffixWord := [0, 3, 0, 1, 2, 4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2, 5], suffixWord := [0, 1, 2, 4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2, 5, 0, 3], suffixWord := [1, 2, 4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2, 5, 0], suffixWord := [2, 4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2, 5, 0, 1], suffixWord := [4, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 2 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2], suffixWord := [0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2, 5, 0, 1], suffixWord := [3, 4, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2, 5, 0], suffixWord := [2, 3, 4, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2, 5], suffixWord := [1, 2, 3, 4, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1, 2], suffixWord := [0, 1, 2, 3, 4, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0, 1], suffixWord := [5, 0, 1, 2, 3, 4, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 2, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5, 0], suffixWord := [2, 5, 0, 1, 2, 3, 4, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 1, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 5], suffixWord := [1, 2, 5, 0, 1, 2, 3, 4, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3], suffixWord := [0, 1, 2, 5, 0, 1, 2, 3, 4, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 4, 5, 0, 1, 2, 5, 0, 1, 2, 3], suffixWord := [1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 3, 4, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0], suffixWord := [4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 3, 4, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1], suffixWord := [5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0], suffixWord := [4, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 4 },
  { kind := .cancel, prefixWord := [2, 1, 0, 4, 3], suffixWord := [5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 4, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 5, 0], suffixWord := [0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1], suffixWord := [3, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 0 }
]

def start3 : List (Fin 6) := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 0, 5, 0, 3, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4]

theorem certificate2 : checkTo adjacent start2 trace2 start3 = true := by
  decide +kernel

theorem chunk2 (arms : Arms) : eval arms start2 = eval arms start3 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate2

def trace3 : List (Step (Fin 6)) := [
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 0, 5], suffixWord := [1, 2, 3, 0, 1, 5, 0, 3, 4], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 0], suffixWord := [0, 3, 1, 2, 3, 0, 1, 5, 0, 3, 4], i := 5, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 0, 3, 5, 0], suffixWord := [2, 3, 0, 1, 5, 0, 3, 4], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 0, 3, 5, 0, 1], suffixWord := [3, 0, 1, 5, 0, 3, 4], i := 3, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 0, 3, 5, 0, 1, 2], suffixWord := [0, 1, 5, 0, 3, 4], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 0, 3, 5, 0, 1], suffixWord := [1, 5, 0, 3, 4], i := 2, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1], suffixWord := [0, 1, 2, 3, 0, 1, 0, 3, 5, 0, 1, 0, 2, 1, 5, 0, 3, 4], i := 2, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5], suffixWord := [1, 2, 3, 0, 1, 0, 3, 5, 0, 1, 0, 2, 1, 5, 0, 3, 4], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0], suffixWord := [3, 0, 1, 0, 3, 5, 0, 1, 0, 2, 1, 5, 0, 3, 4], i := 2, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 2], suffixWord := [0, 1, 0, 3, 5, 0, 1, 0, 2, 1, 5, 0, 3, 4], i := 1, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 2, 3], suffixWord := [0, 3, 5, 0, 1, 0, 2, 1, 5, 0, 3, 4], i := 1, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 2, 3, 0, 1], suffixWord := [3, 5, 0, 1, 0, 2, 1, 5, 0, 3, 4], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 2, 3, 0], suffixWord := [5, 0, 1, 0, 2, 1, 5, 0, 3, 4], i := 1, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 2, 3, 0, 3], suffixWord := [0, 1, 0, 2, 1, 5, 0, 3, 4], i := 1, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 2, 3, 0, 3, 5], suffixWord := [0, 2, 1, 5, 0, 3, 4], i := 1, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1], suffixWord := [2, 1, 5, 0, 3, 4], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1], suffixWord := [0, 3, 5, 0, 1, 2, 1, 5, 0, 3, 4], i := 2, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 3], suffixWord := [3, 5, 0, 1, 2, 1, 5, 0, 3, 4], i := 2, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 3, 0], suffixWord := [5, 0, 1, 2, 1, 5, 0, 3, 4], i := 2, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 3, 0, 3], suffixWord := [0, 1, 2, 1, 5, 0, 3, 4], i := 2, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 3, 0, 3, 5], suffixWord := [1, 2, 1, 5, 0, 3, 4], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 3, 0, 3, 5, 0], suffixWord := [1, 5, 0, 3, 4], i := 2, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 4, 3, 5, 0, 1, 5, 0, 1, 3, 0, 3, 5, 0, 1, 2], suffixWord := [5, 0, 3, 4], i := 1, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 5, 0], suffixWord := [0, 1, 3, 0, 3, 5, 0, 1, 2, 5, 0, 3, 4], i := 1, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3], suffixWord := [1, 0, 1, 3, 0, 3, 5, 0, 1, 2, 5, 0, 3, 4], i := 5, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3, 0, 5], suffixWord := [1, 3, 0, 3, 5, 0, 1, 2, 5, 0, 3, 4], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 0], suffixWord := [0, 1, 1, 3, 0, 3, 5, 0, 1, 2, 5, 0, 3, 4], i := 5, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 4, 3, 0, 1, 5, 0], suffixWord := [3, 0, 3, 5, 0, 1, 2, 5, 0, 3, 4], i := 1, j := 1 },
  { kind := .braid, prefixWord := [2, 1, 0, 4, 3, 0, 1, 5], suffixWord := [3, 5, 0, 1, 2, 5, 0, 3, 4], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 4, 3, 0, 1], suffixWord := [0, 3, 3, 5, 0, 1, 2, 5, 0, 3, 4], i := 5, j := 3 },
  { kind := .cancel, prefixWord := [2, 1, 0, 4, 3, 0, 1, 3, 5, 0], suffixWord := [5, 0, 1, 2, 5, 0, 3, 4], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1], suffixWord := [3, 0, 1, 3, 5, 0, 5, 0, 1, 2, 5, 0, 3, 4], i := 0, j := 4 }
]

def start4 : List (Fin 6) := [2, 1, 4, 0, 3, 0, 1, 3, 5, 0, 5, 0, 1, 2, 5, 0, 3, 4]

theorem certificate3 : checkTo adjacent start3 trace3 start4 = true := by
  decide +kernel

theorem chunk3 (arms : Arms) : eval arms start3 = eval arms start4 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate3

def trace4 : List (Step (Fin 6)) := [
  { kind := .braid, prefixWord := [2, 1, 4], suffixWord := [1, 3, 5, 0, 5, 0, 1, 2, 5, 0, 3, 4], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 4, 3, 0], suffixWord := [3, 5, 0, 5, 0, 1, 2, 5, 0, 3, 4], i := 3, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 4, 3, 0, 1], suffixWord := [5, 0, 5, 0, 1, 2, 5, 0, 3, 4], i := 3, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 4, 3, 0, 1], suffixWord := [0, 1, 2, 5, 0, 3, 4], i := 5, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 4, 3, 0, 1, 0, 5], suffixWord := [1, 2, 5, 0, 3, 4], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 4, 3, 0, 1, 0], suffixWord := [2, 5, 0, 3, 4], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 4, 3, 0, 1, 0, 1], suffixWord := [5, 0, 3, 4], i := 5, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 4, 3, 0, 1, 0, 1, 2], suffixWord := [0, 3, 4], i := 5, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 4, 3, 0, 1, 0, 1], suffixWord := [3, 4], i := 2, j := 0 },
  { kind := .commute, prefixWord := [2], suffixWord := [3, 0, 1, 0, 1, 0, 2, 3, 4], i := 1, j := 4 },
  { kind := .commute, prefixWord := [2, 4], suffixWord := [0, 1, 0, 1, 0, 2, 3, 4], i := 1, j := 3 },
  { kind := .braid, prefixWord := [2, 4, 3], suffixWord := [0, 1, 0, 2, 3, 4], i := 1, j := 0 },
  { kind := .cancel, prefixWord := [2, 4, 3, 0, 1], suffixWord := [1, 0, 2, 3, 4], i := 0, j := 0 },
  { kind := .cancel, prefixWord := [2, 4, 3, 0], suffixWord := [0, 2, 3, 4], i := 1, j := 1 },
  { kind := .commute, prefixWord := [2, 4, 3, 0], suffixWord := [3, 4], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 4, 3], suffixWord := [0, 3, 4], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 4], suffixWord := [0, 0, 3, 4], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2], suffixWord := [3, 0, 0, 3, 4], i := 4, j := 2 },
  { kind := .cancel, prefixWord := [], suffixWord := [4, 3, 0, 0, 3, 4], i := 2, j := 2 },
  { kind := .cancel, prefixWord := [4, 3], suffixWord := [3, 4], i := 0, j := 0 },
  { kind := .cancel, prefixWord := [4], suffixWord := [4], i := 3, j := 3 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 4, j := 4 }
]

def start5 : List (Fin 6) := []

theorem certificate4 : checkTo adjacent start4 trace4 start5 = true := by
  decide +kernel

theorem chunk4 (arms : Arms) : eval arms start4 = eval arms start5 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate4

theorem selected_identity (arms : Arms) : eval arms start0 = 1 := by
  calc
    eval arms start0 = eval arms start1 := chunk0 arms
    _ = eval arms start2 := chunk1 arms
    _ = eval arms start3 := chunk2 arms
    _ = eval arms start4 := chunk3 arms
    _ = eval arms start5 := chunk4 arms
    _ = 1 := rfl

theorem source_word : start0 =
    rotationWord ++ rotationWord ++ rotationWord := rfl

theorem actual_cube (arms : Arms) : eval arms rotationWord ^ 3 = 1 := by
  have h := selected_identity arms
  rw [source_word] at h
  change value (generator arms)
    (rotationWord ++ rotationWord ++ rotationWord) = 1 at h
  rw [value_append,value_append] at h
  simpa only [eval,pow_succ,pow_zero,mul_one,mul_assoc] using h

end SymmetricSubgroupAsymptotics.CFSGYE6RotationCubeBraidCertificate
