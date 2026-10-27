import SymmetricSubgroupAsymptotics.CFSGYE6RotationCubeBraidCertificate
import SymmetricSubgroupAsymptotics.CFSGYE6RotationFirstConjugationBraidPilot

/-! ONE actual rotation identity from literal braid moves only. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6RotationSecondConjugationBraidCertificate
open CFSG.Models.YGroups InvolutionBraidTrace CFSGYE6SelectedWords
open CFSGYE6RotationFirstConjugationBraidPilot (rotationWord)

def start0 : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 5, 1, 0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5]

def trace0 : List (Step (Fin 6)) := [
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0], suffixWord := [0, 3, 2, 1, 0, 5, 4, 3, 0, 1, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 5, 0], suffixWord := [1, 0, 5, 4, 3, 0, 1, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 5], suffixWord := [3, 1, 0, 5, 4, 3, 0, 1, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1], suffixWord := [0, 3, 1, 0, 5, 4, 3, 0, 1, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0], suffixWord := [0, 5, 4, 3, 0, 1, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0], suffixWord := [3, 0, 1, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 5, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4], suffixWord := [0, 1, 2, 5, 0, 3, 1, 0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 5, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0], suffixWord := [0, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 3, 0, 4], suffixWord := [1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 3, 0], suffixWord := [3, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 4, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 3], suffixWord := [4, 3, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1], suffixWord := [0, 4, 3, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 4], suffixWord := [0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0], suffixWord := [3, 0, 5, 0, 1, 2, 3, 4, 0, 1, 3, 0, 5, 5], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3], suffixWord := [1, 3, 0, 5, 5], i := 4, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3, 4, 4, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0], suffixWord := [3, 0, 5, 5], i := 4, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4, 3], suffixWord := [3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 5], i := 4, j := 4 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 4], suffixWord := [0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 5], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3], suffixWord := [1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 5], i := 4, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0], suffixWord := [2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 5], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1], suffixWord := [5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 5], i := 4, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 4, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], suffixWord := [], i := 5, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2], suffixWord := [0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5], suffixWord := [1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0], suffixWord := [3, 0, 4, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 4, 3], suffixWord := [3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1], suffixWord := [0, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 4], suffixWord := [5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3], suffixWord := [3, 0, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3], suffixWord := [1, 2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0], suffixWord := [2, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1], suffixWord := [5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 2 }
]

def start1 : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 5, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0]

theorem certificate0 : checkTo adjacent start0 trace0 start1 = true := by
  decide +kernel

theorem chunk0 (arms : Arms) : eval arms start0 = eval arms start1 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate0

def trace1 : List (Step (Fin 6)) := [
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2], suffixWord := [0, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1], suffixWord := [1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5], suffixWord := [2, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3], suffixWord := [0, 1, 2, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4], suffixWord := [5, 0, 1, 2, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0], suffixWord := [3, 5, 0, 1, 2, 1, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 1 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 4, 3, 5, 0], suffixWord := [2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 4, 3, 5], suffixWord := [1, 2, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 4, 3], suffixWord := [0, 1, 2, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 4], suffixWord := [5, 0, 1, 2, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1], suffixWord := [3, 5, 0, 1, 2, 2, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 3, 5, 0, 1], suffixWord := [3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 2, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4], suffixWord := [0, 1, 3, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 5, 3, 0], suffixWord := [0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 5], suffixWord := [1, 0, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 5, 0, 3], suffixWord := [1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 5, 0], suffixWord := [0, 1, 1, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 4, 5, 0, 1, 3, 0], suffixWord := [4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2], suffixWord := [0, 1, 3, 0, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 5], suffixWord := [1, 3, 0, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 5, 0], suffixWord := [3, 0, 4, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 4, 3], suffixWord := [3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1], suffixWord := [0, 3, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 4], suffixWord := [0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3], suffixWord := [3, 0, 0, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5, 0, 3, 0, 1, 2, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3], suffixWord := [5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 5], suffixWord := [1, 2, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1], suffixWord := [0, 3, 1, 2, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0], suffixWord := [2, 5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1], suffixWord := [5, 0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2], suffixWord := [0, 1, 3, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2, 5, 3, 0], suffixWord := [0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 3 }
]

def start2 : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2, 5, 3, 0, 3, 1, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0]

theorem certificate1 : checkTo adjacent start1 trace1 start2 = true := by
  decide +kernel

theorem chunk1 (arms : Arms) : eval arms start1 = eval arms start2 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate1

def trace2 : List (Step (Fin 6)) := [
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2, 5], suffixWord := [1, 0, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2, 5, 0, 3], suffixWord := [1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2, 5, 0], suffixWord := [0, 1, 1, 2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2, 5, 0, 1, 3, 0], suffixWord := [2, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2, 5, 0, 1, 3], suffixWord := [5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 1, 3, 5, 0, 1, 2, 5, 0, 1], suffixWord := [0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0], suffixWord := [5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3], suffixWord := [0, 1, 2, 5, 0, 1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5], suffixWord := [2, 5, 0, 1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 0], suffixWord := [0, 1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 2, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 0, 5], suffixWord := [1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1], suffixWord := [2, 1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 5, 0], suffixWord := [1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 5], suffixWord := [5, 1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1], suffixWord := [0, 5, 1, 2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0], suffixWord := [2, 3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0, 1], suffixWord := [3, 0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0, 1, 2], suffixWord := [0, 5, 0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3], suffixWord := [0, 1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 5], suffixWord := [1, 3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0], suffixWord := [3, 0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1], suffixWord := [0, 4, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 3, 5], suffixWord := [3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2, 3, 0, 3, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 3], suffixWord := [0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 2], suffixWord := [5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1], suffixWord := [3, 0, 5, 0, 1, 2, 5, 0, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 3], suffixWord := [1, 2, 5, 0, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 3, 5, 0], suffixWord := [2, 5, 0, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 3, 5, 0, 1], suffixWord := [5, 0, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 3, 5, 0, 1, 2], suffixWord := [0, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 3, 5, 0, 1], suffixWord := [1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 3, 5], suffixWord := [2, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 1 }
]

def start3 : List (Fin 6) := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 3, 5, 1, 0, 1, 2, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0]

theorem certificate2 : checkTo adjacent start2 trace2 start3 = true := by
  decide +kernel

theorem chunk2 (arms : Arms) : eval arms start2 = eval arms start3 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate2

def trace3 : List (Step (Fin 6)) := [
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 3], suffixWord := [0, 1, 2, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2], suffixWord := [5, 0, 1, 2, 1, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 1, 3, 5, 0], suffixWord := [2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 1, 3, 5], suffixWord := [1, 2, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 1, 3], suffixWord := [0, 1, 2, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 1], suffixWord := [5, 0, 1, 2, 2, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 3, 4, 5, 0, 1, 0, 2, 1, 2, 3, 5, 0, 1], suffixWord := [3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 2, j := 2 },
  { kind := .braid, prefixWord := [2, 1, 0, 3, 4, 5], suffixWord := [2, 1, 2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3, 4], suffixWord := [0, 1, 2, 1, 2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 3], suffixWord := [5, 0, 1, 2, 1, 2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0], suffixWord := [4, 5, 0, 1, 2, 1, 2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 3, 4, 5, 0], suffixWord := [2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 4, 5], suffixWord := [1, 2, 2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 4], suffixWord := [0, 1, 2, 2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3], suffixWord := [5, 0, 1, 2, 2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 1], suffixWord := [4, 5, 0, 1, 2, 2, 3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 2, 3, 4, 5, 0, 1], suffixWord := [3, 5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 2, j := 2 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 4, 5, 0], suffixWord := [5, 0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 4, 5, 0, 3], suffixWord := [0, 1, 3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 2, 3, 4, 5, 0, 3, 5], suffixWord := [3, 0, 1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 2, 3, 4, 5, 0, 3, 5, 0, 1], suffixWord := [1, 3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 4, 5, 0, 3, 5, 0, 1, 3, 0], suffixWord := [3, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 2, 3, 4, 5, 0, 3, 5, 0, 1, 3, 0, 1], suffixWord := [4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 4, 5, 0], suffixWord := [0, 1, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 5 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 2, 3, 4], suffixWord := [3, 0, 1, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3], suffixWord := [5, 0, 3, 0, 1, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 5], suffixWord := [1, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4], suffixWord := [0, 3, 1, 3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 5, 0], suffixWord := [3, 0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 5, 0, 1], suffixWord := [0, 1, 4, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 5, 0, 1, 0], suffixWord := [5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 5, 0, 1], suffixWord := [1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 4 }
]

def start4 : List (Fin 6) := [2, 1, 0, 1, 2, 3, 0, 4, 3, 5, 0, 1, 4, 0, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0]

theorem certificate3 : checkTo adjacent start3 trace3 start4 = true := by
  decide +kernel

theorem chunk3 (arms : Arms) : eval arms start3 = eval arms start4 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate3

def trace4 : List (Step (Fin 6)) := [
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 5, 0], suffixWord := [0, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 5], suffixWord := [1, 0, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3], suffixWord := [0, 1, 0, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 4, 5], suffixWord := [1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 4], suffixWord := [0, 1, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3], suffixWord := [5, 0, 1, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4], suffixWord := [4, 5, 0, 1, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0], suffixWord := [3, 4, 5, 0, 1, 1, 5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 4, 5, 0], suffixWord := [5, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 1, j := 1 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 4], suffixWord := [0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3], suffixWord := [5, 0, 0, 3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 4, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 0, 4, 5], suffixWord := [3, 5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 0, 4], suffixWord := [5, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 3 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 0, 4, 3], suffixWord := [0, 1, 2, 3, 0, 1, 4, 3, 0], i := 5, j := 5 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3], suffixWord := [3, 0, 1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 4], suffixWord := [1, 2, 3, 0, 1, 4, 3, 0], i := 0, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 4, 3, 0], suffixWord := [2, 3, 0, 1, 4, 3, 0], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 4, 3, 0, 1], suffixWord := [3, 0, 1, 4, 3, 0], i := 3, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 4, 3, 0, 1, 2], suffixWord := [0, 1, 4, 3, 0], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 1, 4, 3, 4, 3, 0, 1], suffixWord := [1, 4, 3, 0], i := 2, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0], suffixWord := [3, 4, 3, 0, 1, 0, 2, 1, 4, 3, 0], i := 1, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4], suffixWord := [4, 3, 0, 1, 0, 2, 1, 4, 3, 0], i := 1, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3], suffixWord := [3, 0, 1, 0, 2, 1, 4, 3, 0], i := 1, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 4], suffixWord := [0, 1, 0, 2, 1, 4, 3, 0], i := 1, j := 3 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 4, 3], suffixWord := [0, 2, 1, 4, 3, 0], i := 1, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 2, 3, 0, 4, 3, 4, 3, 0, 1], suffixWord := [2, 1, 4, 3, 0], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 1], suffixWord := [0, 4, 3, 4, 3, 0, 1, 2, 1, 4, 3, 0], i := 2, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3], suffixWord := [4, 3, 4, 3, 0, 1, 2, 1, 4, 3, 0], i := 2, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 0], suffixWord := [3, 4, 3, 0, 1, 2, 1, 4, 3, 0], i := 2, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 0, 4], suffixWord := [4, 3, 0, 1, 2, 1, 4, 3, 0], i := 2, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 0, 4, 3], suffixWord := [3, 0, 1, 2, 1, 4, 3, 0], i := 2, j := 4 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 0, 4, 3, 4], suffixWord := [0, 1, 2, 1, 4, 3, 0], i := 2, j := 3 }
]

def start5 : List (Fin 6) := [2, 1, 0, 1, 3, 0, 4, 3, 4, 3, 2, 0, 1, 2, 1, 4, 3, 0]

theorem certificate4 : checkTo adjacent start4 trace4 start5 = true := by
  decide +kernel

theorem chunk4 (arms : Arms) : eval arms start4 = eval arms start5 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate4

def trace5 : List (Step (Fin 6)) := [
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 0, 4, 3, 4, 3], suffixWord := [1, 2, 1, 4, 3, 0], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 3, 0, 4, 3, 4, 3, 0], suffixWord := [1, 4, 3, 0], i := 2, j := 1 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 3, 0, 4, 3, 4, 3, 0, 1, 2], suffixWord := [4, 3, 0], i := 1, j := 1 },
  { kind := .braid, prefixWord := [2, 1, 0, 1, 3, 0], suffixWord := [3, 0, 1, 2, 4, 3, 0], i := 4, j := 3 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 3, 0, 3, 4], suffixWord := [0, 1, 2, 4, 3, 0], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 0, 3], suffixWord := [1, 2, 4, 3, 0], i := 4, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 0, 3, 0], suffixWord := [2, 4, 3, 0], i := 4, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 3, 0, 3, 0, 1], suffixWord := [4, 3, 0], i := 4, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 3, 0, 3, 0, 1, 2], suffixWord := [3, 0], i := 4, j := 4 },
  { kind := .braid, prefixWord := [2, 1, 0, 1], suffixWord := [0, 1, 2, 3, 0], i := 3, j := 0 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 0, 3], suffixWord := [1, 2, 3, 0], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 0], suffixWord := [2, 3, 0], i := 3, j := 1 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 0, 1], suffixWord := [3, 0], i := 3, j := 2 },
  { kind := .cancel, prefixWord := [2, 1, 0, 1, 0, 1, 2], suffixWord := [0], i := 3, j := 3 },
  { kind := .commute, prefixWord := [2, 1, 0, 1, 0, 1], suffixWord := [], i := 2, j := 0 },
  { kind := .braid, prefixWord := [2], suffixWord := [0, 1, 0, 2], i := 1, j := 0 },
  { kind := .commute, prefixWord := [], suffixWord := [1, 0, 0, 1, 0, 2], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [0, 2, 1], suffixWord := [1, 0, 2], i := 0, j := 0 },
  { kind := .cancel, prefixWord := [0, 2], suffixWord := [0, 2], i := 1, j := 1 },
  { kind := .commute, prefixWord := [0], suffixWord := [2], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [], suffixWord := [2, 2], i := 0, j := 0 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 2, j := 2 }
]

def start6 : List (Fin 6) := []

theorem certificate5 : checkTo adjacent start5 trace5 start6 = true := by
  decide +kernel

theorem chunk5 (arms : Arms) : eval arms start5 = eval arms start6 :=
  checkTo_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) _ _ _ certificate5

theorem selected_identity (arms : Arms) : eval arms start0 = 1 := by
  calc
    eval arms start0 = eval arms start1 := chunk0 arms
    _ = eval arms start2 := chunk1 arms
    _ = eval arms start3 := chunk2 arms
    _ = eval arms start4 := chunk3 arms
    _ = eval arms start5 := chunk4 arms
    _ = eval arms start6 := chunk5 arms
    _ = 1 := rfl

theorem source_word : start0 =
    rotationWord ++ wordB ++ rotationWord.reverse ++ wordC.reverse := rfl

theorem actual_conjugation (arms : Arms) :
    eval arms rotationWord * eval arms wordB * (eval arms rotationWord)⁻¹ =
      eval arms wordC := by
  have h := selected_identity arms
  rw [source_word] at h
  change value (generator arms)
    (rotationWord ++ wordB ++ rotationWord.reverse ++ wordC.reverse) = 1 at h
  rw [value_append,value_append,value_append,
    value_reverse (generator arms) (generator_square arms) rotationWord,
    value_reverse (generator arms) (generator_square arms) wordC] at h
  have hh : (eval arms rotationWord * eval arms wordB *
      (eval arms rotationWord)⁻¹) * (eval arms wordC)⁻¹ = 1 := by
    simpa only [eval,mul_assoc] using h
  exact mul_inv_eq_one.mp hh

end SymmetricSubgroupAsymptotics.CFSGYE6RotationSecondConjugationBraidCertificate
