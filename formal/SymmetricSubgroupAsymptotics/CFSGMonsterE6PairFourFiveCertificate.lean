import SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords

/-! ONE selected remaining literal Monster E6 relation; root data are not proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6PairFourFiveCertificate
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding
open CFSGMonsterE6SelectedReflectionWords

def start0 : List (Fin 8) := [7, 5, 0, 5, 7, 7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 7, 5, 0, 5, 7, 7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7]

def trace0 : List (Step (Fin 8)) := [
  { kind := .cancel, prefixWord := [7, 5, 0, 5], suffixWord := [4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 7, 5, 0, 5, 7, 7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7], i := 7, j := 7 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4], suffixWord := [5, 0, 5, 7, 7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7], i := 7, j := 7 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 0, 5], suffixWord := [4, 3, 2, 1, 0, 1, 2, 3, 4, 7], i := 7, j := 7 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 3], suffixWord := [0, 5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7], i := 4, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 3, 5], suffixWord := [5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7], i := 4, j := 0 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 3, 5, 0], suffixWord := [4, 3, 2, 1, 0, 1, 2, 3, 4, 7], i := 4, j := 5 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 3, 5, 0, 5], suffixWord := [3, 2, 1, 0, 1, 2, 3, 4, 7], i := 4, j := 4 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2], suffixWord := [0, 5, 3, 2, 1, 0, 1, 2, 3, 4, 7], i := 3, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 5], suffixWord := [5, 3, 2, 1, 0, 1, 2, 3, 4, 7], i := 3, j := 0 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 5, 0], suffixWord := [3, 2, 1, 0, 1, 2, 3, 4, 7], i := 3, j := 5 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 2, 1, 0, 1, 2, 5, 0, 5], suffixWord := [2, 1, 0, 1, 2, 3, 4, 7], i := 3, j := 3 },
  { kind := .braid, prefixWord := [7, 5, 0, 5, 4, 3, 2], suffixWord := [2, 5, 0, 5, 2, 1, 0, 1, 2, 3, 4, 7], i := 1, j := 0 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 1], suffixWord := [5, 0, 5, 2, 1, 0, 1, 2, 3, 4, 7], i := 0, j := 2 },
  { kind := .braid, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 1, 2], suffixWord := [5, 2, 1, 0, 1, 2, 3, 4, 7], i := 0, j := 5 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 1, 2, 5, 0], suffixWord := [2, 1, 0, 1, 2, 3, 4, 7], i := 5, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 1], suffixWord := [0, 2, 1, 0, 1, 2, 3, 4, 7], i := 2, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 1, 5], suffixWord := [2, 1, 0, 1, 2, 3, 4, 7], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 1, 5, 0], suffixWord := [1, 0, 1, 2, 3, 4, 7], i := 2, j := 2 },
  { kind := .braid, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 1, 5], suffixWord := [1, 2, 3, 4, 7], i := 0, j := 1 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 1, 5, 1, 0], suffixWord := [2, 3, 4, 7], i := 1, j := 1 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0], suffixWord := [1, 0, 2, 3, 4, 7], i := 1, j := 5 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 2, 0, 5], suffixWord := [0, 2, 3, 4, 7], i := 1, j := 1 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3], suffixWord := [5, 0, 2, 3, 4, 7], i := 2, j := 0 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 0], suffixWord := [0, 2, 3, 4, 7], i := 2, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 5, 4, 3, 0, 5], suffixWord := [2, 3, 4, 7], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [7, 5, 0, 5, 4, 3, 0, 5, 0], suffixWord := [3, 4, 7], i := 2, j := 2 },
  { kind := .braid, prefixWord := [7], suffixWord := [4, 3, 0, 5, 0, 3, 4, 7], i := 5, j := 0 },
  { kind := .commute, prefixWord := [7, 0, 5], suffixWord := [3, 0, 5, 0, 3, 4, 7], i := 0, j := 4 },
  { kind := .commute, prefixWord := [7, 0, 5, 4], suffixWord := [0, 5, 0, 3, 4, 7], i := 0, j := 3 },
  { kind := .cancel, prefixWord := [7, 0, 5, 4, 3], suffixWord := [5, 0, 3, 4, 7], i := 0, j := 0 },
  { kind := .commute, prefixWord := [7, 0], suffixWord := [3, 5, 0, 3, 4, 7], i := 5, j := 4 },
  { kind := .commute, prefixWord := [7, 0, 4], suffixWord := [5, 0, 3, 4, 7], i := 5, j := 3 }
]

def start1 : List (Fin 8) := [7, 0, 4, 3, 5, 5, 0, 3, 4, 7]

theorem certificate0 : checkTo adjacent start0 trace0 start1=true := by decide +kernel

theorem chunk0 : value generator start0=value generator start1 :=
  checkTo_sound adjacent generator CFSGMonsterE8BraidBinding.generator_square
    generator_commute generator_braid start0 trace0 start1 certificate0

def trace1 : List (Step (Fin 8)) := [
  { kind := .cancel, prefixWord := [7, 0, 4, 3], suffixWord := [0, 3, 4, 7], i := 5, j := 5 },
  { kind := .commute, prefixWord := [7, 0, 4], suffixWord := [3, 4, 7], i := 3, j := 0 },
  { kind := .cancel, prefixWord := [7, 0, 4, 0], suffixWord := [4, 7], i := 3, j := 3 },
  { kind := .commute, prefixWord := [7], suffixWord := [0, 4, 7], i := 0, j := 4 },
  { kind := .cancel, prefixWord := [7, 4], suffixWord := [4, 7], i := 0, j := 0 },
  { kind := .cancel, prefixWord := [7], suffixWord := [7], i := 4, j := 4 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 7, j := 7 }
]

def start2 : List (Fin 8) := []

theorem certificate1 : checkTo adjacent start1 trace1 start2=true := by decide +kernel

theorem chunk1 : value generator start1=value generator start2 :=
  checkTo_sound adjacent generator CFSGMonsterE8BraidBinding.generator_square
    generator_commute generator_braid start1 trace1 start2 certificate1

theorem selected_identity : value generator start0=1 := by
  calc
    value generator start0=value generator start1 := chunk0
    _=value generator start2 := chunk1
    _=1 := rfl

theorem source_binding : start0=(word 4++word 5)++(word 4++word 5) := rfl

theorem pair_period : (reflection 4*reflection 5)^2=1 := by
  have hh := selected_identity
  rw [source_binding] at hh
  simpa only [reflection,value_append,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh

end SymmetricSubgroupAsymptotics.CFSGMonsterE6PairFourFiveCertificate
