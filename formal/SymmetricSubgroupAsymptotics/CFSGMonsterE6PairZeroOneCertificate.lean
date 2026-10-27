import SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords

/-! ONE selected remaining literal Monster E6 relation; root data are not proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroOneCertificate
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding
open CFSGMonsterE6SelectedReflectionWords

def start0 : List (Fin 8) := [5, 1, 0, 1, 5, 2, 5, 1, 0, 1, 5, 2, 5, 1, 0, 1, 5, 2]

def trace0 : List (Step (Fin 8)) := [
  { kind := .commute, prefixWord := [5, 1, 0, 1], suffixWord := [5, 1, 0, 1, 5, 2, 5, 1, 0, 1, 5, 2], i := 5, j := 2 },
  { kind := .cancel, prefixWord := [5, 1, 0, 1, 2], suffixWord := [1, 0, 1, 5, 2, 5, 1, 0, 1, 5, 2], i := 5, j := 5 },
  { kind := .commute, prefixWord := [5, 1, 0, 1, 2, 1, 0, 1], suffixWord := [5, 1, 0, 1, 5, 2], i := 5, j := 2 },
  { kind := .cancel, prefixWord := [5, 1, 0, 1, 2, 1, 0, 1, 2], suffixWord := [1, 0, 1, 5, 2], i := 5, j := 5 },
  { kind := .braid, prefixWord := [5], suffixWord := [2, 1, 0, 1, 2, 1, 0, 1, 5, 2], i := 1, j := 0 },
  { kind := .commute, prefixWord := [5, 0, 1], suffixWord := [1, 0, 1, 2, 1, 0, 1, 5, 2], i := 0, j := 2 },
  { kind := .braid, prefixWord := [5, 0, 1, 2], suffixWord := [1, 2, 1, 0, 1, 5, 2], i := 0, j := 1 },
  { kind := .cancel, prefixWord := [5, 0, 1, 2, 1, 0], suffixWord := [2, 1, 0, 1, 5, 2], i := 1, j := 1 },
  { kind := .braid, prefixWord := [5, 0], suffixWord := [0, 2, 1, 0, 1, 5, 2], i := 1, j := 2 },
  { kind := .commute, prefixWord := [5, 0, 2, 1], suffixWord := [2, 1, 0, 1, 5, 2], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [5, 0, 2, 1, 0], suffixWord := [1, 0, 1, 5, 2], i := 2, j := 2 },
  { kind := .braid, prefixWord := [5, 0, 2], suffixWord := [0, 1, 5, 2], i := 1, j := 0 },
  { kind := .cancel, prefixWord := [5, 0, 2, 0, 1], suffixWord := [1, 5, 2], i := 0, j := 0 },
  { kind := .cancel, prefixWord := [5, 0, 2, 0], suffixWord := [5, 2], i := 1, j := 1 },
  { kind := .commute, prefixWord := [5], suffixWord := [0, 5, 2], i := 0, j := 2 },
  { kind := .cancel, prefixWord := [5, 2], suffixWord := [5, 2], i := 0, j := 0 },
  { kind := .commute, prefixWord := [], suffixWord := [5, 2], i := 5, j := 2 },
  { kind := .cancel, prefixWord := [2], suffixWord := [2], i := 5, j := 5 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 2, j := 2 }
]

def start1 : List (Fin 8) := []

theorem certificate0 : checkTo adjacent start0 trace0 start1=true := by decide +kernel

theorem chunk0 : value generator start0=value generator start1 :=
  checkTo_sound adjacent generator CFSGMonsterE8BraidBinding.generator_square
    generator_commute generator_braid start0 trace0 start1 certificate0

theorem selected_identity : value generator start0=1 := by
  calc
    value generator start0=value generator start1 := chunk0
    _=1 := rfl

theorem source_binding : start0=(word 0++word 1)++(word 0++word 1)++(word 0++word 1) := rfl

theorem pair_period : (reflection 0*reflection 1)^3=1 := by
  have hh := selected_identity
  rw [source_binding] at hh
  simpa only [reflection,value_append,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh

end SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroOneCertificate
