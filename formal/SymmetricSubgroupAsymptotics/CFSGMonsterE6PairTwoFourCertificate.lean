import SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords

/-! ONE selected remaining literal Monster E6 relation; root data are not proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6PairTwoFourCertificate
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding
open CFSGMonsterE6SelectedReflectionWords

def start0 : List (Fin 8) := [3, 7, 5, 0, 5, 7, 3, 7, 5, 0, 5, 7]

def trace0 : List (Step (Fin 8)) := [
  { kind := .commute, prefixWord := [3, 7, 5, 0, 5], suffixWord := [7, 5, 0, 5, 7], i := 7, j := 3 },
  { kind := .cancel, prefixWord := [3, 7, 5, 0, 5, 3], suffixWord := [5, 0, 5, 7], i := 7, j := 7 },
  { kind := .commute, prefixWord := [3, 7, 5, 0], suffixWord := [5, 0, 5, 7], i := 5, j := 3 },
  { kind := .cancel, prefixWord := [3, 7, 5, 0, 3], suffixWord := [0, 5, 7], i := 5, j := 5 },
  { kind := .commute, prefixWord := [3, 7, 5], suffixWord := [0, 5, 7], i := 0, j := 3 },
  { kind := .cancel, prefixWord := [3, 7, 5, 3], suffixWord := [5, 7], i := 0, j := 0 },
  { kind := .commute, prefixWord := [3, 7], suffixWord := [5, 7], i := 5, j := 3 },
  { kind := .cancel, prefixWord := [3, 7, 3], suffixWord := [7], i := 5, j := 5 },
  { kind := .commute, prefixWord := [], suffixWord := [3, 7], i := 3, j := 7 },
  { kind := .cancel, prefixWord := [7], suffixWord := [7], i := 3, j := 3 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 7, j := 7 }
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

theorem source_binding : start0=(word 2++word 4)++(word 2++word 4) := rfl

theorem pair_period : (reflection 2*reflection 4)^2=1 := by
  have hh := selected_identity
  rw [source_binding] at hh
  simpa only [reflection,value_append,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh

end SymmetricSubgroupAsymptotics.CFSGMonsterE6PairTwoFourCertificate
