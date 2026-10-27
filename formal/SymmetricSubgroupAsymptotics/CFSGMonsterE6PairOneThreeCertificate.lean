import SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords

/-! ONE selected remaining literal Monster E6 relation; root data are not proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6PairOneThreeCertificate
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding
open CFSGMonsterE6SelectedReflectionWords

def start0 : List (Fin 8) := [2, 6, 2, 6]

def trace0 : List (Step (Fin 8)) := [
  { kind := .commute, prefixWord := [], suffixWord := [2, 6], i := 2, j := 6 },
  { kind := .cancel, prefixWord := [6], suffixWord := [6], i := 2, j := 2 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 6, j := 6 }
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

theorem source_binding : start0=(word 1++word 3)++(word 1++word 3) := rfl

theorem pair_period : (reflection 1*reflection 3)^2=1 := by
  have hh := selected_identity
  rw [source_binding] at hh
  simpa only [reflection,value_append,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh

end SymmetricSubgroupAsymptotics.CFSGMonsterE6PairOneThreeCertificate
