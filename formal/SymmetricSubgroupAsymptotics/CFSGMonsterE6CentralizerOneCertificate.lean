import SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords

/-! ONE selected remaining literal Monster E6 relation; root data are not proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerOneCertificate
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding
open CFSGMonsterE6SelectedReflectionWords

def start0 : List (Fin 8) := [2, 0, 2, 0]

def trace0 : List (Step (Fin 8)) := [
  { kind := .commute, prefixWord := [], suffixWord := [2, 0], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [0], suffixWord := [0], i := 2, j := 2 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 0, j := 0 }
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

theorem source_binding : start0=word 1++[0]++word 1++[0] := rfl

theorem selected_conjugacy : reflection 1*generator 0*reflection 1=generator 0 := by
  have hh := selected_identity
  rw [source_binding] at hh
  have he : (reflection 1*generator 0*reflection 1)*generator 0=1 := by
    simpa only [reflection,value_append,value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hi : (generator 0)⁻¹=generator 0 := inv_eq_of_mul_eq_one_right (CFSGMonsterE8BraidBinding.generator_square 0)
  apply mul_inv_eq_one.mp
  rw [hi]
  exact he

theorem selected_mem_centralizer : reflection 1∈nodeCentralizer := by
  change reflection 1∈Subgroup.centralizer {generator 0}
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hh := congrArg (fun z : Bimonster => z*reflection 1) selected_conjugacy
  simpa only [mul_assoc,CFSGMonsterE6SelectedReflectionWords.reflection_square,mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerOneCertificate
