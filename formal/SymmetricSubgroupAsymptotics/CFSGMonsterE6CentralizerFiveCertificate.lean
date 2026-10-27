import SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords

/-! ONE selected remaining literal Monster E6 relation; root data are not proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerFiveCertificate
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding
open CFSGMonsterE6SelectedReflectionWords

def start0 : List (Fin 8) := [7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 0, 7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 0]

def trace0 : List (Step (Fin 8)) := [
  { kind := .commute, prefixWord := [7, 4, 3, 2, 1, 0, 1, 2, 3], suffixWord := [0, 7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 4, j := 7 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 1, 0, 1, 2, 3, 7], suffixWord := [7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 4, j := 0 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 1, 0, 1, 2, 3, 7, 0], suffixWord := [4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 4, j := 7 },
  { kind := .cancel, prefixWord := [7, 4, 3, 2, 1, 0, 1, 2, 3, 7, 0, 7], suffixWord := [3, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 4, j := 4 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 1, 0, 1, 2], suffixWord := [0, 7, 3, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 3, j := 7 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 1, 0, 1, 2, 7], suffixWord := [7, 3, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 3, j := 0 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 1, 0, 1, 2, 7, 0], suffixWord := [3, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 3, j := 7 },
  { kind := .cancel, prefixWord := [7, 4, 3, 2, 1, 0, 1, 2, 7, 0, 7], suffixWord := [2, 1, 0, 1, 2, 3, 4, 7, 0], i := 3, j := 3 },
  { kind := .braid, prefixWord := [7, 4, 3, 2], suffixWord := [2, 7, 0, 7, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 1, j := 0 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 0, 1], suffixWord := [7, 0, 7, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 0, j := 2 },
  { kind := .braid, prefixWord := [7, 4, 3, 2, 0, 1, 2], suffixWord := [7, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 0, j := 7 },
  { kind := .cancel, prefixWord := [7, 4, 3, 2, 0, 1, 2, 7, 0], suffixWord := [2, 1, 0, 1, 2, 3, 4, 7, 0], i := 7, j := 7 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 0, 1], suffixWord := [0, 2, 1, 0, 1, 2, 3, 4, 7, 0], i := 2, j := 7 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 0, 1, 7], suffixWord := [2, 1, 0, 1, 2, 3, 4, 7, 0], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [7, 4, 3, 2, 0, 1, 7, 0], suffixWord := [1, 0, 1, 2, 3, 4, 7, 0], i := 2, j := 2 },
  { kind := .braid, prefixWord := [7, 4, 3, 2, 0, 1, 7], suffixWord := [1, 2, 3, 4, 7, 0], i := 0, j := 1 },
  { kind := .cancel, prefixWord := [7, 4, 3, 2, 0, 1, 7, 1, 0], suffixWord := [2, 3, 4, 7, 0], i := 1, j := 1 },
  { kind := .commute, prefixWord := [7, 4, 3, 2, 0], suffixWord := [1, 0, 2, 3, 4, 7, 0], i := 1, j := 7 },
  { kind := .cancel, prefixWord := [7, 4, 3, 2, 0, 7], suffixWord := [0, 2, 3, 4, 7, 0], i := 1, j := 1 },
  { kind := .commute, prefixWord := [7, 4, 3], suffixWord := [7, 0, 2, 3, 4, 7, 0], i := 2, j := 0 },
  { kind := .commute, prefixWord := [7, 4, 3, 0], suffixWord := [0, 2, 3, 4, 7, 0], i := 2, j := 7 },
  { kind := .commute, prefixWord := [7, 4, 3, 0, 7], suffixWord := [2, 3, 4, 7, 0], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [7, 4, 3, 0, 7, 0], suffixWord := [3, 4, 7, 0], i := 2, j := 2 },
  { kind := .commute, prefixWord := [], suffixWord := [3, 0, 7, 0, 3, 4, 7, 0], i := 7, j := 4 },
  { kind := .commute, prefixWord := [4], suffixWord := [0, 7, 0, 3, 4, 7, 0], i := 7, j := 3 },
  { kind := .braid, prefixWord := [4, 3], suffixWord := [0, 3, 4, 7, 0], i := 7, j := 0 },
  { kind := .cancel, prefixWord := [4, 3, 0, 7], suffixWord := [3, 4, 7, 0], i := 0, j := 0 },
  { kind := .commute, prefixWord := [4], suffixWord := [7, 3, 4, 7, 0], i := 3, j := 0 },
  { kind := .commute, prefixWord := [4, 0], suffixWord := [3, 4, 7, 0], i := 3, j := 7 },
  { kind := .cancel, prefixWord := [4, 0, 7], suffixWord := [4, 7, 0], i := 3, j := 3 },
  { kind := .commute, prefixWord := [4, 0], suffixWord := [7, 0], i := 7, j := 4 },
  { kind := .cancel, prefixWord := [4, 0, 4], suffixWord := [0], i := 7, j := 7 }
]

def start1 : List (Fin 8) := [4, 0, 4, 0]

theorem certificate0 : checkTo adjacent start0 trace0 start1=true := by decide +kernel

theorem chunk0 : value generator start0=value generator start1 :=
  checkTo_sound adjacent generator CFSGMonsterE8BraidBinding.generator_square
    generator_commute generator_braid start0 trace0 start1 certificate0

def trace1 : List (Step (Fin 8)) := [
  { kind := .commute, prefixWord := [], suffixWord := [4, 0], i := 4, j := 0 },
  { kind := .cancel, prefixWord := [0], suffixWord := [0], i := 4, j := 4 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 0, j := 0 }
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

theorem source_binding : start0=word 5++[0]++word 5++[0] := rfl

theorem selected_conjugacy : reflection 5*generator 0*reflection 5=generator 0 := by
  have hh := selected_identity
  rw [source_binding] at hh
  have he : (reflection 5*generator 0*reflection 5)*generator 0=1 := by
    simpa only [reflection,value_append,value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hi : (generator 0)⁻¹=generator 0 := inv_eq_of_mul_eq_one_right (CFSGMonsterE8BraidBinding.generator_square 0)
  apply mul_inv_eq_one.mp
  rw [hi]
  exact he

theorem selected_mem_centralizer : reflection 5∈nodeCentralizer := by
  change reflection 5∈Subgroup.centralizer {generator 0}
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hh := congrArg (fun z : Bimonster => z*reflection 5) selected_conjugacy
  simpa only [mul_assoc,CFSGMonsterE6SelectedReflectionWords.reflection_square,mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGMonsterE6CentralizerFiveCertificate
