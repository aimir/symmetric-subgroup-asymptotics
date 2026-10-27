import SymmetricSubgroupAsymptotics.CFSGMonsterE8BraidBinding

/-! ONE literal selected reflection0 centralizer certificate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterSelectedReflectionCentralizerPilot
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding

def selectedWord : List (Fin 8) := [5, 1, 0, 1, 5]
def start : List (Fin 8) := [5, 1, 0, 1, 5, 0, 5, 1, 0, 1, 5]
def trace : List (Step (Fin 8)) := [
  { kind := .braid, prefixWord := [5], suffixWord := [5, 0, 5, 1, 0, 1, 5], i := 1, j := 0 },
  { kind := .braid, prefixWord := [5, 0, 1], suffixWord := [5, 1, 0, 1, 5], i := 0, j := 5 },
  { kind := .commute, prefixWord := [5, 0], suffixWord := [0, 5, 5, 1, 0, 1, 5], i := 1, j := 5 },
  { kind := .braid, prefixWord := [], suffixWord := [1, 0, 5, 5, 1, 0, 1, 5], i := 5, j := 0 },
  { kind := .braid, prefixWord := [0, 5], suffixWord := [5, 5, 1, 0, 1, 5], i := 0, j := 1 },
  { kind := .cancel, prefixWord := [0, 5, 1, 0, 1], suffixWord := [1, 0, 1, 5], i := 5, j := 5 },
  { kind := .cancel, prefixWord := [0, 5, 1, 0], suffixWord := [0, 1, 5], i := 1, j := 1 },
  { kind := .cancel, prefixWord := [0, 5, 1], suffixWord := [1, 5], i := 0, j := 0 },
  { kind := .cancel, prefixWord := [0, 5], suffixWord := [5], i := 1, j := 1 },
  { kind := .cancel, prefixWord := [0], suffixWord := [], i := 5, j := 5 }
]

theorem source_binding : start=selectedWord++[0]++selectedWord := rfl

theorem certificate : checkTo adjacent start trace [0]=true := by decide +kernel

def selectedReflection : Bimonster := value generator selectedWord

theorem selected_square : selectedReflection*selectedReflection=1 :=
  reflection_square [5,1] 0

theorem selected_conjugacy : selectedReflection*generator 0*selectedReflection=generator 0 := by
  have hh := checkTo_sound adjacent generator generator_square generator_commute generator_braid
    start trace [0] certificate
  rw [source_binding] at hh
  simpa only [selectedReflection,value_append,value,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one] using hh

theorem selected_mem_centralizer : selectedReflection∈nodeCentralizer := by
  change selectedReflection∈Subgroup.centralizer {generator 0}
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hh := congrArg (fun z : Bimonster => z*selectedReflection) selected_conjugacy
  simpa only [mul_assoc,selected_square,mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGMonsterSelectedReflectionCentralizerPilot
