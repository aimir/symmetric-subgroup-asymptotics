import SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords

/-! Fixed common-conjugator proof of pair05. No root fact is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroFiveCertificate
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding
open CFSGMonsterE6SelectedReflectionWords

def conjugatorWord : List (Fin 8) := [7, 5, 0, 1, 2, 3, 4, 1, 5]
def t : Bimonster := value generator conjugatorWord

def leftStart0 : List (Fin 8) := [7, 5, 0, 1, 2, 3, 4, 1, 5, 5, 1, 0, 1, 5, 5, 1, 4, 3, 2, 1, 0, 5, 7, 1]

def leftTrace0 : List (Step (Fin 8)) := [
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 2, 3, 4, 1], suffixWord := [1, 0, 1, 5, 5, 1, 4, 3, 2, 1, 0, 5, 7, 1], i := 5, j := 5 },
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 2, 3, 4], suffixWord := [0, 1, 5, 5, 1, 4, 3, 2, 1, 0, 5, 7, 1], i := 1, j := 1 },
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 2, 3, 4, 0, 1], suffixWord := [1, 4, 3, 2, 1, 0, 5, 7, 1], i := 5, j := 5 },
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 2, 3, 4, 0], suffixWord := [4, 3, 2, 1, 0, 5, 7, 1], i := 1, j := 1 },
  { kind := .commute, prefixWord := [7, 5, 0, 1, 2, 3], suffixWord := [4, 3, 2, 1, 0, 5, 7, 1], i := 4, j := 0 },
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 2, 3, 0], suffixWord := [3, 2, 1, 0, 5, 7, 1], i := 4, j := 4 },
  { kind := .commute, prefixWord := [7, 5, 0, 1, 2], suffixWord := [3, 2, 1, 0, 5, 7, 1], i := 3, j := 0 },
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 2, 0], suffixWord := [2, 1, 0, 5, 7, 1], i := 3, j := 3 },
  { kind := .commute, prefixWord := [7, 5, 0, 1], suffixWord := [2, 1, 0, 5, 7, 1], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 0], suffixWord := [1, 0, 5, 7, 1], i := 2, j := 2 },
  { kind := .braid, prefixWord := [7, 5], suffixWord := [1, 0, 5, 7, 1], i := 0, j := 1 },
  { kind := .cancel, prefixWord := [7, 5, 1, 0], suffixWord := [0, 5, 7, 1], i := 1, j := 1 },
  { kind := .cancel, prefixWord := [7, 5, 1], suffixWord := [5, 7, 1], i := 0, j := 0 },
  { kind := .commute, prefixWord := [7], suffixWord := [5, 7, 1], i := 5, j := 1 },
  { kind := .cancel, prefixWord := [7, 1], suffixWord := [7, 1], i := 5, j := 5 },
  { kind := .commute, prefixWord := [], suffixWord := [7, 1], i := 7, j := 1 },
  { kind := .cancel, prefixWord := [1], suffixWord := [1], i := 7, j := 7 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 1, j := 1 }
]
def leftStart1 : List (Fin 8) := []
theorem leftCertificate0 : checkTo adjacent leftStart0 leftTrace0 leftStart1=true := by decide +kernel
theorem leftChunk0 : value generator leftStart0=value generator leftStart1 :=
  checkTo_sound adjacent generator CFSGMonsterE8BraidBinding.generator_square
    generator_commute generator_braid leftStart0 leftTrace0 leftStart1 leftCertificate0

theorem left_identity : value generator leftStart0=1 := by
  calc
    value generator leftStart0=value generator leftStart1 := leftChunk0
    _=1 := rfl

theorem left_source_word : leftStart0=conjugatorWord++word 0++conjugatorWord.reverse++[1] := rfl

theorem left_conjugacy : t*reflection 0*t⁻¹=generator 1 := by
  have hh := left_identity
  rw [left_source_word] at hh
  rw [value_append,value_append,value_append,
    value_reverse generator CFSGMonsterE8BraidBinding.generator_square] at hh
  have hsingle : value generator [1]=generator 1 := rfl
  rw [hsingle] at hh
  have he : (t*reflection 0*t⁻¹)*generator 1=1 := hh
  have hi : (generator 1)⁻¹=generator 1 :=
    inv_eq_of_mul_eq_one_right (CFSGMonsterE8BraidBinding.generator_square 1)
  apply mul_inv_eq_one.mp
  rw [hi]
  exact he

def rightStart0 : List (Fin 8) := [7, 5, 0, 1, 2, 3, 4, 1, 5, 7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0]

def rightTrace0 : List (Step (Fin 8)) := [
  { kind := .commute, prefixWord := [7, 5, 0, 1, 2, 3], suffixWord := [5, 7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 4, j := 1 },
  { kind := .commute, prefixWord := [7, 5, 0, 1, 2, 3, 1], suffixWord := [7, 4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 4, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 1, 2, 3, 1, 5], suffixWord := [4, 3, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 4, j := 7 },
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 2, 3, 1, 5, 7], suffixWord := [3, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 4, j := 4 },
  { kind := .commute, prefixWord := [7, 5, 0, 1, 2], suffixWord := [5, 7, 3, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 3, j := 1 },
  { kind := .commute, prefixWord := [7, 5, 0, 1, 2, 1], suffixWord := [7, 3, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 3, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 1, 2, 1, 5], suffixWord := [3, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 3, j := 7 },
  { kind := .cancel, prefixWord := [7, 5, 0, 1, 2, 1, 5, 7], suffixWord := [2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 3, j := 3 },
  { kind := .braid, prefixWord := [7, 5, 0], suffixWord := [5, 7, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 1, j := 2 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 1], suffixWord := [7, 2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 2, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 1, 5], suffixWord := [2, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 2, j := 7 },
  { kind := .cancel, prefixWord := [7, 5, 0, 2, 1, 5, 7], suffixWord := [1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 2, j := 2 },
  { kind := .commute, prefixWord := [7, 5, 0, 2], suffixWord := [7, 1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 1, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5], suffixWord := [1, 0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 1, j := 7 },
  { kind := .cancel, prefixWord := [7, 5, 0, 2, 5, 7], suffixWord := [0, 1, 2, 3, 4, 7, 5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 1, j := 1 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 2, 3], suffixWord := [5, 1, 4, 3, 2, 1, 0, 5, 7, 0], i := 4, j := 7 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 2, 3, 7], suffixWord := [1, 4, 3, 2, 1, 0, 5, 7, 0], i := 4, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 2, 3, 7, 5], suffixWord := [4, 3, 2, 1, 0, 5, 7, 0], i := 4, j := 1 },
  { kind := .cancel, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 2, 3, 7, 5, 1], suffixWord := [3, 2, 1, 0, 5, 7, 0], i := 4, j := 4 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 2], suffixWord := [5, 1, 3, 2, 1, 0, 5, 7, 0], i := 3, j := 7 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 2, 7], suffixWord := [1, 3, 2, 1, 0, 5, 7, 0], i := 3, j := 5 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 2, 7, 5], suffixWord := [3, 2, 1, 0, 5, 7, 0], i := 3, j := 1 },
  { kind := .cancel, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 2, 7, 5, 1], suffixWord := [2, 1, 0, 5, 7, 0], i := 3, j := 3 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1], suffixWord := [5, 1, 2, 1, 0, 5, 7, 0], i := 2, j := 7 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 7], suffixWord := [1, 2, 1, 0, 5, 7, 0], i := 2, j := 5 },
  { kind := .braid, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 7, 5], suffixWord := [1, 0, 5, 7, 0], i := 2, j := 1 },
  { kind := .cancel, prefixWord := [7, 5, 0, 2, 5, 7, 0, 1, 7, 5, 1, 2], suffixWord := [0, 5, 7, 0], i := 1, j := 1 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0], suffixWord := [5, 1, 2, 0, 5, 7, 0], i := 1, j := 7 },
  { kind := .commute, prefixWord := [7, 5, 0, 2, 5, 7, 0, 7], suffixWord := [1, 2, 0, 5, 7, 0], i := 1, j := 5 },
  { kind := .cancel, prefixWord := [7, 5, 0, 2, 5, 7, 0, 7, 5], suffixWord := [2, 0, 5, 7, 0], i := 1, j := 1 },
  { kind := .commute, prefixWord := [7, 5], suffixWord := [5, 7, 0, 7, 5, 2, 0, 5, 7, 0], i := 0, j := 2 },
  { kind := .commute, prefixWord := [7], suffixWord := [0, 5, 7, 0, 7, 5, 2, 0, 5, 7, 0], i := 5, j := 2 }
]
def rightStart1 : List (Fin 8) := [7, 2, 5, 0, 5, 7, 0, 7, 5, 2, 0, 5, 7, 0]
theorem rightCertificate0 : checkTo adjacent rightStart0 rightTrace0 rightStart1=true := by decide +kernel
theorem rightChunk0 : value generator rightStart0=value generator rightStart1 :=
  checkTo_sound adjacent generator CFSGMonsterE8BraidBinding.generator_square
    generator_commute generator_braid rightStart0 rightTrace0 rightStart1 rightCertificate0

def rightTrace1 : List (Step (Fin 8)) := [
  { kind := .braid, prefixWord := [7, 2], suffixWord := [7, 0, 7, 5, 2, 0, 5, 7, 0], i := 5, j := 0 },
  { kind := .braid, prefixWord := [7, 2, 0, 5], suffixWord := [7, 5, 2, 0, 5, 7, 0], i := 0, j := 7 },
  { kind := .cancel, prefixWord := [7, 2, 0, 5, 7, 0], suffixWord := [5, 2, 0, 5, 7, 0], i := 7, j := 7 },
  { kind := .commute, prefixWord := [7, 2, 0], suffixWord := [0, 5, 2, 0, 5, 7, 0], i := 5, j := 7 },
  { kind := .braid, prefixWord := [7, 2, 0, 7], suffixWord := [2, 0, 5, 7, 0], i := 5, j := 0 },
  { kind := .commute, prefixWord := [7, 2, 0, 7, 0, 5], suffixWord := [0, 5, 7, 0], i := 0, j := 2 },
  { kind := .cancel, prefixWord := [7, 2, 0, 7, 0, 5, 2], suffixWord := [5, 7, 0], i := 0, j := 0 },
  { kind := .commute, prefixWord := [7, 2, 0, 7, 0], suffixWord := [5, 7, 0], i := 5, j := 2 },
  { kind := .cancel, prefixWord := [7, 2, 0, 7, 0, 2], suffixWord := [7, 0], i := 5, j := 5 },
  { kind := .commute, prefixWord := [], suffixWord := [0, 7, 0, 2, 7, 0], i := 7, j := 2 },
  { kind := .braid, prefixWord := [2], suffixWord := [0, 2, 7, 0], i := 7, j := 0 },
  { kind := .cancel, prefixWord := [2, 0, 7], suffixWord := [2, 7, 0], i := 0, j := 0 },
  { kind := .commute, prefixWord := [2, 0], suffixWord := [7, 0], i := 7, j := 2 },
  { kind := .cancel, prefixWord := [2, 0, 2], suffixWord := [0], i := 7, j := 7 },
  { kind := .commute, prefixWord := [], suffixWord := [2, 0], i := 2, j := 0 },
  { kind := .cancel, prefixWord := [0], suffixWord := [0], i := 2, j := 2 },
  { kind := .cancel, prefixWord := [], suffixWord := [], i := 0, j := 0 }
]
def rightStart2 : List (Fin 8) := []
theorem rightCertificate1 : checkTo adjacent rightStart1 rightTrace1 rightStart2=true := by decide +kernel
theorem rightChunk1 : value generator rightStart1=value generator rightStart2 :=
  checkTo_sound adjacent generator CFSGMonsterE8BraidBinding.generator_square
    generator_commute generator_braid rightStart1 rightTrace1 rightStart2 rightCertificate1

theorem right_identity : value generator rightStart0=1 := by
  calc
    value generator rightStart0=value generator rightStart1 := rightChunk0
    _=value generator rightStart2 := rightChunk1
    _=1 := rfl

theorem right_source_word : rightStart0=conjugatorWord++word 5++conjugatorWord.reverse++[0] := rfl

theorem right_conjugacy : t*reflection 5*t⁻¹=generator 0 := by
  have hh := right_identity
  rw [right_source_word] at hh
  rw [value_append,value_append,value_append,
    value_reverse generator CFSGMonsterE8BraidBinding.generator_square] at hh
  have hsingle : value generator [0]=generator 0 := rfl
  rw [hsingle] at hh
  have he : (t*reflection 5*t⁻¹)*generator 0=1 := hh
  have hi : (generator 0)⁻¹=generator 0 :=
    inv_eq_of_mul_eq_one_right (CFSGMonsterE8BraidBinding.generator_square 0)
  apply mul_inv_eq_one.mp
  rw [hi]
  exact he

theorem pair_period : (reflection 0*reflection 5)^3=1 := by
  have he : t*(reflection 0*reflection 5)*t⁻¹=generator 1*generator 0 := by
    rw [←left_conjugacy,←right_conjugacy]
    group
  have hp : ((MulAut.conj t) (reflection 0*reflection 5))^3=1 := by
    change (t*(reflection 0*reflection 5)*t⁻¹)^3=1
    rw [he]
    exact CFSGMonsterSelectedDerivedInvolution.adjacent_cube (node 1) (node 0)
      ((adjacent_node 1 0).mp rfl)
  apply (MulAut.conj t).injective
  rw [map_pow,map_one]
  exact hp

end SymmetricSubgroupAsymptotics.CFSGMonsterE6PairZeroFiveCertificate
