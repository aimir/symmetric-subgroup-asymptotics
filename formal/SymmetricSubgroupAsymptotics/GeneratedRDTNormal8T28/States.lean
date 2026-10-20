import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T28

/-! Exact original normal states and quotient rows for 8T28.
Selected by external selected_missing_normal_registry.py; all finite facts are checked
in Lean's kernel. This file certifies normal-state coverage, not the later
pair/character/transport acceptance of those states. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.RDTBinaryNormal8T28

abbrev Source := FiniteGroupRow 64
local instance : Group Source := BinaryMenuCayley8T28.group

def generators (j : Fin 3) : Source :=
  ⟨BinaryMenuCayley8T28.certificate.next BinaryMenuCayley8T28.certificate.identity j⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  apply binaryNormal_full_generators_of_equiv BinaryMenuCayley8T28.generators
    generators BinaryMenuCayley8T28.originalEquiv
  intro j
  change BinaryMenuCayley8T28.certificate.toCayley.elements
    (BinaryMenuCayley8T28.certificate.toCayley.next
      BinaryMenuCayley8T28.certificate.toCayley.identity j)=_
  rw [FiniteCayleyCertificate.next_eq,FiniteCayleyCertificate.identity_eq,one_mul]

theorem source_card : Nat.card Source=64 := by
  rw [Nat.card_eq_fintype_card]
  rfl

namespace N0
def normalGenerators (j : Fin 0) : Source := Fin.elim0 j
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 1) : Fin 64 := (63 : Fin 64)
private def next (i : Fin 1) (j : Fin 0) : Fin 1 := Fin.elim0 j
private def rank (i : Fin 1) : ℕ := 0
private def parents (i : Fin 1) : Fin 1 := (0 : Fin 1)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 1 where
  rows := rows
  identity := 0
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := False.elim (hi (Subsingleton.elim i (0 : Fin 1)))
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=1 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 1) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)

private def representatives (i : Fin 64) : Source := ⟨((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 58) else (if i.val < 3 then 61 else 7)) else (if i.val < 6 then (if i.val < 5 then 60 else 6) else (if i.val < 7 then 56 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 5) else (if i.val < 11 then 9 else 57)) else (if i.val < 14 then (if i.val < 13 then 55 else 3) else (if i.val < 15 then 0 else 41)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 62 else 22) else (if i.val < 19 then 18 else 21)) else (if i.val < 22 then (if i.val < 21 then 11 else 4) else (if i.val < 23 then 8 else 25))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 15) else (if i.val < 27 then 16 else 59)) else (if i.val < 30 then (if i.val < 29 then 54 else 50) else (if i.val < 31 then 49 else 47))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 1 else 40) else (if i.val < 35 then 24 else 44)) else (if i.val < 38 then (if i.val < 37 then 43 else 52) else (if i.val < 39 then 39 else 19))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 20 else 10) else (if i.val < 43 then 27 else 14)) else (if i.val < 46 then (if i.val < 45 then 13 else 48) else (if i.val < 47 then 28 else 31)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 17 else 33) else (if i.val < 51 then 26 else 38)) else (if i.val < 54 then (if i.val < 53 then 51 else 46) else (if i.val < 55 then 30 else 42))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 45 else 29) else (if i.val < 59 then 53 else 36)) else (if i.val < 62 then (if i.val < 61 then 34 else 32) else (if i.val < 63 then 35 else 37)))))) : Fin 64)⟩
private def quotientNext (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[8,9,10])) else (if i.val < 6 then (if i.val < 5 then #[11,1,12] else #[13,14,15]) else (if i.val < 7 then #[2,16,17] else #[18,19,20]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,21,22] else #[14,3,23]) else (if i.val < 11 then #[24,25,26] else #[4,27,28])) else (if i.val < 14 then (if i.val < 13 then #[29,30,31] else #[5,32,33]) else (if i.val < 15 then #[9,5,34] else #[35,36,37])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[27,6,38] else #[39,26,36]) else (if i.val < 19 then #[7,40,41] else #[26,7,42])) else (if i.val < 22 then (if i.val < 21 then #[43,44,14] else #[32,8,11]) else (if i.val < 23 then #[44,41,45] else #[46,47,18]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[10,43,48] else #[41,10,49]) else (if i.val < 27 then #[19,17,50] else #[16,11,51])) else (if i.val < 30 then (if i.val < 29 then #[52,37,25] else #[12,45,53]) else (if i.val < 31 then #[37,12,54] else #[55,56,9]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[21,13,6] else #[56,53,40]) else (if i.val < 35 then #[57,50,29] else #[15,55,58])) else (if i.val < 38 then (if i.val < 37 then #[53,15,59] else #[30,28,47]) else (if i.val < 39 then #[60,49,56] else #[17,48,55]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[48,18,27] else #[25,22,61]) else (if i.val < 43 then #[54,57,8] else #[20,24,32])) else (if i.val < 46 then (if i.val < 45 then #[22,20,30] else #[58,29,16]) else (if i.val < 47 then #[23,54,39] else #[50,23,62])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[40,39,1] else #[59,38,46]) else (if i.val < 51 then #[47,34,60] else #[62,59,44])) else (if i.val < 54 then (if i.val < 53 then #[28,58,43] else #[36,33,63]) else (if i.val < 55 then #[42,46,13] else #[31,35,21]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[33,31,19] else #[34,42,52]) else (if i.val < 59 then #[45,52,0] else #[49,51,57])) else (if i.val < 62 then (if i.val < 61 then #[38,61,35] else #[63,60,4]) else (if i.val < 63 then #[51,63,24] else #[61,62,2])))))) : Array (Fin 64))[j.val]!
private def quotientPrev (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,58] else #[0,4,48]) else (if i.val < 3 then #[6,0,63] else #[8,9,0])) else (if i.val < 6 then (if i.val < 5 then #[11,1,61] else #[13,14,1]) else (if i.val < 7 then #[2,16,32] else #[18,19,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,21,42] else #[14,3,31]) else (if i.val < 11 then #[24,25,3] else #[4,27,21])) else (if i.val < 14 then (if i.val < 13 then #[29,30,4] else #[5,32,54]) else (if i.val < 15 then #[9,5,20] else #[35,36,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[27,6,45] else #[39,26,6]) else (if i.val < 19 then #[7,40,23] else #[26,7,56])) else (if i.val < 22 then (if i.val < 21 then #[43,44,7] else #[32,8,55]) else (if i.val < 23 then #[44,41,8] else #[46,47,9]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[10,43,62] else #[41,10,28]) else (if i.val < 27 then #[19,17,10] else #[16,11,40])) else (if i.val < 30 then (if i.val < 29 then #[52,37,11] else #[12,45,34]) else (if i.val < 31 then #[37,12,44] else #[55,56,12]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[21,13,43] else #[56,53,13]) else (if i.val < 35 then #[57,50,14] else #[15,55,60])) else (if i.val < 38 then (if i.val < 37 then #[53,15,17] else #[30,28,15]) else (if i.val < 39 then #[60,49,16] else #[17,48,46]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[48,18,33] else #[25,22,18]) else (if i.val < 43 then #[54,57,19] else #[20,24,52])) else (if i.val < 46 then (if i.val < 45 then #[22,20,51] else #[58,29,22]) else (if i.val < 47 then #[23,54,49] else #[50,23,37])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[40,39,24] else #[59,38,25]) else (if i.val < 51 then #[47,34,26] else #[62,59,27])) else (if i.val < 54 then (if i.val < 53 then #[28,58,57] else #[36,33,29]) else (if i.val < 55 then #[42,46,30] else #[31,35,39]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[33,31,38] else #[34,42,59]) else (if i.val < 59 then #[45,52,35] else #[49,51,36])) else (if i.val < 62 then (if i.val < 61 then #[38,61,50] else #[63,60,41]) else (if i.val < 63 then #[51,63,47] else #[61,62,53])))))) : Array (Fin 64))[j.val]!
private def quotientParents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 3 else 4)) else (if i.val < 14 then (if i.val < 13 then 4 else 5) else (if i.val < 15 then 5 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 6) else (if i.val < 19 then 7 else 7)) else (if i.val < 22 then (if i.val < 21 then 7 else 8) else (if i.val < 23 then 8 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 10 else 10) else (if i.val < 27 then 10 else 11)) else (if i.val < 30 then (if i.val < 29 then 11 else 12) else (if i.val < 31 then 12 else 12))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 13 else 13) else (if i.val < 35 then 14 else 15)) else (if i.val < 38 then (if i.val < 37 then 15 else 15) else (if i.val < 39 then 16 else 17))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 18 else 18) else (if i.val < 43 then 19 else 20)) else (if i.val < 46 then (if i.val < 45 then 20 else 22) else (if i.val < 47 then 23 else 23)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 24 else 25) else (if i.val < 51 then 26 else 27)) else (if i.val < 54 then (if i.val < 53 then 28 else 29) else (if i.val < 55 then 30 else 31))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 31 else 34) else (if i.val < 59 then 35 else 36)) else (if i.val < 62 then (if i.val < 61 then 38 else 41) else (if i.val < 63 then 47 else 53)))))) : Fin 64)
private def quotientLetters (i : Fin 64) : Fin 3 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 1 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 2) else (if i.val < 19 then 0 else 1)) else (if i.val < 22 then (if i.val < 21 then 2 else 1) else (if i.val < 23 then 2 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 1) else (if i.val < 27 then 2 else 1)) else (if i.val < 30 then (if i.val < 29 then 2 else 0) else (if i.val < 31 then 1 else 2))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 1 else 2) else (if i.val < 35 then 2 else 0)) else (if i.val < 38 then (if i.val < 37 then 1 else 2) else (if i.val < 39 then 2 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 1 else 2) else (if i.val < 43 then 2 else 0)) else (if i.val < 46 then (if i.val < 45 then 1 else 2) else (if i.val < 47 then 0 else 1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 2 else 2) else (if i.val < 51 then 2 else 2)) else (if i.val < 54 then (if i.val < 53 then 0 else 2) else (if i.val < 55 then 2 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 1 else 0) else (if i.val < 59 then 2 else 2)) else (if i.val < 62 then (if i.val < 61 then 0 else 2) else (if i.val < 63 then 2 else 2)))))) : Fin 3)
private def stepWitness (i : Fin 64) (j : Fin 3) : Fin 1 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,0] else #[0,0,0]) else (if i.val < 3 then #[0,0,0] else #[0,0,0])) else (if i.val < 6 then (if i.val < 5 then #[0,0,0] else #[0,0,0]) else (if i.val < 7 then #[0,0,0] else #[0,0,0]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,0,0] else #[0,0,0]) else (if i.val < 11 then #[0,0,0] else #[0,0,0])) else (if i.val < 14 then (if i.val < 13 then #[0,0,0] else #[0,0,0]) else (if i.val < 15 then #[0,0,0] else #[0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[0,0,0] else #[0,0,0]) else (if i.val < 19 then #[0,0,0] else #[0,0,0])) else (if i.val < 22 then (if i.val < 21 then #[0,0,0] else #[0,0,0]) else (if i.val < 23 then #[0,0,0] else #[0,0,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[0,0,0] else #[0,0,0]) else (if i.val < 27 then #[0,0,0] else #[0,0,0])) else (if i.val < 30 then (if i.val < 29 then #[0,0,0] else #[0,0,0]) else (if i.val < 31 then #[0,0,0] else #[0,0,0]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,0,0] else #[0,0,0]) else (if i.val < 35 then #[0,0,0] else #[0,0,0])) else (if i.val < 38 then (if i.val < 37 then #[0,0,0] else #[0,0,0]) else (if i.val < 39 then #[0,0,0] else #[0,0,0]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[0,0,0] else #[0,0,0]) else (if i.val < 43 then #[0,0,0] else #[0,0,0])) else (if i.val < 46 then (if i.val < 45 then #[0,0,0] else #[0,0,0]) else (if i.val < 47 then #[0,0,0] else #[0,0,0])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[0,0,0] else #[0,0,0]) else (if i.val < 51 then #[0,0,0] else #[0,0,0])) else (if i.val < 54 then (if i.val < 53 then #[0,0,0] else #[0,0,0]) else (if i.val < 55 then #[0,0,0] else #[0,0,0]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[0,0,0] else #[0,0,0]) else (if i.val < 59 then #[0,0,0] else #[0,0,0])) else (if i.val < 62 then (if i.val < 61 then #[0,0,0] else #[0,0,0]) else (if i.val < 63 then #[0,0,0] else #[0,0,0])))))) : Array (Fin 1))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

def cosets : BinaryNormalCosetCertificate generators kernel 64 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 0⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 0
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
  parent_next := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 0
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 64
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

end N0

namespace N1
def normalGenerators (j : Fin 1) : Source := ⟨(26 : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 2) : Fin 64 := ((if i.val < 1 then 26 else 63) : Fin 64)
private def next (i : Fin 2) (j : Fin 1) : Fin 2 := ((if i.val < 1 then #[1] else #[0]) : Array (Fin 2))[j.val]!
private def rank (i : Fin 2) : ℕ := (if i.val < 1 then 1 else 0)
private def parents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 1 else 1) : Fin 2)
private def letters (i : Fin 2) : Fin 1 := ((if i.val < 1 then 0 else 0) : Fin 1)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 2 where
  rows := rows
  identity := 1
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=2 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 2) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 1) : Fin 2 := ((if i.val < 1 then #[0] else (if i.val < 2 then #[0] else #[0])) : Array (Fin 2))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 1) : Fin 2 := ((if i.val < 1 then #[0] else (if i.val < 2 then #[0] else #[0])) : Array (Fin 2))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 32) : Source := ⟨((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 58) else (if i.val < 3 then 61 else 7)) else (if i.val < 6 then (if i.val < 5 then 60 else 6) else (if i.val < 7 then 56 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 5) else (if i.val < 11 then 9 else 57)) else (if i.val < 14 then (if i.val < 13 then 55 else 3) else (if i.val < 15 then 0 else 41)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 62 else 22) else (if i.val < 19 then 21 else 11)) else (if i.val < 22 then (if i.val < 21 then 4 else 8) else (if i.val < 23 then 15 else 16))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 59 else 54) else (if i.val < 27 then 49 else 47)) else (if i.val < 30 then (if i.val < 29 then 1 else 40) else (if i.val < 31 then 43 else 52))))) : Fin 64)⟩
private def quotientNext (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[8,9,10])) else (if i.val < 6 then (if i.val < 5 then #[11,1,12] else #[13,14,15]) else (if i.val < 7 then #[2,16,17] else #[12,18,19]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,20,21] else #[14,3,4]) else (if i.val < 11 then #[15,22,23] else #[4,24,25])) else (if i.val < 14 then (if i.val < 13 then #[7,26,27] else #[5,28,29]) else (if i.val < 15 then #[9,5,2] else #[10,30,31])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[24,6,8] else #[25,23,30]) else (if i.val < 19 then #[23,7,16] else #[30,29,14])) else (if i.val < 22 then (if i.val < 21 then #[28,8,11] else #[29,27,18]) else (if i.val < 23 then #[27,10,20] else #[18,17,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[16,11,13] else #[17,31,22]) else (if i.val < 27 then #[31,12,24] else #[22,21,9])) else (if i.val < 30 then (if i.val < 29 then #[20,13,6] else #[21,19,26]) else (if i.val < 31 then #[19,15,28] else #[26,25,1]))))) : Array (Fin 32))[j.val]!
private def quotientPrev (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,23] else #[0,4,31]) else (if i.val < 3 then #[6,0,14] else #[8,9,0])) else (if i.val < 6 then (if i.val < 5 then #[11,1,9] else #[13,14,1]) else (if i.val < 7 then #[2,16,28] else #[12,18,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,20,16] else #[14,3,27]) else (if i.val < 11 then #[15,22,3] else #[4,24,20])) else (if i.val < 14 then (if i.val < 13 then #[7,26,4] else #[5,28,24]) else (if i.val < 15 then #[9,5,19] else #[10,30,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[24,6,18] else #[25,23,6]) else (if i.val < 19 then #[23,7,21] else #[30,29,7])) else (if i.val < 22 then (if i.val < 21 then #[28,8,22] else #[29,27,8]) else (if i.val < 23 then #[27,10,25] else #[18,17,10]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[16,11,26] else #[17,31,11]) else (if i.val < 27 then #[31,12,29] else #[22,21,12])) else (if i.val < 30 then (if i.val < 29 then #[20,13,30] else #[21,19,13]) else (if i.val < 31 then #[19,15,17] else #[26,25,15]))))) : Array (Fin 32))[j.val]!
private def quotientParents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 3 else 4)) else (if i.val < 14 then (if i.val < 13 then 4 else 5) else (if i.val < 15 then 5 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 6) else (if i.val < 19 then 7 else 7)) else (if i.val < 22 then (if i.val < 21 then 8 else 8) else (if i.val < 23 then 10 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 11 else 11) else (if i.val < 27 then 12 else 12)) else (if i.val < 30 then (if i.val < 29 then 13 else 13) else (if i.val < 31 then 15 else 15))))) : Fin 32)
private def quotientLetters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 1 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 2) else (if i.val < 19 then 1 else 2)) else (if i.val < 22 then (if i.val < 21 then 1 else 2) else (if i.val < 23 then 1 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 2) else (if i.val < 27 then 1 else 2)) else (if i.val < 30 then (if i.val < 29 then 1 else 2) else (if i.val < 31 then 1 else 2))))) : Fin 3)
private def stepWitness (i : Fin 32) (j : Fin 3) : Fin 2 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,1,1] else #[1,1,1]) else (if i.val < 3 then #[1,1,1] else #[1,1,1])) else (if i.val < 6 then (if i.val < 5 then #[1,1,1] else #[1,1,1]) else (if i.val < 7 then #[1,1,1] else #[0,1,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[1,1,1] else #[1,1,0]) else (if i.val < 11 then #[0,1,1] else #[1,1,1])) else (if i.val < 14 then (if i.val < 13 then #[0,1,1] else #[1,1,1]) else (if i.val < 15 then #[1,1,0] else #[0,1,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[1,1,0] else #[0,1,1]) else (if i.val < 19 then #[1,1,0] else #[0,0,1])) else (if i.val < 22 then (if i.val < 21 then #[1,1,1] else #[0,0,0]) else (if i.val < 23 then #[0,1,0] else #[1,1,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[1,1,0] else #[0,1,1]) else (if i.val < 27 then #[1,1,0] else #[0,0,1])) else (if i.val < 30 then (if i.val < 29 then #[1,1,1] else #[0,0,0]) else (if i.val < 31 then #[0,1,0] else #[1,1,0]))))) : Array (Fin 2))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

def cosets : BinaryNormalCosetCertificate generators kernel 32 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 1⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 1
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  parent_next := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 1
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 32
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

end N1

namespace N2
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 26 else 30) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 26 else 30) else (if i.val < 3 then 59 else 63)) : Fin 64)
private def next (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[3,2] else #[2,3]) else (if i.val < 3 then #[1,0] else #[0,1])) : Array (Fin 4))[j.val]!
private def rank (i : Fin 4) : ℕ := (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 3 else 0))
private def parents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 0 else 3)) : Fin 4)
private def letters (i : Fin 4) : Fin 2 := ((if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 1 else 0)) : Fin 2)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 4 where
  rows := rows
  identity := 3
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=4 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 4) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[0,1] else (if i.val < 2 then #[0,1] else #[0,2])) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[0,1] else (if i.val < 2 then #[0,1] else #[0,2])) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 58) else (if i.val < 3 then 61 else 7)) else (if i.val < 6 then (if i.val < 5 then 60 else 6) else (if i.val < 7 then 23 else 5))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 55) else (if i.val < 11 then 0 else 41)) else (if i.val < 14 then (if i.val < 13 then 21 else 11) else (if i.val < 15 then 16 else 47)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,7,8])) else (if i.val < 6 then (if i.val < 5 then #[2,1,9] else #[3,10,11]) else (if i.val < 7 then #[9,12,13] else #[10,3,4]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,13,14] else #[6,14,15]) else (if i.val < 11 then #[7,5,2] else #[8,15,12])) else (if i.val < 14 then (if i.val < 13 then #[14,6,1] else #[15,8,10]) else (if i.val < 15 then #[12,9,0] else #[13,11,7])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,14] else #[0,4,12]) else (if i.val < 3 then #[4,0,10] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,10,1]) else (if i.val < 7 then #[9,12,2] else #[10,3,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,13,3] else #[6,14,4]) else (if i.val < 11 then #[7,5,13] else #[8,15,5])) else (if i.val < 14 then (if i.val < 13 then #[14,6,11] else #[15,8,6]) else (if i.val < 15 then #[12,9,8] else #[13,11,9])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 6) else (if i.val < 15 then 8 else 9)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 2 else 2)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3,3] else #[3,3,3]) else (if i.val < 3 then #[2,3,3] else #[1,3,3])) else (if i.val < 6 then (if i.val < 5 then #[2,3,3] else #[1,3,3]) else (if i.val < 7 then #[0,3,3] else #[3,3,0]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,2,3] else #[0,2,3]) else (if i.val < 11 then #[3,3,0] else #[0,2,2])) else (if i.val < 14 then (if i.val < 13 then #[3,3,1] else #[1,2,3]) else (if i.val < 15 then #[3,2,0] else #[1,2,3])))) : Array (Fin 4))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 16 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 3⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 3
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 16
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N2

namespace N3
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 26 else (if j.val < 2 then 30 else 8)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 12) else (if i.val < 3 then 26 else 30)) else (if i.val < 6 then (if i.val < 5 then 41 else 45) else (if i.val < 7 then 59 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,4,7] else #[4,5,6]) else (if i.val < 3 then #[7,6,5] else #[6,7,4])) else (if i.val < 6 then (if i.val < 5 then #[1,0,3] else #[0,1,2]) else (if i.val < 7 then #[3,2,1] else #[2,3,0]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 7) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 4 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 6) else (if i.val < 3 then 7 else 7)) else (if i.val < 6 then (if i.val < 5 then 3 else 2) else (if i.val < 7 then 2 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 2) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 1 else 0))) : Fin 3)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 8 where
  rows := rows
  identity := 7
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=8 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 8) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,5] else (if i.val < 2 then #[2,3,0] else #[2,6,1])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,5] else (if i.val < 2 then #[2,3,0] else #[2,6,4])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 58) else (if i.val < 3 then 61 else 7)) else (if i.val < 6 then (if i.val < 5 then 60 else 6) else (if i.val < 7 then 23 else 55))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,6,1])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,7,0]) else (if i.val < 7 then #[7,3,4] else #[6,5,2]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,5] else #[0,4,3]) else (if i.val < 3 then #[4,0,7] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,6] else #[3,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 4))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[6,7,7] else #[3,5,1])) else (if i.val < 6 then (if i.val < 5 then #[6,7,7] else #[3,0,4]) else (if i.val < 7 then #[2,5,0] else #[2,0,5]))) : Array (Fin 8))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 7⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 7
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 3
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 8
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N3

namespace N4
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 26 else (if j.val < 2 then 30 else 9)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 9 else 13) else (if i.val < 3 then 26 else 30)) else (if i.val < 6 then (if i.val < 5 then 40 else 44) else (if i.val < 7 then 59 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,4,2] else #[4,5,3]) else (if i.val < 3 then #[7,6,5] else #[6,7,4])) else (if i.val < 6 then (if i.val < 5 then #[1,0,6] else #[0,1,7]) else (if i.val < 7 then #[3,2,1] else #[2,3,0]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 7) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 4 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 6) else (if i.val < 3 then 7 else 7)) else (if i.val < 6 then (if i.val < 5 then 3 else 2) else (if i.val < 7 then 2 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 2) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 1 else 0))) : Fin 3)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 8 where
  rows := rows
  identity := 7
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=8 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 8) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,5] else (if i.val < 2 then #[2,3,1] else #[2,6,0])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,5] else (if i.val < 2 then #[2,3,1] else #[2,6,0])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 58) else (if i.val < 3 then 61 else 7)) else (if i.val < 6 then (if i.val < 5 then 60 else 6) else (if i.val < 7 then 23 else 5))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,6,1]) else (if i.val < 7 then #[7,5,2] else #[6,3,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,6,1]) else (if i.val < 7 then #[7,5,2] else #[6,3,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 1))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[6,7,7] else #[3,7,5])) else (if i.val < 6 then (if i.val < 5 then #[6,7,4] else #[3,4,0]) else (if i.val < 7 then #[1,1,4] else #[4,7,2]))) : Array (Fin 8))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 7⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 7
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 3
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 8
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N4

namespace N5
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 26 else (if j.val < 2 then 30 else 27)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 27) else (if i.val < 3 then 30 else 31)) else (if i.val < 6 then (if i.val < 5 then 58 else 59) else (if i.val < 7 then 62 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,5,6] else #[6,4,7]) else (if i.val < 3 then #[5,7,4] else #[4,6,5])) else (if i.val < 6 then (if i.val < 5 then #[3,1,2] else #[2,0,3]) else (if i.val < 7 then #[1,3,0] else #[0,2,1]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 2 else 7)) else (if i.val < 6 then (if i.val < 5 then 6 else 4) else (if i.val < 7 then 5 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 7 else 5)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 0 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 2 else 0))) : Fin 3)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 8 where
  rows := rows
  identity := 7
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=8 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 8) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[0,2,1] else (if i.val < 2 then #[0,2,3] else #[0,5,3])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[0,2,1] else (if i.val < 2 then #[0,2,3] else #[0,5,4])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 61) else (if i.val < 3 then 7 else 23)) else (if i.val < 6 then (if i.val < 5 then 5 else 9) else (if i.val < 7 then 21 else 11))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,4,5] else #[3,6,7])) else (if i.val < 6 then (if i.val < 5 then #[4,2,1] else #[5,7,6]) else (if i.val < 7 then #[6,3,0] else #[7,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1,6] else #[1,0,4]) else (if i.val < 3 then #[2,4,0] else #[3,6,1])) else (if i.val < 6 then (if i.val < 5 then #[4,2,7] else #[5,7,2]) else (if i.val < 7 then #[6,3,5] else #[7,5,3]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 3 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 1 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,7,7] else #[6,7,7]) else (if i.val < 3 then #[1,7,7] else #[3,7,7])) else (if i.val < 6 then (if i.val < 5 then #[4,7,3] else #[3,5,6]) else (if i.val < 7 then #[6,7,1] else #[1,5,4]))) : Array (Fin 8))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 7⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 7
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 3
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 8
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N5

namespace N6
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 30) else (if j.val < 3 then 8 else 9)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 9) else (if i.val < 3 then 12 else 13)) else (if i.val < 6 then (if i.val < 5 then 26 else 27) else (if i.val < 7 then 30 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 40 else 41) else (if i.val < 11 then 44 else 45)) else (if i.val < 14 then (if i.val < 13 then 58 else 59) else (if i.val < 15 then 62 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,9,15,14] else #[10,8,5,4]) else (if i.val < 3 then #[9,11,13,12] else #[8,10,7,6])) else (if i.val < 6 then (if i.val < 5 then #[15,13,11,10] else #[14,12,1,0]) else (if i.val < 7 then #[13,15,9,8] else #[12,14,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,1,12,13] else #[2,0,6,7]) else (if i.val < 11 then #[1,3,14,15] else #[0,2,4,5])) else (if i.val < 14 then (if i.val < 13 then #[7,5,8,9] else #[6,4,2,3]) else (if i.val < 15 then #[5,7,10,11] else #[4,6,0,1])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 4) else (if i.val < 3 then 12 else 13)) else (if i.val < 6 then (if i.val < 5 then 1 else 11) else (if i.val < 7 then 2 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 8) else (if i.val < 11 then 7 else 6)) else (if i.val < 14 then (if i.val < 13 then 15 else 5) else (if i.val < 15 then 10 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 13 else 13)) else (if i.val < 6 then (if i.val < 5 then 15 else 1) else (if i.val < 7 then 15 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 6) else (if i.val < 11 then 4 else 4)) else (if i.val < 14 then (if i.val < 13 then 8 else 4) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 1 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 2) else (if i.val < 11 then 3 else 2)) else (if i.val < 14 then (if i.val < 13 then 2 else 1) else (if i.val < 15 then 3 else 0)))) : Fin 4)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 16 where
  rows := rows
  identity := 15
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=16 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 16) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,6,11,10] else (if i.val < 2 then #[4,6,0,3] else #[4,13,2,1])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,6,11,10] else (if i.val < 2 then #[4,6,0,3] else #[4,13,9,1])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 61) else (if i.val < 3 then 7 else 23)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,3,0] else #[3,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,3,0] else #[3,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[12,15,15] else #[14,15,15]) else (if i.val < 3 then #[5,11,10] else #[7,11,8])) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 15⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 15
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 4
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 4
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N6

namespace N7
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 30) else (if j.val < 3 then 8 else 10)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 10) else (if i.val < 3 then 12 else 14)) else (if i.val < 6 then (if i.val < 5 then 24 else 26) else (if i.val < 7 then 28 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 41 else 43) else (if i.val < 11 then 45 else 47)) else (if i.val < 14 then (if i.val < 13 then 57 else 59) else (if i.val < 15 then 61 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,8,15,14] else #[11,9,14,15]) else (if i.val < 3 then #[8,10,13,12] else #[9,11,12,13])) else (if i.val < 6 then (if i.val < 5 then #[14,12,11,10] else #[15,13,10,11]) else (if i.val < 7 then #[12,14,9,8] else #[13,15,8,9]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,0,7,6] else #[3,1,6,7]) else (if i.val < 11 then #[0,2,5,4] else #[1,3,4,5])) else (if i.val < 14 then (if i.val < 13 then #[6,4,3,2] else #[7,5,2,3]) else (if i.val < 15 then #[4,6,1,0] else #[5,7,0,1])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 4) else (if i.val < 3 then 11 else 12)) else (if i.val < 6 then (if i.val < 5 then 13 else 1) else (if i.val < 7 then 14 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 6 else 7)) else (if i.val < 14 then (if i.val < 13 then 15 else 5) else (if i.val < 15 then 10 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 13 else 13)) else (if i.val < 6 then (if i.val < 5 then 10 else 15) else (if i.val < 7 then 8 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 7) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 2 else 5) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 0) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 2 else 3)) else (if i.val < 14 then (if i.val < 13 then 3 else 1) else (if i.val < 15 then 3 else 0)))) : Fin 4)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 16 where
  rows := rows
  identity := 15
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=16 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 16) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[5,7,10,9] else (if i.val < 2 then #[5,7,0,1] else #[5,13,2,6])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[5,7,10,9] else (if i.val < 2 then #[5,7,0,1] else #[5,13,8,4])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 58) else (if i.val < 3 then 7 else 6)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[3,2,1] else #[2,3,0])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0,3] else #[0,1,2]) else (if i.val < 3 then #[3,2,0] else #[2,3,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,14,15] else #[15,12,15]) else (if i.val < 3 then #[7,11,2] else #[7,3,8])) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 15⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 15
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 4
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 4
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N7

namespace N8
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 30) else (if j.val < 3 then 8 else 11)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 11) else (if i.val < 3 then 12 else 15)) else (if i.val < 6 then (if i.val < 5 then 25 else 26) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 41 else 42) else (if i.val < 11 then 45 else 46)) else (if i.val < 14 then (if i.val < 13 then 56 else 59) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,8,15,14] else #[11,9,4,7]) else (if i.val < 3 then #[8,10,13,12] else #[9,11,6,5])) else (if i.val < 6 then (if i.val < 5 then #[14,12,1,2] else #[15,13,10,11]) else (if i.val < 7 then #[12,14,3,0] else #[13,15,8,9]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,0,7,6] else #[3,1,12,15]) else (if i.val < 11 then #[0,2,5,4] else #[1,3,14,13])) else (if i.val < 14 then (if i.val < 13 then #[6,4,9,10] else #[7,5,2,3]) else (if i.val < 15 then #[4,6,11,8] else #[5,7,0,1])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 4) else (if i.val < 3 then 12 else 13)) else (if i.val < 6 then (if i.val < 5 then 11 else 1) else (if i.val < 7 then 14 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 6 else 7)) else (if i.val < 14 then (if i.val < 13 then 15 else 5) else (if i.val < 15 then 10 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 13 else 13)) else (if i.val < 6 then (if i.val < 5 then 1 else 15) else (if i.val < 7 then 8 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 7) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 9 else 5) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 2 else 3)) else (if i.val < 14 then (if i.val < 13 then 2 else 1) else (if i.val < 15 then 3 else 0)))) : Fin 4)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 16 where
  rows := rows
  identity := 15
  identity_eq := by decide +kernel
  next := next
  next_eq := (by decide +kernel)
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=16 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 16) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[5,7,10,9] else (if i.val < 2 then #[5,7,0,3] else #[5,13,2,4])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[5,7,10,9] else (if i.val < 2 then #[5,7,0,3] else #[5,13,8,12])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 58) else (if i.val < 3 then 7 else 6)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,1,2] else #[0,0,3]) else (if i.val < 3 then #[3,3,1] else #[2,2,0])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,1,3] else #[0,0,2]) else (if i.val < 3 then #[3,3,0] else #[2,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,14,15] else #[15,12,15]) else (if i.val < 3 then #[7,1,2] else #[7,9,8])) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 15⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 15
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 4
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 4
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N8

namespace N9
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 30) else (if j.val < 3 then 8 else (if j.val < 4 then 9 else 0))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 4 else 5)) else (if i.val < 6 then (if i.val < 5 then 8 else 9) else (if i.val < 7 then 12 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 18 else 19) else (if i.val < 11 then 22 else 23)) else (if i.val < 14 then (if i.val < 13 then 26 else 27) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 33) else (if i.val < 19 then 36 else 37)) else (if i.val < 22 then (if i.val < 21 then 40 else 41) else (if i.val < 23 then 44 else 45))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 50 else 51) else (if i.val < 27 then 54 else 55)) else (if i.val < 30 then (if i.val < 29 then 58 else 59) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[19,17,25,24,15] else #[18,16,11,10,29]) else (if i.val < 3 then #[17,19,27,26,30] else #[16,18,9,8,12])) else (if i.val < 6 then (if i.val < 5 then #[23,21,31,30,27] else #[22,20,13,12,9]) else (if i.val < 7 then #[21,23,29,28,10] else #[20,22,15,14,24]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[27,25,17,16,7] else #[26,24,3,2,21]) else (if i.val < 11 then #[25,27,19,18,22] else #[24,26,1,0,4])) else (if i.val < 14 then (if i.val < 13 then #[31,29,23,22,19] else #[30,28,5,4,1]) else (if i.val < 15 then #[29,31,21,20,2] else #[28,30,7,6,16])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[3,1,26,27,31] else #[2,0,8,9,13]) else (if i.val < 19 then #[1,3,24,25,14] else #[0,2,10,11,28])) else (if i.val < 22 then (if i.val < 21 then #[7,5,28,29,11] else #[6,4,14,15,25]) else (if i.val < 23 then #[5,7,30,31,26] else #[4,6,12,13,8]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[11,9,18,19,23] else #[10,8,0,1,5]) else (if i.val < 27 then #[9,11,16,17,6] else #[8,10,2,3,20])) else (if i.val < 30 then (if i.val < 29 then #[15,13,20,21,3] else #[14,12,6,7,17]) else (if i.val < 31 then #[13,15,22,23,18] else #[12,14,4,5,0]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 30) else (if i.val < 3 then 12 else 29)) else (if i.val < 6 then (if i.val < 5 then 3 else 4) else (if i.val < 7 then 21 else 22))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 23 else 16) else (if i.val < 11 then 25 else 26)) else (if i.val < 14 then (if i.val < 13 then 1 else 15) else (if i.val < 15 then 2 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 31 else 17) else (if i.val < 19 then 28 else 9)) else (if i.val < 22 then (if i.val < 21 then 11 else 10) else (if i.val < 23 then 8 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 19 else 18) else (if i.val < 27 then 24 else 14)) else (if i.val < 30 then (if i.val < 29 then 27 else 6) else (if i.val < 31 then 13 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 13) else (if i.val < 3 then 14 else 27)) else (if i.val < 6 then (if i.val < 5 then 31 else 31) else (if i.val < 7 then 29 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 23 else 5) else (if i.val < 11 then 19 else 19)) else (if i.val < 14 then (if i.val < 13 then 31 else 5) else (if i.val < 15 then 31 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 15 else 0) else (if i.val < 19 then 30 else 12)) else (if i.val < 22 then (if i.val < 21 then 14 else 14) else (if i.val < 23 then 12 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 22 else 4)) else (if i.val < 30 then (if i.val < 29 then 19 else 12) else (if i.val < 31 then 4 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 4) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 4) else (if i.val < 11 then 2 else 3)) else (if i.val < 14 then (if i.val < 13 then 0 else 2) else (if i.val < 15 then 1 else 4)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 1) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 2) else (if i.val < 23 then 3 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 2) else (if i.val < 27 then 4 else 4)) else (if i.val < 30 then (if i.val < 29 then 4 else 1) else (if i.val < 31 then 3 else 0))))) : Fin 5)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 32 where
  rows := rows
  identity := 31
  identity_eq := by decide +kernel
  next := next
  next_eq := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  parent_next := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=32 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 32) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,14,23,22,0] else (if i.val < 2 then #[12,14,4,7,10] else #[12,29,6,5,8])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,14,23,22,0] else (if i.val < 2 then #[12,14,4,7,10] else #[12,29,21,5,10])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 61) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,1] else #[1,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,1] else #[1,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 1) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[28,31,19] else #[30,31,25]) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 31⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 31
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 5
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 2
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N9

namespace N10
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 30) else (if j.val < 3 then 8 else (if j.val < 4 then 9 else 2))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 6 else 7)) else (if i.val < 6 then (if i.val < 5 then 8 else 9) else (if i.val < 7 then 12 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 17) else (if i.val < 11 then 20 else 21)) else (if i.val < 14 then (if i.val < 13 then 26 else 27) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 35) else (if i.val < 19 then 38 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 41) else (if i.val < 23 then 44 else 45))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 49) else (if i.val < 27 then 52 else 53)) else (if i.val < 30 then (if i.val < 29 then 58 else 59) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[19,17,25,24,7] else #[18,16,11,10,23]) else (if i.val < 3 then #[17,19,27,26,22] else #[16,18,9,8,6])) else (if i.val < 6 then (if i.val < 5 then #[23,21,31,30,27] else #[22,20,13,12,11]) else (if i.val < 7 then #[21,23,29,28,10] else #[20,22,15,14,26]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[27,25,17,16,15] else #[26,24,3,2,31]) else (if i.val < 11 then #[25,27,19,18,30] else #[24,26,1,0,14])) else (if i.val < 14 then (if i.val < 13 then #[31,29,23,22,19] else #[30,28,5,4,3]) else (if i.val < 15 then #[29,31,21,20,2] else #[28,30,7,6,18])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[3,1,26,27,21] else #[2,0,8,9,5]) else (if i.val < 19 then #[1,3,24,25,4] else #[0,2,10,11,20])) else (if i.val < 22 then (if i.val < 21 then #[7,5,28,29,9] else #[6,4,14,15,25]) else (if i.val < 23 then #[5,7,30,31,24] else #[4,6,12,13,8]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[11,9,18,19,29] else #[10,8,0,1,13]) else (if i.val < 27 then #[9,11,16,17,12] else #[8,10,2,3,28])) else (if i.val < 30 then (if i.val < 29 then #[15,13,20,21,1] else #[14,12,6,7,17]) else (if i.val < 31 then #[13,15,22,23,16] else #[12,14,4,5,0]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 30) else (if i.val < 3 then 12 else 29)) else (if i.val < 6 then (if i.val < 5 then 3 else 4) else (if i.val < 7 then 21 else 20))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 26) else (if i.val < 11 then 23 else 16)) else (if i.val < 14 then (if i.val < 13 then 1 else 15) else (if i.val < 15 then 2 else 24)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 28 else 17) else (if i.val < 19 then 31 else 9)) else (if i.val < 22 then (if i.val < 21 then 11 else 10) else (if i.val < 23 then 8 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 19 else 18) else (if i.val < 27 then 27 else 14)) else (if i.val < 30 then (if i.val < 29 then 25 else 6) else (if i.val < 31 then 13 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 11) else (if i.val < 3 then 14 else 27)) else (if i.val < 6 then (if i.val < 5 then 31 else 31) else (if i.val < 7 then 29 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 23 else 20) else (if i.val < 11 then 19 else 5)) else (if i.val < 14 then (if i.val < 13 then 31 else 5) else (if i.val < 15 then 31 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 0) else (if i.val < 19 then 24 else 12)) else (if i.val < 22 then (if i.val < 21 then 14 else 14) else (if i.val < 23 then 12 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 2 else 4)) else (if i.val < 30 then (if i.val < 29 then 20 else 12) else (if i.val < 31 then 4 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 2) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 2 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 4) else (if i.val < 11 then 2 else 4)) else (if i.val < 14 then (if i.val < 13 then 0 else 2) else (if i.val < 15 then 1 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 1) else (if i.val < 19 then 2 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 2) else (if i.val < 23 then 3 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 2) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 2 else 1) else (if i.val < 31 then 3 else 0))))) : Fin 5)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 32 where
  rows := rows
  identity := 31
  identity_eq := by decide +kernel
  next := next
  next_eq := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  parent_next := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=32 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 32) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,14,23,22,2] else (if i.val < 2 then #[12,14,4,7,10] else #[12,29,6,5,17])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,14,23,22,2] else (if i.val < 2 then #[12,14,4,7,10] else #[12,29,21,5,2])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 61) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,0] else #[1,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,0] else #[1,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 1) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[28,31,27] else #[30,31,17]) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 31⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 31
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 5
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 2
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N10

namespace N11
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 26 else 30) else (if j.val < 3 then 8 else (if j.val < 4 then 9 else 10))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 9) else (if i.val < 3 then 10 else 11)) else (if i.val < 6 then (if i.val < 5 then 12 else 13) else (if i.val < 7 then 14 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 25) else (if i.val < 11 then 26 else 27)) else (if i.val < 14 then (if i.val < 13 then 28 else 29) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 40 else 41) else (if i.val < 19 then 42 else 43)) else (if i.val < 22 then (if i.val < 21 then 44 else 45) else (if i.val < 23 then 46 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[21,17,31,30,29] else #[20,16,11,10,13]) else (if i.val < 3 then #[23,19,29,28,31] else #[22,18,9,8,15])) else (if i.val < 6 then (if i.val < 5 then #[17,21,27,26,25] else #[16,20,15,14,9]) else (if i.val < 7 then #[19,23,25,24,27] else #[18,22,13,12,11]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[29,25,23,22,21] else #[28,24,3,2,5]) else (if i.val < 11 then #[31,27,21,20,23] else #[30,26,1,0,7])) else (if i.val < 14 then (if i.val < 13 then #[25,29,19,18,17] else #[24,28,7,6,1]) else (if i.val < 15 then #[27,31,17,16,19] else #[26,30,5,4,3])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[5,1,26,27,28] else #[4,0,14,15,12]) else (if i.val < 19 then #[7,3,24,25,30] else #[6,2,12,13,14])) else (if i.val < 22 then (if i.val < 21 then #[1,5,30,31,24] else #[0,4,10,11,8]) else (if i.val < 23 then #[3,7,28,29,26] else #[2,6,8,9,10]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[13,9,18,19,20] else #[12,8,6,7,4]) else (if i.val < 27 then #[15,11,16,17,22] else #[14,10,4,5,6])) else (if i.val < 30 then (if i.val < 29 then #[9,13,22,23,16] else #[8,12,2,3,0]) else (if i.val < 31 then #[11,15,20,21,18] else #[10,14,0,1,2]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 4) else (if i.val < 3 then 5 else 28)) else (if i.val < 6 then (if i.val < 5 then 18 else 19) else (if i.val < 7 then 20 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 23) else (if i.val < 11 then 1 else 15)) else (if i.val < 14 then (if i.val < 13 then 25 else 16) else (if i.val < 15 then 2 else 24)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 11 else 10) else (if i.val < 19 then 27 else 12)) else (if i.val < 22 then (if i.val < 21 then 8 else 7) else (if i.val < 23 then 30 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 31) else (if i.val < 27 then 26 else 6)) else (if i.val < 30 then (if i.val < 29 then 17 else 14) else (if i.val < 31 then 13 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 31 else 29)) else (if i.val < 6 then (if i.val < 5 then 27 else 27) else (if i.val < 7 then 27 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 23) else (if i.val < 11 then 31 else 1)) else (if i.val < 14 then (if i.val < 13 then 17 else 1) else (if i.val < 15 then 31 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 14 else 14) else (if i.val < 19 then 30 else 14)) else (if i.val < 22 then (if i.val < 21 then 10 else 10) else (if i.val < 23 then 28 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 20 else 4) else (if i.val < 27 then 16 else 10)) else (if i.val < 30 then (if i.val < 29 then 2 else 0) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 3) else (if i.val < 11 then 0 else 2)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 1 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 2) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 2) else (if i.val < 23 then 2 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 4) else (if i.val < 27 then 2 else 1)) else (if i.val < 30 then (if i.val < 29 then 3 else 4) else (if i.val < 31 then 3 else 0))))) : Fin 5)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 32 where
  rows := rows
  identity := 31
  identity_eq := by decide +kernel
  next := next
  next_eq := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  parent_next := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=32 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 32) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[10,14,21,20,19] else (if i.val < 2 then #[10,14,0,5,2] else #[10,27,4,1,12])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[10,14,21,20,19] else (if i.val < 2 then #[10,14,0,5,2] else #[10,27,17,1,8])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 7) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,0,1] else #[1,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,0,1] else #[1,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 2) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[26,29,31] else #[11,23,20]) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 31⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 31
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 5
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 2
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N11

namespace N12
def normalGenerators (j : Fin 6) : Source := ⟨((if j.val < 3 then (if j.val < 1 then 26 else (if j.val < 2 then 30 else 8)) else (if j.val < 4 then 9 else (if j.val < 5 then 0 else 2))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63)))))) : Fin 64)
private def next (i : Fin 64) (j : Fin 6) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[37,33,51,50,31,29] else #[36,32,23,22,59,61]) else (if i.val < 3 then #[39,35,49,48,15,13] else #[38,34,21,20,43,45])) else (if i.val < 6 then (if i.val < 5 then #[33,37,55,54,62,60] else #[32,36,19,18,26,28]) else (if i.val < 7 then #[35,39,53,52,46,44] else #[34,38,17,16,10,12]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[45,41,63,62,55,53] else #[44,40,27,26,19,21]) else (if i.val < 11 then #[47,43,61,60,39,37] else #[46,42,25,24,3,5])) else (if i.val < 14 then (if i.val < 13 then #[41,45,59,58,22,20] else #[40,44,31,30,50,52]) else (if i.val < 15 then #[43,47,57,56,6,4] else #[42,46,29,28,34,36])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[53,49,35,34,29,31] else #[52,48,7,6,57,63]) else (if i.val < 19 then #[55,51,33,32,13,15] else #[54,50,5,4,41,47])) else (if i.val < 22 then (if i.val < 21 then #[49,53,39,38,60,62] else #[48,52,3,2,24,30]) else (if i.val < 23 then #[51,55,37,36,44,46] else #[50,54,1,0,8,14]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[61,57,47,46,53,55] else #[60,56,11,10,17,23]) else (if i.val < 27 then #[63,59,45,44,37,39] else #[62,58,9,8,1,7])) else (if i.val < 30 then (if i.val < 29 then #[57,61,43,42,20,22] else #[56,60,15,14,48,54]) else (if i.val < 31 then #[59,63,41,40,4,6] else #[58,62,13,12,32,38]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[5,1,54,55,63,57] else #[4,0,18,19,27,25]) else (if i.val < 35 then #[7,3,52,53,47,41] else #[6,2,16,17,11,9])) else (if i.val < 38 then (if i.val < 37 then #[1,5,50,51,30,24] else #[0,4,22,23,58,56]) else (if i.val < 39 then #[3,7,48,49,14,8] else #[2,6,20,21,42,40]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[13,9,58,59,23,17] else #[12,8,30,31,51,49]) else (if i.val < 43 then #[15,11,56,57,7,1] else #[14,10,28,29,35,33])) else (if i.val < 46 then (if i.val < 45 then #[9,13,62,63,54,48] else #[8,12,26,27,18,16]) else (if i.val < 47 then #[11,15,60,61,38,32] else #[10,14,24,25,2,0])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[21,17,38,39,61,59] else #[20,16,2,3,25,27]) else (if i.val < 51 then #[23,19,36,37,45,43] else #[22,18,0,1,9,11])) else (if i.val < 54 then (if i.val < 53 then #[17,21,34,35,28,26] else #[16,20,6,7,56,58]) else (if i.val < 55 then #[19,23,32,33,12,10] else #[18,22,4,5,40,42]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[29,25,42,43,21,19] else #[28,24,14,15,49,51]) else (if i.val < 59 then #[31,27,40,41,5,3] else #[30,26,12,13,33,35])) else (if i.val < 62 then (if i.val < 61 then #[25,29,46,47,52,50] else #[24,28,10,11,16,18]) else (if i.val < 63 then #[27,31,44,45,36,34] else #[26,30,8,9,0,2])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 50) else (if i.val < 3 then 6 else 52)) else (if i.val < 6 then (if i.val < 5 then 14 else 48) else (if i.val < 7 then 15 else 49))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 62 else 55)) else (if i.val < 14 then (if i.val < 13 then 32 else 31) else (if i.val < 15 then 59 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 42) else (if i.val < 19 then 33 else 20)) else (if i.val < 22 then (if i.val < 21 then 40 else 21) else (if i.val < 23 then 36 else 37))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 53 else 54) else (if i.val < 27 then 1 else 19)) else (if i.val < 30 then (if i.val < 29 then 61 else 26) else (if i.val < 31 then 2 else 25))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 22) else (if i.val < 35 then 47 else 27)) else (if i.val < 38 then (if i.val < 37 then 46 else 10) else (if i.val < 39 then 58 else 11))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 13 else 12) else (if i.val < 43 then 41 else 56)) else (if i.val < 46 then (if i.val < 45 then 9 else 8) else (if i.val < 47 then 45 else 51)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 29 else 28) else (if i.val < 51 then 24 else 23)) else (if i.val < 54 then (if i.val < 53 then 44 else 18) else (if i.val < 55 then 35 else 17))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 39 else 63) else (if i.val < 59 then 38 else 7)) else (if i.val < 62 then (if i.val < 61 then 43 else 60) else (if i.val < 63 then 16 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 27) else (if i.val < 3 then 63 else 21)) else (if i.val < 6 then (if i.val < 5 then 30 else 55) else (if i.val < 7 then 30 else 53))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 63 else 63) else (if i.val < 11 then 54 else 51)) else (if i.val < 14 then (if i.val < 13 then 59 else 2) else (if i.val < 15 then 29 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 45 else 40) else (if i.val < 19 then 45 else 9)) else (if i.val < 22 then (if i.val < 21 then 39 else 9) else (if i.val < 23 then 37 else 37))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 33) else (if i.val < 27 then 63 else 9)) else (if i.val < 30 then (if i.val < 29 then 15 else 0) else (if i.val < 31 then 63 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 31 else 0) else (if i.val < 35 then 62 else 2)) else (if i.val < 38 then (if i.val < 37 then 62 else 26) else (if i.val < 39 then 31 else 26))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 30 else 30) else (if i.val < 43 then 39 else 50)) else (if i.val < 46 then (if i.val < 45 then 26 else 26) else (if i.val < 47 then 6 else 19)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 2 else 2) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 6 else 8) else (if i.val < 55 then 44 else 8))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 37 else 42) else (if i.val < 59 then 37 else 26)) else (if i.val < 62 then (if i.val < 61 then 4 else 48) else (if i.val < 63 then 8 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 6 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 4) else (if i.val < 3 then 5 else 2)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 5 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 2 else 5) else (if i.val < 15 then 3 else 4)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 5 else 5) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 2 else 5) else (if i.val < 23 then 2 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 5) else (if i.val < 27 then 0 else 2)) else (if i.val < 30 then (if i.val < 29 then 3 else 5) else (if i.val < 31 then 1 else 4))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 4 else 1) else (if i.val < 35 then 5 else 1)) else (if i.val < 38 then (if i.val < 37 then 4 else 4) else (if i.val < 39 then 5 else 5))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 3 else 2) else (if i.val < 43 then 4 else 5)) else (if i.val < 46 then (if i.val < 45 then 3 else 2) else (if i.val < 47 then 4 else 5)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 3 else 2) else (if i.val < 51 then 3 else 2)) else (if i.val < 54 then (if i.val < 53 then 3 else 5) else (if i.val < 55 then 4 else 4))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 5 else 3) else (if i.val < 59 then 4 else 1)) else (if i.val < 62 then (if i.val < 61 then 5 else 4) else (if i.val < 63 then 3 else 0)))))) : Fin 6)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 64 where
  rows := rows
  identity := 63
  identity_eq := by decide +kernel
  next := next
  next_eq := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
  parent_next := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=64 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 64) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 6) : Fin 64 := ((if i.val < 1 then #[26,30,45,44,0,6] else (if i.val < 2 then #[26,30,8,13,22,20] else #[26,59,12,9,18,35])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 6) : Fin 64 := ((if i.val < 1 then #[26,30,45,44,0,6] else (if i.val < 2 then #[26,30,8,13,22,20] else #[26,59,41,9,22,6])) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 1) : Source := ⟨(63 : Fin 64)⟩
private def quotientNext (i : Fin 1) (j : Fin 3) : Fin 1 := (#[0,0,0] : Array (Fin 1))[j.val]!
private def quotientPrev (i : Fin 1) (j : Fin 3) : Fin 1 := (#[0,0,0] : Array (Fin 1))[j.val]!
private def quotientParents (i : Fin 1) : Fin 1 := (0 : Fin 1)
private def quotientLetters (i : Fin 1) : Fin 3 := (0 : Fin 3)
private def stepWitness (i : Fin 1) (j : Fin 3) : Fin 64 := (#[58,61,53] : Array (Fin 64))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 1 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 63⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 63
  next := quotientNext
  step_mem := fun i j => (quotientStep_checked i j) ▸ row_mem (stepWitness i j)
  rank i := i.val
  parent i _ := quotientParents i
  letter i _ := quotientLetters i
  parent_lt := (by decide +kernel)
  parent_next := (by decide +kernel)

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 6
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 1
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

end N12

@[reducible] def states (i : Fin 13) : BinaryNormalState generators :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then N0.state else (if i.val < 2 then N1.state else N2.state)) else (if i.val < 4 then N3.state else (if i.val < 5 then N4.state else N5.state))) else (if i.val < 9 then (if i.val < 7 then N6.state else (if i.val < 8 then N7.state else N8.state)) else (if i.val < 11 then (if i.val < 10 then N9.state else N10.state) else (if i.val < 12 then N11.state else N12.state))))

end SymmetricSubgroupAsymptotics.RDTBinaryNormal8T28
