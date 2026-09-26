import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T27

/-! Exact original normal states and quotient rows for 8T27.
Selected by export_lean_carrier_j_registry.py; all finite facts are checked
in Lean's kernel. This file certifies normal-state coverage, not the later
pair/character/transport acceptance of those states. -/

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27

abbrev Source := FiniteGroupRow 64
local instance : Group Source := BinaryMenuCayley8T27.group

def generators (j : Fin 2) : Source :=
  ⟨BinaryMenuCayley8T27.certificate.next BinaryMenuCayley8T27.certificate.identity j⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  apply binaryNormal_full_generators_of_equiv BinaryMenuCayley8T27.generators
    generators BinaryMenuCayley8T27.originalEquiv
  intro j
  change BinaryMenuCayley8T27.certificate.toCayley.elements
    (BinaryMenuCayley8T27.certificate.toCayley.next
      BinaryMenuCayley8T27.certificate.toCayley.identity j)=_
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

private def representatives (i : Fin 64) : Source := ⟨((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 3 else 7)) else (if i.val < 6 then (if i.val < 5 then 35 else 13) else (if i.val < 7 then 39 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 45) else (if i.val < 11 then 22 else 11)) else (if i.val < 14 then (if i.val < 13 then 47 else 23) else (if i.val < 15 then 41 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 18 else 54) else (if i.val < 19 then 43 else 21)) else (if i.val < 22 then (if i.val < 21 then 19 else 55) else (if i.val < 23 then 16 else 52))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 62 else 50) else (if i.val < 27 then 61 else 59)) else (if i.val < 30 then (if i.val < 29 then 17 else 53) else (if i.val < 31 then 30 else 51))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 29 else 27) else (if i.val < 35 then 48 else 60)) else (if i.val < 38 then (if i.val < 37 then 58 else 57) else (if i.val < 39 then 2 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 49 else 28) else (if i.val < 43 then 26 else 25)) else (if i.val < 46 then (if i.val < 45 then 6 else 5) else (if i.val < 47 then 56 else 34)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 33 else 0) else (if i.val < 51 then 12 else 24)) else (if i.val < 54 then (if i.val < 53 then 38 else 37) else (if i.val < 55 then 4 else 14))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 32 else 8) else (if i.val < 59 then 44 else 36)) else (if i.val < 62 then (if i.val < 61 then 10 else 46) else (if i.val < 63 then 40 else 42)))))) : Fin 64)⟩
private def quotientNext (i : Fin 64) (j : Fin 2) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[4,5] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,8] else #[9,10]) else (if i.val < 7 then #[3,11] else #[12,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[14,15] else #[5,16]) else (if i.val < 11 then #[17,0] else #[18,19])) else (if i.val < 14 then (if i.val < 13 then #[7,20] else #[21,1]) else (if i.val < 15 then #[8,22] else #[23,24])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[25,26] else #[10,27]) else (if i.val < 19 then #[11,28] else #[29,30])) else (if i.val < 22 then (if i.val < 21 then #[31,32] else #[13,33]) else (if i.val < 23 then #[34,35] else #[15,36]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[30,4] else #[16,37]) else (if i.val < 27 then #[32,38] else #[33,39])) else (if i.val < 30 then (if i.val < 29 then #[40,41] else #[19,42]) else (if i.val < 31 then #[24,6] else #[20,43]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[26,44] else #[27,45]) else (if i.val < 35 then #[22,46] else #[41,47])) else (if i.val < 38 then (if i.val < 37 then #[42,48] else #[43,49]) else (if i.val < 39 then #[47,9] else #[48,50]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[28,51] else #[35,52]) else (if i.val < 43 then #[36,53] else #[37,54])) else (if i.val < 46 then (if i.val < 45 then #[52,12] else #[53,55]) else (if i.val < 47 then #[51,56] else #[38,14])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[39,57] else #[56,58]) else (if i.val < 51 then #[58,17] else #[46,59])) else (if i.val < 54 then (if i.val < 53 then #[44,18] else #[45,60]) else (if i.val < 55 then #[59,61] else #[61,21]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[49,62] else #[62,23]) else (if i.val < 59 then #[50,25] else #[54,63])) else (if i.val < 62 then (if i.val < 61 then #[63,29] else #[55,31]) else (if i.val < 63 then #[57,34] else #[60,40])))))) : Array (Fin 64))[j.val]!
private def quotientPrev (i : Fin 64) (j : Fin 2) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,10] else #[0,13]) else (if i.val < 3 then #[4,0] else #[6,1])) else (if i.val < 6 then (if i.val < 5 then #[2,24] else #[9,2]) else (if i.val < 7 then #[3,30] else #[12,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[14,4] else #[5,38]) else (if i.val < 11 then #[17,5] else #[18,6])) else (if i.val < 14 then (if i.val < 13 then #[7,44] else #[21,7]) else (if i.val < 15 then #[8,47] else #[23,8])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[25,9] else #[10,50]) else (if i.val < 19 then #[11,52] else #[29,11])) else (if i.val < 22 then (if i.val < 21 then #[31,12] else #[13,55]) else (if i.val < 23 then #[34,14] else #[15,57]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[30,15] else #[16,58]) else (if i.val < 27 then #[32,16] else #[33,17])) else (if i.val < 30 then (if i.val < 29 then #[40,18] else #[19,60]) else (if i.val < 31 then #[24,19] else #[20,61]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[26,20] else #[27,21]) else (if i.val < 35 then #[22,62] else #[41,22])) else (if i.val < 38 then (if i.val < 37 then #[42,23] else #[43,25]) else (if i.val < 39 then #[47,26] else #[48,27]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[28,63] else #[35,28]) else (if i.val < 43 then #[36,29] else #[37,31])) else (if i.val < 46 then (if i.val < 45 then #[52,32] else #[53,33]) else (if i.val < 47 then #[51,34] else #[38,35])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[39,36] else #[56,37]) else (if i.val < 51 then #[58,39] else #[46,40])) else (if i.val < 54 then (if i.val < 53 then #[44,41] else #[45,42]) else (if i.val < 55 then #[59,43] else #[61,45]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[49,46] else #[62,48]) else (if i.val < 59 then #[50,49] else #[54,51])) else (if i.val < 62 then (if i.val < 61 then #[63,53] else #[55,54]) else (if i.val < 63 then #[57,56] else #[60,59])))))) : Array (Fin 64))[j.val]!
private def quotientParents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 3 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 5 else 6)) else (if i.val < 14 then (if i.val < 13 then 7 else 7) else (if i.val < 15 then 8 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 10) else (if i.val < 19 then 11 else 11)) else (if i.val < 22 then (if i.val < 21 then 12 else 13) else (if i.val < 23 then 14 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 15 else 16) else (if i.val < 27 then 16 else 17)) else (if i.val < 30 then (if i.val < 29 then 18 else 19) else (if i.val < 31 then 19 else 20))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 20 else 21) else (if i.val < 35 then 22 else 22)) else (if i.val < 38 then (if i.val < 37 then 23 else 25) else (if i.val < 39 then 26 else 27))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 28 else 28) else (if i.val < 43 then 29 else 31)) else (if i.val < 46 then (if i.val < 45 then 32 else 33) else (if i.val < 47 then 34 else 35)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 36 else 37) else (if i.val < 51 then 39 else 40)) else (if i.val < 54 then (if i.val < 53 then 41 else 42) else (if i.val < 55 then 43 else 45))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 48) else (if i.val < 59 then 49 else 51)) else (if i.val < 62 then (if i.val < 61 then 53 else 54) else (if i.val < 63 then 56 else 59)))))) : Fin 64)
private def quotientLetters (i : Fin 64) : Fin 2 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 0 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 0 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 0) else (if i.val < 19 then 0 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 0) else (if i.val < 23 then 1 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 0) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 1 else 0) else (if i.val < 31 then 1 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 1 else 1) else (if i.val < 35 then 0 else 1)) else (if i.val < 38 then (if i.val < 37 then 1 else 1) else (if i.val < 39 then 1 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 1) else (if i.val < 43 then 1 else 1)) else (if i.val < 46 then (if i.val < 45 then 1 else 1) else (if i.val < 47 then 1 else 1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 1 else 1) else (if i.val < 51 then 1 else 1)) else (if i.val < 54 then (if i.val < 53 then 1 else 1) else (if i.val < 55 then 1 else 1))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 1 else 1) else (if i.val < 59 then 1 else 1)) else (if i.val < 62 then (if i.val < 61 then 1 else 1) else (if i.val < 63 then 1 else 1)))))) : Fin 2)
private def stepWitness (i : Fin 64) (j : Fin 2) : Fin 1 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0] else #[0,0]) else (if i.val < 3 then #[0,0] else #[0,0])) else (if i.val < 6 then (if i.val < 5 then #[0,0] else #[0,0]) else (if i.val < 7 then #[0,0] else #[0,0]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,0] else #[0,0]) else (if i.val < 11 then #[0,0] else #[0,0])) else (if i.val < 14 then (if i.val < 13 then #[0,0] else #[0,0]) else (if i.val < 15 then #[0,0] else #[0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[0,0] else #[0,0]) else (if i.val < 19 then #[0,0] else #[0,0])) else (if i.val < 22 then (if i.val < 21 then #[0,0] else #[0,0]) else (if i.val < 23 then #[0,0] else #[0,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[0,0] else #[0,0]) else (if i.val < 27 then #[0,0] else #[0,0])) else (if i.val < 30 then (if i.val < 29 then #[0,0] else #[0,0]) else (if i.val < 31 then #[0,0] else #[0,0]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,0] else #[0,0]) else (if i.val < 35 then #[0,0] else #[0,0])) else (if i.val < 38 then (if i.val < 37 then #[0,0] else #[0,0]) else (if i.val < 39 then #[0,0] else #[0,0]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[0,0] else #[0,0]) else (if i.val < 43 then #[0,0] else #[0,0])) else (if i.val < 46 then (if i.val < 45 then #[0,0] else #[0,0]) else (if i.val < 47 then #[0,0] else #[0,0])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[0,0] else #[0,0]) else (if i.val < 51 then #[0,0] else #[0,0])) else (if i.val < 54 then (if i.val < 53 then #[0,0] else #[0,0]) else (if i.val < 55 then #[0,0] else #[0,0]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[0,0] else #[0,0]) else (if i.val < 59 then #[0,0] else #[0,0])) else (if i.val < 62 then (if i.val < 61 then #[0,0] else #[0,0]) else (if i.val < 63 then #[0,0] else #[0,0])))))) : Array (Fin 1))[j.val]!
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

def literalNormalGenerators (k : Fin 0) : Equiv.Perm (Fin 8) :=
  Fin.elim0 k

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 0) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  exact Fin.elim0 k

end N0

namespace N1
def normalGenerators (j : Fin 1) : Source := ⟨(24 : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 2) : Fin 64 := ((if i.val < 1 then 24 else 63) : Fin 64)
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

private def posWitness (i : Fin 2) (j : Fin 1) : Fin 2 := ((if i.val < 1 then #[0] else #[0]) : Array (Fin 2))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 1) : Fin 2 := ((if i.val < 1 then #[0] else #[0]) : Array (Fin 2))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 32) : Source := ⟨((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 3 else 7)) else (if i.val < 6 then (if i.val < 5 then 35 else 13) else (if i.val < 7 then 39 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 45) else (if i.val < 11 then 22 else 11)) else (if i.val < 14 then (if i.val < 13 then 47 else 23) else (if i.val < 15 then 41 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 18 else 54) else (if i.val < 19 then 43 else 21)) else (if i.val < 22 then (if i.val < 21 then 19 else 55) else (if i.val < 23 then 62 else 61))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 59 else 30) else (if i.val < 27 then 29 else 27)) else (if i.val < 30 then (if i.val < 29 then 2 else 1) else (if i.val < 31 then 6 else 5))))) : Fin 64)⟩
private def quotientNext (i : Fin 32) (j : Fin 2) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[4,5] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,8] else #[9,10]) else (if i.val < 7 then #[3,11] else #[12,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[14,15] else #[5,16]) else (if i.val < 11 then #[17,0] else #[18,19])) else (if i.val < 14 then (if i.val < 13 then #[7,20] else #[21,1]) else (if i.val < 15 then #[8,21] else #[20,22])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[19,23] else #[10,24]) else (if i.val < 19 then #[11,17] else #[16,25])) else (if i.val < 22 then (if i.val < 21 then #[15,26] else #[13,27]) else (if i.val < 23 then #[25,4] else #[26,28]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,29] else #[22,6]) else (if i.val < 27 then #[23,30] else #[24,31])) else (if i.val < 30 then (if i.val < 29 then #[31,9] else #[30,18]) else (if i.val < 31 then #[29,12] else #[28,14]))))) : Array (Fin 32))[j.val]!
private def quotientPrev (i : Fin 32) (j : Fin 2) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,10] else #[0,13]) else (if i.val < 3 then #[4,0] else #[6,1])) else (if i.val < 6 then (if i.val < 5 then #[2,22] else #[9,2]) else (if i.val < 7 then #[3,25] else #[12,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[14,4] else #[5,28]) else (if i.val < 11 then #[17,5] else #[18,6])) else (if i.val < 14 then (if i.val < 13 then #[7,30] else #[21,7]) else (if i.val < 15 then #[8,31] else #[20,8])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[19,9] else #[10,18]) else (if i.val < 19 then #[11,29] else #[16,11])) else (if i.val < 22 then (if i.val < 21 then #[15,12] else #[13,14]) else (if i.val < 23 then #[25,15] else #[26,16]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,17] else #[22,19]) else (if i.val < 27 then #[23,20] else #[24,21])) else (if i.val < 30 then (if i.val < 29 then #[31,23] else #[30,24]) else (if i.val < 31 then #[29,26] else #[28,27]))))) : Array (Fin 32))[j.val]!
private def quotientParents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 3 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 5 else 6)) else (if i.val < 14 then (if i.val < 13 then 7 else 7) else (if i.val < 15 then 8 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 10) else (if i.val < 19 then 11 else 11)) else (if i.val < 22 then (if i.val < 21 then 12 else 13) else (if i.val < 23 then 15 else 16))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 17 else 19) else (if i.val < 27 then 20 else 21)) else (if i.val < 30 then (if i.val < 29 then 23 else 24) else (if i.val < 31 then 26 else 27))))) : Fin 32)
private def quotientLetters (i : Fin 32) : Fin 2 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 0 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 0 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 0) else (if i.val < 19 then 0 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 0) else (if i.val < 23 then 1 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 1) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 1 else 1))))) : Fin 2)
private def stepWitness (i : Fin 32) (j : Fin 2) : Fin 2 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,1] else #[1,1]) else (if i.val < 3 then #[1,1] else #[1,1])) else (if i.val < 6 then (if i.val < 5 then #[1,1] else #[1,1]) else (if i.val < 7 then #[1,1] else #[1,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[1,1] else #[1,1]) else (if i.val < 11 then #[1,1] else #[1,1])) else (if i.val < 14 then (if i.val < 13 then #[1,1] else #[1,1]) else (if i.val < 15 then #[1,0] else #[0,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[0,1] else #[1,1]) else (if i.val < 19 then #[1,0] else #[0,1])) else (if i.val < 22 then (if i.val < 21 then #[0,1] else #[1,1]) else (if i.val < 23 then #[1,1] else #[1,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[1,1] else #[1,1]) else (if i.val < 27 then #[1,1] else #[1,1])) else (if i.val < 30 then (if i.val < 29 then #[0,1] else #[0,0]) else (if i.val < 31 then #[0,1] else #[0,0]))))) : Array (Fin 2))[j.val]!
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

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 1) : Equiv.Perm (Fin 8) :=
  literalGenerator0

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 1) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N1

namespace N2
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 29 else 58) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 24 else 29) else (if i.val < 3 then 58 else 63)) : Fin 64)
private def next (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[2,1] else #[3,0]) else (if i.val < 3 then #[0,3] else #[1,2])) : Array (Fin 4))[j.val]!
private def rank (i : Fin 4) : ℕ := (if i.val < 2 then (if i.val < 1 then 3 else 1) else (if i.val < 3 then 2 else 0))
private def parents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 3 else 3)) : Fin 4)
private def letters (i : Fin 4) : Fin 2 := ((if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 0)) : Fin 2)

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

private def posWitness (i : Fin 2) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[1,2] else #[2,1]) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[1,2] else #[2,1]) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 3 else 7)) else (if i.val < 6 then (if i.val < 5 then 35 else 13) else (if i.val < 7 then 39 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 22) else (if i.val < 11 then 11 else 23)) else (if i.val < 14 then (if i.val < 13 then 20 else 21) else (if i.val < 15 then 62 else 30)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 2) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[4,5] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,8] else #[7,9]) else (if i.val < 7 then #[3,10] else #[5,11]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,12] else #[12,0]) else (if i.val < 11 then #[8,13] else #[13,1])) else (if i.val < 14 then (if i.val < 13 then #[9,14] else #[11,15]) else (if i.val < 15 then #[15,4] else #[14,6])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 2) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,9] else #[0,11]) else (if i.val < 3 then #[4,0] else #[6,1])) else (if i.val < 6 then (if i.val < 5 then #[2,14] else #[7,2]) else (if i.val < 7 then #[3,15] else #[5,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,4] else #[12,5]) else (if i.val < 11 then #[8,6] else #[13,7])) else (if i.val < 14 then (if i.val < 13 then #[9,8] else #[11,10]) else (if i.val < 15 then #[15,12] else #[14,13])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 3 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 6 else 7)) else (if i.val < 14 then (if i.val < 13 then 8 else 10) else (if i.val < 15 then 12 else 13)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 2 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 0 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 1)))) : Fin 2)
private def stepWitness (i : Fin 16) (j : Fin 2) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3] else #[3,3]) else (if i.val < 3 then #[3,3] else #[3,3])) else (if i.val < 6 then (if i.val < 5 then #[3,3] else #[1,3]) else (if i.val < 7 then #[3,3] else #[1,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[1,3] else #[2,3]) else (if i.val < 11 then #[1,3] else #[2,3])) else (if i.val < 14 then (if i.val < 13 then #[2,3] else #[2,3]) else (if i.val < 15 then #[3,3] else #[3,3])))) : Array (Fin 4))[j.val]!
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

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N2

namespace N3
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 41 else (if j.val < 2 then 29 else 58)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 11 else 14) else (if i.val < 3 then 24 else 29)) else (if i.val < 6 then (if i.val < 5 then 41 else 44) else (if i.val < 7 then 58 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,4,1] else #[7,5,0]) else (if i.val < 3 then #[1,6,3] else #[0,7,2])) else (if i.val < 6 then (if i.val < 5 then #[2,0,5] else #[3,1,4]) else (if i.val < 7 then #[5,2,7] else #[4,3,6]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 7) else (if i.val < 3 then 4 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 6) else (if i.val < 7 then 3 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 2) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 7 else 4) else (if i.val < 7 then 7 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 2) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[0,3,6] else #[5,6,3]) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[0,3,6] else #[0,6,3]) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 3 else 7)) else (if i.val < 6 then (if i.val < 5 then 35 else 13) else (if i.val < 7 then 39 else 15))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[4,5] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,1] else #[7,6]) else (if i.val < 7 then #[3,0] else #[5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,6] else #[0,4]) else (if i.val < 3 then #[4,0] else #[6,1])) else (if i.val < 6 then (if i.val < 5 then #[2,7] else #[7,2]) else (if i.val < 7 then #[3,5] else #[5,3]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 3 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 2 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 0 else 1))) : Fin 2)
private def stepWitness (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7] else #[7,7]) else (if i.val < 3 then #[7,7] else #[7,7])) else (if i.val < 6 then (if i.val < 5 then #[7,1] else #[3,0]) else (if i.val < 7 then #[7,5] else #[3,4]))) : Array (Fin 8))[j.val]!
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

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N3

namespace N4
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 29 else 58)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 24 else 27) else (if i.val < 3 then 29 else 30)) else (if i.val < 6 then (if i.val < 5 then 57 else 58) else (if i.val < 7 then 60 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,5,2] else #[7,4,3]) else (if i.val < 3 then #[4,7,0] else #[5,6,1])) else (if i.val < 6 then (if i.val < 5 then #[2,1,6] else #[3,0,7]) else (if i.val < 7 then #[0,3,4] else #[1,2,5]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 6 else 1) else (if i.val < 3 then 2 else 5)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 7 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 7) else (if i.val < 3 then 7 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 7) else (if i.val < 7 then 4 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 2) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[1,2,5] else #[3,5,2]) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[1,2,5] else #[4,5,2]) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 3 else 7)) else (if i.val < 6 then (if i.val < 5 then 13 else 15) else (if i.val < 7 then 22 else 23))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[3,4] else #[2,5])) else (if i.val < 6 then (if i.val < 5 then #[5,6] else #[4,7]) else (if i.val < 7 then #[7,0] else #[6,1]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,6] else #[0,7]) else (if i.val < 3 then #[3,0] else #[2,1])) else (if i.val < 6 then (if i.val < 5 then #[5,2] else #[4,3]) else (if i.val < 7 then #[7,4] else #[6,5]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 5))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 2 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 1))) : Fin 2)
private def stepWitness (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7] else #[7,7]) else (if i.val < 3 then #[3,7] else #[3,7])) else (if i.val < 6 then (if i.val < 5 then #[2,7] else #[2,7]) else (if i.val < 7 then #[1,7] else #[1,7]))) : Array (Fin 8))[j.val]!
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

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N4

namespace N5
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 45 else (if j.val < 2 then 27 else 58)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 9 else 10) else (if i.val < 3 then 12 else 15)) else (if i.val < 6 then (if i.val < 5 then 24 else 27) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 40 else 43) else (if i.val < 11 then 45 else 46)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,10,2] else #[13,11,3]) else (if i.val < 3 then #[5,8,0] else #[15,9,1])) else (if i.val < 6 then (if i.val < 5 then #[1,14,6] else #[11,15,7]) else (if i.val < 7 then #[3,12,4] else #[9,13,5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[4,2,10] else #[14,3,11]) else (if i.val < 11 then #[6,0,8] else #[12,1,9])) else (if i.val < 14 then (if i.val < 13 then #[2,6,14] else #[8,7,15]) else (if i.val < 15 then #[0,4,12] else #[10,5,13])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 13) else (if i.val < 3 then 12 else 9)) else (if i.val < 6 then (if i.val < 5 then 11 else 2) else (if i.val < 7 then 4 else 8))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 14) else (if i.val < 11 then 1 else 7)) else (if i.val < 14 then (if i.val < 13 then 10 else 3) else (if i.val < 15 then 15 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 11) else (if i.val < 3 then 0 else 6)) else (if i.val < 6 then (if i.val < 5 then 6 else 15) else (if i.val < 7 then 10 else 5))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 11) else (if i.val < 11 then 15 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 15) else (if i.val < 15 then 12 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 2 else 0)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 2 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 2) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[3,5,13] else #[2,7,6]) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[3,5,13] else #[0,12,6]) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 3 else 7)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[3,1] else #[2,0])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,3] else #[0,2]) else (if i.val < 3 then #[3,0] else #[2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 2 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 2)
private def stepWitness (i : Fin 4) (j : Fin 2) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15] else #[15,15]) else (if i.val < 3 then #[7,3] else #[7,10])) : Array (Fin 16))[j.val]!
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
  generatorCount := 3
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 4
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N5

namespace N6
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 31 else 27) else (if j.val < 3 then 29 else 58)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 24 else 25) else (if i.val < 3 then 26 else 27)) else (if i.val < 6 then (if i.val < 5 then 28 else 29) else (if i.val < 7 then 30 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 56 else 57) else (if i.val < 11 then 58 else 59)) else (if i.val < 14 then (if i.val < 13 then 60 else 61) else (if i.val < 15 then 62 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[8,12,10,5] else #[9,13,11,4]) else (if i.val < 3 then #[10,14,8,7] else #[11,15,9,6])) else (if i.val < 6 then (if i.val < 5 then #[12,8,14,1] else #[13,9,15,0]) else (if i.val < 7 then #[14,10,12,3] else #[15,11,13,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,4,2,13] else #[1,5,3,12]) else (if i.val < 11 then #[2,6,0,15] else #[3,7,1,14])) else (if i.val < 14 then (if i.val < 13 then #[4,0,6,9] else #[5,1,7,8]) else (if i.val < 15 then #[6,2,4,11] else #[7,3,5,10])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 11) else (if i.val < 3 then 7 else 2)) else (if i.val < 6 then (if i.val < 5 then 15 else 3) else (if i.val < 7 then 9 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 8) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 14 else 6) else (if i.val < 15 then 12 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 11) else (if i.val < 3 then 7 else 15)) else (if i.val < 6 then (if i.val < 5 then 1 else 15) else (if i.val < 7 then 3 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 3) else (if i.val < 11 then 15 else 7)) else (if i.val < 14 then (if i.val < 13 then 9 else 7) else (if i.val < 15 then 11 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 2) else (if i.val < 3 then 3 else 1)) else (if i.val < 6 then (if i.val < 5 then 3 else 2) else (if i.val < 7 then 3 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 2) else (if i.val < 11 then 3 else 1)) else (if i.val < 14 then (if i.val < 13 then 3 else 2) else (if i.val < 15 then 3 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 2) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[7,3,5,10] else #[14,6,10,5]) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[7,3,5,10] else #[11,9,10,5]) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 3) else (if i.val < 3 then 13 else 22)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1] else #[1,2]) else (if i.val < 3 then #[2,3] else #[3,0])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,3] else #[1,0]) else (if i.val < 3 then #[2,1] else #[3,2])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 2 := ((if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 1 else 1)) : Fin 2)
private def stepWitness (i : Fin 4) (j : Fin 2) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[7,15] else #[14,15]) else (if i.val < 3 then #[13,15] else #[11,15])) : Array (Fin 16))[j.val]!
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

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N6

namespace N7
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 29 else (if j.val < 2 then 13 else 24)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 13) else (if i.val < 3 then 24 else 29)) else (if i.val < 6 then (if i.val < 5 then 42 else 47) else (if i.val < 7 then 58 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,6,5] else #[5,7,4]) else (if i.val < 3 then #[6,4,7] else #[7,5,6])) else (if i.val < 6 then (if i.val < 5 then #[0,2,1] else #[1,3,0]) else (if i.val < 7 then #[2,0,3] else #[3,1,2]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 2) else (if i.val < 3 then 3 else 1)) else (if i.val < 6 then (if i.val < 5 then 6 else 4) else (if i.val < 7 then 5 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 7) else (if i.val < 3 then 7 else 7)) else (if i.val < 6 then (if i.val < 5 then 1 else 3) else (if i.val < 7 then 3 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 2 else 0)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 2) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[3,5,2] else #[6,1,2]) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[3,5,2] else #[6,1,2]) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 3 else 7)) else (if i.val < 6 then (if i.val < 5 then 35 else 39) else (if i.val < 7 then 9 else 11))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[4,0] else #[5,1])) else (if i.val < 6 then (if i.val < 5 then #[2,6] else #[3,7]) else (if i.val < 7 then #[7,4] else #[6,5]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[4,0] else #[5,1])) else (if i.val < 6 then (if i.val < 5 then #[2,6] else #[3,7]) else (if i.val < 7 then #[7,4] else #[6,5]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 5))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 2 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 1))) : Fin 2)
private def stepWitness (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7] else #[7,7]) else (if i.val < 3 then #[7,1] else #[7,5])) else (if i.val < 6 then (if i.val < 5 then #[7,7] else #[7,7]) else (if i.val < 7 then #[3,0] else #[3,4]))) : Array (Fin 8))[j.val]!
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

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N7

namespace N8
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 41 else (if j.val < 2 then 29 else 13)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 11) else (if i.val < 3 then 13 else 14)) else (if i.val < 6 then (if i.val < 5 then 24 else 27) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 41 else 42) else (if i.val < 11 then 44 else 47)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,9,13] else #[13,8,7]) else (if i.val < 3 then #[5,11,15] else #[15,10,5])) else (if i.val < 6 then (if i.val < 5 then #[3,13,9] else #[9,12,3]) else (if i.val < 7 then #[1,15,11] else #[11,14,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[4,1,14] else #[14,0,4]) else (if i.val < 11 then #[6,3,12] else #[12,2,6])) else (if i.val < 14 then (if i.val < 13 then #[0,5,10] else #[10,4,0]) else (if i.val < 15 then #[2,7,8] else #[8,6,2])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 5) else (if i.val < 3 then 3 else 9)) else (if i.val < 6 then (if i.val < 5 then 4 else 8) else (if i.val < 7 then 2 else 12))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 11) else (if i.val < 11 then 14 else 7)) else (if i.val < 14 then (if i.val < 13 then 13 else 10) else (if i.val < 15 then 6 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 8) else (if i.val < 3 then 15 else 4)) else (if i.val < 6 then (if i.val < 5 then 8 else 2) else (if i.val < 7 then 15 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 4) else (if i.val < 11 then 3 else 6)) else (if i.val < 14 then (if i.val < 13 then 11 else 4) else (if i.val < 15 then 8 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 2 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 2) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 2 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 2) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[1,6,11] else #[10,13,2]) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[1,6,11] else #[1,13,2]) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 3 else 7)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[3,0] else #[2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[3,0] else #[2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 2 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 2)
private def stepWitness (i : Fin 4) (j : Fin 2) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15] else #[15,15]) else (if i.val < 3 then #[7,2] else #[7,11])) : Array (Fin 16))[j.val]!
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
  generatorCount := 3
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 4
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N8

namespace N9
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 35 else (if j.val < 2 then 29 else 13)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 8 else 11) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 18) else (if i.val < 11 then 20 else 23)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 35) else (if i.val < 19 then 37 else 38)) else (if i.val < 22 then (if i.val < 21 then 41 else 42) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 51) else (if i.val < 27 then 53 else 54)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[22,17,27] else #[6,16,9]) else (if i.val < 3 then #[7,19,25] else #[23,18,11])) else (if i.val < 6 then (if i.val < 5 then #[10,21,29] else #[26,20,15]) else (if i.val < 7 then #[27,23,31] else #[11,22,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[30,25,19] else #[14,24,1]) else (if i.val < 11 then #[15,27,17] else #[31,26,3])) else (if i.val < 14 then (if i.val < 13 then #[2,29,21] else #[18,28,7]) else (if i.val < 15 then #[19,31,23] else #[3,30,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[4,1,24] else #[20,0,10]) else (if i.val < 19 then #[21,3,26] else #[5,2,8])) else (if i.val < 22 then (if i.val < 21 then #[24,5,30] else #[8,4,12]) else (if i.val < 23 then #[9,7,28] else #[25,6,14]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[12,9,16] else #[28,8,2]) else (if i.val < 27 then #[29,11,18] else #[13,10,0])) else (if i.val < 30 then (if i.val < 29 then #[16,13,22] else #[0,12,4]) else (if i.val < 31 then #[1,15,20] else #[17,14,6]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 23) else (if i.val < 3 then 15 else 26)) else (if i.val < 6 then (if i.val < 5 then 30 else 11) else (if i.val < 7 then 3 else 24))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 20) else (if i.val < 11 then 6 else 31)) else (if i.val < 14 then (if i.val < 13 then 19 else 18) else (if i.val < 15 then 2 else 14)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 1) else (if i.val < 19 then 27 else 7)) else (if i.val < 22 then (if i.val < 21 then 4 else 29) else (if i.val < 23 then 13 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 10 else 17) else (if i.val < 27 then 22 else 9)) else (if i.val < 30 then (if i.val < 29 then 25 else 28) else (if i.val < 31 then 12 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 17 else 30) else (if i.val < 3 then 19 else 15)) else (if i.val < 6 then (if i.val < 5 then 16 else 20) else (if i.val < 7 then 31 else 22))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 19 else 24) else (if i.val < 11 then 17 else 26)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 31 else 10)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 24 else 31) else (if i.val < 19 then 13 else 14)) else (if i.val < 22 then (if i.val < 21 then 17 else 12) else (if i.val < 23 then 0 else 14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 20 else 23) else (if i.val < 27 then 5 else 6)) else (if i.val < 30 then (if i.val < 29 then 22 else 12) else (if i.val < 31 then 20 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 1) else (if i.val < 11 then 2 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 1 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 0) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 2) else (if i.val < 23 then 0 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 2 else 1) else (if i.val < 31 then 2 else 0))))) : Fin 3)

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

private def posWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[3,14,23] else #[1,29,6]) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[3,14,23] else #[3,29,6]) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 31) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 2) : Fin 2 := ((if i.val < 1 then #[1,1] else #[0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 2) : Fin 2 := ((if i.val < 1 then #[1,1] else #[0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def stepWitness (i : Fin 2) (j : Fin 2) : Fin 32 := ((if i.val < 1 then #[31,11] else #[31,27]) : Array (Fin 32))[j.val]!
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
  generatorCount := 3
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 2
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N9

namespace N10
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 41 else 31) else (if j.val < 3 then 29 else 13)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 9) else (if i.val < 3 then 10 else 11)) else (if i.val < 6 then (if i.val < 5 then 12 else 13) else (if i.val < 7 then 14 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 25) else (if i.val < 11 then 26 else 27)) else (if i.val < 14 then (if i.val < 13 then 28 else 29) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 40 else 41) else (if i.val < 19 then 42 else 43)) else (if i.val < 22 then (if i.val < 21 then 44 else 45) else (if i.val < 23 then 46 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 4) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[14,16,18,26] else #[10,17,19,30]) else (if i.val < 3 then #[30,18,16,10] else #[26,19,17,14])) else (if i.val < 6 then (if i.val < 5 then #[15,20,22,27] else #[11,21,23,31]) else (if i.val < 7 then #[31,22,20,11] else #[27,23,21,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[6,24,26,18] else #[2,25,27,22]) else (if i.val < 11 then #[22,26,24,2] else #[18,27,25,6])) else (if i.val < 14 then (if i.val < 13 then #[7,28,30,19] else #[3,29,31,23]) else (if i.val < 15 then #[23,30,28,3] else #[19,31,29,7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[12,0,2,24] else #[8,1,3,28]) else (if i.val < 19 then #[28,2,0,8] else #[24,3,1,12])) else (if i.val < 22 then (if i.val < 21 then #[13,4,6,25] else #[9,5,7,29]) else (if i.val < 23 then #[29,6,4,9] else #[25,7,5,13]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[4,8,10,16] else #[0,9,11,20]) else (if i.val < 27 then #[20,10,8,0] else #[16,11,9,4])) else (if i.val < 30 then (if i.val < 29 then #[5,12,14,17] else #[1,13,15,21]) else (if i.val < 31 then #[21,14,12,1] else #[17,15,13,5]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 6) else (if i.val < 3 then 31 else 7)) else (if i.val < 6 then (if i.val < 5 then 28 else 4) else (if i.val < 7 then 15 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 25) else (if i.val < 11 then 19 else 13)) else (if i.val < 14 then (if i.val < 13 then 22 else 3) else (if i.val < 15 then 21 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 29 else 1) else (if i.val < 19 then 18 else 9)) else (if i.val < 22 then (if i.val < 21 then 27 else 14) else (if i.val < 23 then 26 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 16 else 24) else (if i.val < 27 then 17 else 23)) else (if i.val < 30 then (if i.val < 29 then 8 else 10) else (if i.val < 31 then 20 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 17) else (if i.val < 3 then 18 else 17)) else (if i.val < 6 then (if i.val < 5 then 24 else 31) else (if i.val < 7 then 8 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 21) else (if i.val < 11 then 1 else 5)) else (if i.val < 14 then (if i.val < 13 then 28 else 31) else (if i.val < 15 then 3 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 24 else 31) else (if i.val < 19 then 8 else 15)) else (if i.val < 22 then (if i.val < 21 then 6 else 5) else (if i.val < 23 then 6 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 8 else 23) else (if i.val < 27 then 8 else 7)) else (if i.val < 30 then (if i.val < 29 then 17 else 15) else (if i.val < 31 then 1 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 4 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 1) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 3) else (if i.val < 7 then 0 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 3 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 0) else (if i.val < 19 then 3 else 0)) else (if i.val < 22 then (if i.val < 21 then 2 else 1) else (if i.val < 23 then 1 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 0) else (if i.val < 27 then 2 else 0)) else (if i.val < 30 then (if i.val < 29 then 3 else 2) else (if i.val < 31 then 3 else 0))))) : Fin 4)

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

private def posWitness (i : Fin 2) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[3,15,13,23] else #[20,30,26,5]) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[3,15,13,23] else #[3,27,26,5]) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 3) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 2) : Fin 2 := ((if i.val < 1 then #[0,1] else #[1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 2) : Fin 2 := ((if i.val < 1 then #[0,1] else #[1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 1) : Fin 2)
private def stepWitness (i : Fin 2) (j : Fin 2) : Fin 32 := ((if i.val < 1 then #[15,31] else #[30,5]) : Array (Fin 32))[j.val]!
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
  generatorCount := 4
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 2
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N10

namespace N11
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 3 else 27) else (if j.val < 3 then 29 else 8)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 8 else 11) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 34) else (if i.val < 19 then 36 else 39)) else (if i.val < 22 then (if i.val < 21 then 41 else 42) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 50) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 4) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[22,18,17,27] else #[6,19,16,9]) else (if i.val < 3 then #[7,16,19,25] else #[23,17,18,11])) else (if i.val < 6 then (if i.val < 5 then #[26,22,21,31] else #[10,23,20,13]) else (if i.val < 7 then #[11,20,23,29] else #[27,21,22,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[30,26,25,19] else #[14,27,24,1]) else (if i.val < 11 then #[15,24,27,17] else #[31,25,26,3])) else (if i.val < 14 then (if i.val < 13 then #[18,30,29,23] else #[2,31,28,5]) else (if i.val < 15 then #[3,28,31,21] else #[19,29,30,7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[4,2,1,24] else #[20,3,0,10]) else (if i.val < 19 then #[21,0,3,26] else #[5,1,2,8])) else (if i.val < 22 then (if i.val < 21 then #[8,6,5,28] else #[24,7,4,14]) else (if i.val < 23 then #[25,4,7,30] else #[9,5,6,12]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[12,10,9,16] else #[28,11,8,2]) else (if i.val < 27 then #[29,8,11,18] else #[13,9,10,0])) else (if i.val < 30 then (if i.val < 29 then #[0,14,13,20] else #[16,15,12,6]) else (if i.val < 31 then #[17,12,15,22] else #[1,13,14,4]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 25 else 1) else (if i.val < 3 then 9 else 12)) else (if i.val < 6 then (if i.val < 5 then 4 else 11) else (if i.val < 7 then 5 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 20 else 8) else (if i.val < 11 then 26 else 16)) else (if i.val < 14 then (if i.val < 13 then 30 else 2) else (if i.val < 15 then 3 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 7 else 27) else (if i.val < 19 then 28 else 6)) else (if i.val < 22 then (if i.val < 21 then 17 else 13) else (if i.val < 23 then 15 else 18))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 24) else (if i.val < 27 then 14 else 22)) else (if i.val < 30 then (if i.val < 29 then 10 else 19) else (if i.val < 31 then 29 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 28 else 31) else (if i.val < 3 then 13 else 14)) else (if i.val < 6 then (if i.val < 5 then 31 else 13) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 19 else 1) else (if i.val < 11 then 5 else 6)) else (if i.val < 14 then (if i.val < 13 then 23 else 31) else (if i.val < 15 then 31 else 29)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 3) else (if i.val < 19 then 3 else 1)) else (if i.val < 22 then (if i.val < 21 then 6 else 14) else (if i.val < 23 then 4 else 6))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 16 else 2) else (if i.val < 27 then 4 else 9)) else (if i.val < 30 then (if i.val < 29 then 13 else 6) else (if i.val < 31 then 22 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 4 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 3 else 3) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 3 else 1) else (if i.val < 15 then 2 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 1) else (if i.val < 19 then 2 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 3) else (if i.val < 23 then 1 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 3) else (if i.val < 27 then 0 else 1)) else (if i.val < 30 then (if i.val < 29 then 2 else 3) else (if i.val < 31 then 3 else 0))))) : Fin 4)

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

private def posWitness (i : Fin 2) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[19,13,14,21] else #[1,15,29,23]) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[19,13,14,21] else #[1,28,29,23]) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 31) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 2) : Fin 2 := ((if i.val < 1 then #[1,0] else #[0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 2) : Fin 2 := ((if i.val < 1 then #[1,0] else #[0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def stepWitness (i : Fin 2) (j : Fin 2) : Fin 32 := ((if i.val < 1 then #[31,11] else #[31,27]) : Array (Fin 32))[j.val]!
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
  generatorCount := 4
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 2
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N11

namespace N12
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 3 else 31) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63)))))) : Fin 64)
private def next (i : Fin 64) (j : Fin 2) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[44,32] else #[12,33]) else (if i.val < 3 then #[45,34] else #[13,35])) else (if i.val < 6 then (if i.val < 5 then #[46,36] else #[14,37]) else (if i.val < 7 then #[47,38] else #[15,39]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[52,40] else #[20,41]) else (if i.val < 11 then #[53,42] else #[21,43])) else (if i.val < 14 then (if i.val < 13 then #[54,44] else #[22,45]) else (if i.val < 15 then #[55,46] else #[23,47])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[60,48] else #[28,49]) else (if i.val < 19 then #[61,50] else #[29,51])) else (if i.val < 22 then (if i.val < 21 then #[62,52] else #[30,53]) else (if i.val < 23 then #[63,54] else #[31,55]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[36,56] else #[4,57]) else (if i.val < 27 then #[37,58] else #[5,59])) else (if i.val < 30 then (if i.val < 29 then #[38,60] else #[6,61]) else (if i.val < 31 then #[39,62] else #[7,63]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[40,0] else #[8,1]) else (if i.val < 35 then #[41,2] else #[9,3])) else (if i.val < 38 then (if i.val < 37 then #[42,4] else #[10,5]) else (if i.val < 39 then #[43,6] else #[11,7]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[48,8] else #[16,9]) else (if i.val < 43 then #[49,10] else #[17,11])) else (if i.val < 46 then (if i.val < 45 then #[50,12] else #[18,13]) else (if i.val < 47 then #[51,14] else #[19,15])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[56,16] else #[24,17]) else (if i.val < 51 then #[57,18] else #[25,19])) else (if i.val < 54 then (if i.val < 53 then #[58,20] else #[26,21]) else (if i.val < 55 then #[59,22] else #[27,23]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[32,24] else #[0,25]) else (if i.val < 59 then #[33,26] else #[1,27])) else (if i.val < 62 then (if i.val < 61 then #[34,28] else #[2,29]) else (if i.val < 63 then #[35,30] else #[3,31])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 45 else 28) else (if i.val < 3 then 30 else 1)) else (if i.val < 6 then (if i.val < 5 then 57 else 42) else (if i.val < 7 then 44 else 5))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 52 else 8) else (if i.val < 11 then 61 else 17)) else (if i.val < 14 then (if i.val < 13 then 40 else 3) else (if i.val < 15 then 53 else 9)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 23 else 39) else (if i.val < 19 then 12 else 25)) else (if i.val < 22 then (if i.val < 21 then 13 else 26) else (if i.val < 23 then 6 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 58 else 46) else (if i.val < 27 then 47 else 29)) else (if i.val < 30 then (if i.val < 29 then 48 else 31) else (if i.val < 31 then 33 else 2))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 56 else 41) else (if i.val < 35 then 43 else 4)) else (if i.val < 38 then (if i.val < 37 then 62 else 54) else (if i.val < 39 then 55 else 10))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 59 else 14) else (if i.val < 43 then 63 else 27)) else (if i.val < 46 then (if i.val < 45 then 51 else 7) else (if i.val < 47 then 60 else 16)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 36 else 50) else (if i.val < 51 then 20 else 37)) else (if i.val < 54 then (if i.val < 53 then 22 else 38) else (if i.val < 55 then 11 else 24))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 32) else (if i.val < 59 then 34 else 18)) else (if i.val < 62 then (if i.val < 61 then 35 else 19) else (if i.val < 63 then 21 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 59) else (if i.val < 3 then 61 else 63)) else (if i.val < 6 then (if i.val < 5 then 25 else 27) else (if i.val < 7 then 29 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 33 else 35) else (if i.val < 11 then 37 else 39)) else (if i.val < 14 then (if i.val < 13 then 1 else 3) else (if i.val < 15 then 5 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 41 else 43) else (if i.val < 19 then 45 else 47)) else (if i.val < 22 then (if i.val < 21 then 9 else 11) else (if i.val < 23 then 13 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 1) else (if i.val < 35 then 2 else 3)) else (if i.val < 38 then (if i.val < 37 then 4 else 5) else (if i.val < 39 then 6 else 7))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 8 else 9) else (if i.val < 43 then 10 else 11)) else (if i.val < 46 then (if i.val < 45 then 12 else 13) else (if i.val < 47 then 14 else 15)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 17) else (if i.val < 51 then 18 else 19)) else (if i.val < 54 then (if i.val < 53 then 20 else 21) else (if i.val < 55 then 22 else 23))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 48 else 50) else (if i.val < 59 then 52 else 54)) else (if i.val < 62 then (if i.val < 61 then 16 else 18) else (if i.val < 63 then 20 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 2 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 1) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 1 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 1 else 1) else (if i.val < 35 then 1 else 1)) else (if i.val < 38 then (if i.val < 37 then 1 else 1) else (if i.val < 39 then 1 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 1 else 1) else (if i.val < 43 then 1 else 1)) else (if i.val < 46 then (if i.val < 45 then 1 else 1) else (if i.val < 47 then 1 else 1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 1 else 1) else (if i.val < 51 then 1 else 1)) else (if i.val < 54 then (if i.val < 53 then 1 else 1) else (if i.val < 55 then 1 else 1))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 0) else (if i.val < 59 then 0 else 0)) else (if i.val < 62 then (if i.val < 61 then 0 else 0) else (if i.val < 63 then 0 else 0)))))) : Fin 2)

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

private def posWitness (i : Fin 2) (j : Fin 2) : Fin 64 := ((if i.val < 1 then #[39,31] else #[3,62]) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 2) (j : Fin 2) : Fin 64 := ((if i.val < 1 then #[39,31] else #[3,59]) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 1) : Source := ⟨(63 : Fin 64)⟩
private def quotientNext (i : Fin 1) (j : Fin 2) : Fin 1 := (#[0,0] : Array (Fin 1))[j.val]!
private def quotientPrev (i : Fin 1) (j : Fin 2) : Fin 1 := (#[0,0] : Array (Fin 1))[j.val]!
private def quotientParents (i : Fin 1) : Fin 1 := (0 : Fin 1)
private def quotientLetters (i : Fin 1) : Fin 2 := (0 : Fin 2)
private def stepWitness (i : Fin 1) (j : Fin 2) : Fin 64 := (#[31,22] : Array (Fin 64))[j.val]!
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
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 1
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N12

@[reducible] def states (i : Fin 13) : BinaryNormalState generators :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then N0.state else (if i.val < 2 then N1.state else N2.state)) else (if i.val < 4 then N3.state else (if i.val < 5 then N4.state else N5.state))) else (if i.val < 9 then (if i.val < 7 then N6.state else (if i.val < 8 then N7.state else N8.state)) else (if i.val < 11 then (if i.val < 10 then N9.state else N10.state) else (if i.val < 12 then N11.state else N12.state))))

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
