import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T26

/-! Exact original normal states and quotient rows for 8T26.
Selected by export_lean_carrier_normal_registry_selected.py; all finite facts are checked
in Lean's kernel. This file certifies normal-state coverage, not the later
pair/character/transport acceptance of those states. -/

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T26

abbrev Source := FiniteGroupRow 64
local instance selectedStateSourceGroup : Group Source := BinaryMenuCayley8T26.group

def generators (j : Fin 3) : Source :=
  ⟨BinaryMenuCayley8T26.certificate.next BinaryMenuCayley8T26.certificate.identity j⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  apply binaryNormal_full_generators_of_equiv BinaryMenuCayley8T26.generators
    generators BinaryMenuCayley8T26.originalEquiv
  intro j
  change BinaryMenuCayley8T26.certificate.toCayley.elements
    (BinaryMenuCayley8T26.certificate.toCayley.next
      BinaryMenuCayley8T26.certificate.toCayley.identity j)=_
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

private def representatives (i : Fin 64) : Source := ⟨((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 9 else 39) else (if i.val < 7 then 33 else 35))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 61 else 50) else (if i.val < 11 then 57 else 16)) else (if i.val < 14 then (if i.val < 13 then 41 else 43) else (if i.val < 15 then 45 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 60 else 1) else (if i.val < 19 then 12 else 3)) else (if i.val < 22 then (if i.val < 21 then 55 else 29) else (if i.val < 23 then 14 else 18))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 27) else (if i.val < 27 then 26 else 48)) else (if i.val < 30 then (if i.val < 29 then 52 else 15) else (if i.val < 31 then 4 else 11))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 21 else 13) else (if i.val < 35 then 37 else 23)) else (if i.val < 38 then (if i.val < 37 then 28 else 24) else (if i.val < 39 then 17 else 44))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 42 else 40) else (if i.val < 43 then 19 else 59)) else (if i.val < 46 then (if i.val < 45 then 46 else 54) else (if i.val < 47 then 2 else 34)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 58 else 62) else (if i.val < 51 then 20 else 47)) else (if i.val < 54 then (if i.val < 53 then 36 else 32) else (if i.val < 55 then 53 else 51))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 56) else (if i.val < 59 then 10 else 8)) else (if i.val < 62 then (if i.val < 61 then 38 else 6) else (if i.val < 63 then 30 else 0)))))) : Fin 64)⟩
private def quotientNext (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[4,5,6]) else (if i.val < 3 then #[7,0,8] else #[9,10,0])) else (if i.val < 6 then (if i.val < 5 then #[11,12,13] else #[14,1,15]) else (if i.val < 7 then #[16,17,1] else #[18,19,17]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[20,21,2] else #[22,23,11]) else (if i.val < 11 then #[24,3,25] else #[26,27,9])) else (if i.val < 14 then (if i.val < 13 then #[28,4,29] else #[30,31,4]) else (if i.val < 15 then #[32,33,31] else #[10,34,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[35,36,26] else #[37,6,7]) else (if i.val < 19 then #[38,39,40] else #[41,7,34])) else (if i.val < 22 then (if i.val < 21 then #[29,35,38] else #[42,8,43]) else (if i.val < 23 then #[6,44,39] else #[40,9,28]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[31,45,27] else #[46,43,10]) else (if i.val < 27 then #[47,48,16] else #[49,11,24])) else (if i.val < 30 then (if i.val < 29 then #[2,50,23] else #[17,51,12]) else (if i.val < 31 then #[3,52,47] else #[53,13,14]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[25,54,55] else #[56,14,51]) else (if i.val < 35 then #[21,15,19] else #[13,20,54])) else (if i.val < 38 then (if i.val < 37 then #[55,16,49] else #[23,57,48]) else (if i.val < 39 then #[48,56,20] else #[54,18,22]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[52,58,18] else #[50,59,58]) else (if i.val < 43 then #[58,55,56] else #[60,25,21])) else (if i.val < 46 then (if i.val < 45 then #[15,22,59] else #[51,24,50]) else (if i.val < 47 then #[59,47,53] else #[39,46,30])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[61,26,37] else #[5,62,36]) else (if i.val < 51 then #[43,28,45] else #[34,29,33])) else (if i.val < 54 then (if i.val < 53 then #[8,30,61] else #[36,63,46]) else (if i.val < 55 then #[0,32,35] else #[44,42,32]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[62,38,42] else #[45,37,62]) else (if i.val < 59 then #[63,40,41] else #[27,41,44])) else (if i.val < 62 then (if i.val < 61 then #[33,61,63] else #[12,60,52]) else (if i.val < 63 then #[19,49,57] else #[57,53,60])))))) : Array (Fin 64))[j.val]!
private def quotientPrev (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[54,2,3] else #[0,5,6]) else (if i.val < 3 then #[28,0,8] else #[30,10,0])) else (if i.val < 6 then (if i.val < 5 then #[1,12,13] else #[49,1,15]) else (if i.val < 7 then #[22,17,1] else #[2,19,17]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[52,21,2] else #[3,23,11]) else (if i.val < 11 then #[15,3,25] else #[4,27,9])) else (if i.val < 14 then (if i.val < 13 then #[61,4,29] else #[35,31,4]) else (if i.val < 15 then #[5,33,31] else #[44,34,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[6,36,26] else #[29,6,7]) else (if i.val < 19 then #[7,39,40] else #[62,7,34])) else (if i.val < 22 then (if i.val < 21 then #[8,35,38] else #[34,8,43]) else (if i.val < 23 then #[9,44,39] else #[37,9,28]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[10,45,27] else #[32,43,10]) else (if i.val < 27 then #[11,48,16] else #[59,11,24])) else (if i.val < 30 then (if i.val < 29 then #[12,50,23] else #[20,51,12]) else (if i.val < 31 then #[13,52,47] else #[24,13,14]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[14,54,55] else #[60,14,51]) else (if i.val < 35 then #[51,15,19] else #[16,20,54])) else (if i.val < 38 then (if i.val < 37 then #[53,16,49] else #[17,57,48]) else (if i.val < 39 then #[18,56,20] else #[47,18,22]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[23,58,18] else #[19,59,58]) else (if i.val < 43 then #[21,55,56] else #[50,25,21])) else (if i.val < 46 then (if i.val < 45 then #[55,22,59] else #[57,24,50]) else (if i.val < 47 then #[25,47,53] else #[26,46,30])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[38,26,37] else #[27,62,36]) else (if i.val < 51 then #[41,28,45] else #[45,29,33])) else (if i.val < 54 then (if i.val < 53 then #[40,30,61] else #[31,63,46]) else (if i.val < 55 then #[39,32,35] else #[36,42,32]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[33,38,42] else #[63,37,62]) else (if i.val < 59 then #[42,40,41] else #[46,41,44])) else (if i.val < 62 then (if i.val < 61 then #[43,61,63] else #[48,60,52]) else (if i.val < 63 then #[56,49,57] else #[58,53,60])))))) : Array (Fin 64))[j.val]!
private def quotientParents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 3 else 4)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 5 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 6) else (if i.val < 19 then 7 else 7)) else (if i.val < 22 then (if i.val < 21 then 8 else 8) else (if i.val < 23 then 9 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 10 else 10) else (if i.val < 27 then 11 else 11)) else (if i.val < 30 then (if i.val < 29 then 12 else 12) else (if i.val < 31 then 13 else 13))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 14 else 14) else (if i.val < 35 then 15 else 16)) else (if i.val < 38 then (if i.val < 37 then 16 else 17) else (if i.val < 39 then 18 else 18))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 18 else 19) else (if i.val < 43 then 21 else 21)) else (if i.val < 46 then (if i.val < 45 then 22 else 24) else (if i.val < 47 then 25 else 26)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 26 else 27) else (if i.val < 51 then 28 else 29)) else (if i.val < 54 then (if i.val < 53 then 30 else 31) else (if i.val < 55 then 32 else 32))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 33 else 37) else (if i.val < 59 then 40 else 41)) else (if i.val < 62 then (if i.val < 61 then 43 else 48) else (if i.val < 63 then 49 else 53)))))) : Fin 64)
private def quotientLetters (i : Fin 64) : Fin 3 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 0) else (if i.val < 11 then 1 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 0 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 1) else (if i.val < 19 then 0 else 1)) else (if i.val < 22 then (if i.val < 21 then 0 else 1) else (if i.val < 23 then 0 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 2) else (if i.val < 27 then 0 else 1)) else (if i.val < 30 then (if i.val < 29 then 0 else 2) else (if i.val < 31 then 0 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 1) else (if i.val < 35 then 1 else 0)) else (if i.val < 38 then (if i.val < 37 then 1 else 0) else (if i.val < 39 then 0 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 2 else 0) else (if i.val < 43 then 0 else 2)) else (if i.val < 46 then (if i.val < 45 then 1 else 1) else (if i.val < 47 then 0 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 1 else 0) else (if i.val < 51 then 1 else 1)) else (if i.val < 54 then (if i.val < 53 then 1 else 0) else (if i.val < 55 then 1 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 1) else (if i.val < 59 then 1 else 1)) else (if i.val < 62 then (if i.val < 61 then 0 else 0) else (if i.val < 63 then 1 else 1)))))) : Fin 3)
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

def literalNormalGenerators (k : Fin 0) : Equiv.Perm (Fin 8) :=
  Fin.elim0 k

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 0) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  exact Fin.elim0 k

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

private def representatives (i : Fin 32) : Source := ⟨((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 9 else 39) else (if i.val < 7 then 33 else 35))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 61 else 50) else (if i.val < 11 then 57 else 16)) else (if i.val < 14 then (if i.val < 13 then 41 else 43) else (if i.val < 15 then 45 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 3) else (if i.val < 19 then 55 else 29)) else (if i.val < 22 then (if i.val < 21 then 22 else 27) else (if i.val < 23 then 48 else 52))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 15 else 11) else (if i.val < 27 then 13 else 37)) else (if i.val < 30 then (if i.val < 29 then 19 else 59) else (if i.val < 31 then 20 else 47))))) : Fin 64)⟩
private def quotientNext (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[4,5,6]) else (if i.val < 3 then #[7,0,8] else #[9,10,0])) else (if i.val < 6 then (if i.val < 5 then #[11,12,13] else #[14,1,15]) else (if i.val < 7 then #[3,16,1] else #[12,17,16]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[18,19,2] else #[13,18,11]) else (if i.val < 11 then #[20,3,21] else #[0,22,9])) else (if i.val < 14 then (if i.val < 13 then #[23,4,24] else #[6,25,4]) else (if i.val < 15 then #[22,26,25] else #[10,27,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[8,6,7] else #[26,7,27]) else (if i.val < 19 then #[24,9,23] else #[28,8,29])) else (if i.val < 22 then (if i.val < 21 then #[25,28,22] else #[5,29,10]) else (if i.val < 23 then #[21,11,20] else #[2,30,18]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[16,31,12] else #[15,13,14]) else (if i.val < 27 then #[30,14,31] else #[19,15,17])) else (if i.val < 30 then (if i.val < 29 then #[31,20,30] else #[17,21,19]) else (if i.val < 31 then #[29,23,28] else #[27,24,26]))))) : Array (Fin 32))[j.val]!
private def quotientPrev (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,2,3] else #[0,5,6]) else (if i.val < 3 then #[23,0,8] else #[6,10,0])) else (if i.val < 6 then (if i.val < 5 then #[1,12,13] else #[21,1,15]) else (if i.val < 7 then #[13,16,1] else #[2,17,16]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[16,19,2] else #[3,18,11]) else (if i.val < 11 then #[15,3,21] else #[4,22,9])) else (if i.val < 14 then (if i.val < 13 then #[7,4,24] else #[9,25,4]) else (if i.val < 15 then #[5,26,25] else #[25,27,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[24,6,7] else #[29,7,27]) else (if i.val < 19 then #[8,9,23] else #[27,8,29])) else (if i.val < 22 then (if i.val < 21 then #[10,28,22] else #[22,29,10]) else (if i.val < 23 then #[14,11,20] else #[12,30,18]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,31,12] else #[20,13,14]) else (if i.val < 27 then #[17,14,31] else #[31,15,17])) else (if i.val < 30 then (if i.val < 29 then #[19,20,30] else #[30,21,19]) else (if i.val < 31 then #[26,23,28] else #[28,24,26]))))) : Array (Fin 32))[j.val]!
private def quotientParents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 3 else 4)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 5 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 7) else (if i.val < 19 then 8 else 8)) else (if i.val < 22 then (if i.val < 21 then 10 else 10) else (if i.val < 23 then 11 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 13) else (if i.val < 27 then 14 else 15)) else (if i.val < 30 then (if i.val < 29 then 19 else 19) else (if i.val < 31 then 23 else 24))))) : Fin 32)
private def quotientLetters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 0) else (if i.val < 11 then 1 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 0 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 1) else (if i.val < 19 then 0 else 1)) else (if i.val < 22 then (if i.val < 21 then 0 else 2) else (if i.val < 23 then 1 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 1) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 0 else 2) else (if i.val < 31 then 1 else 1))))) : Fin 3)
private def stepWitness (i : Fin 32) (j : Fin 3) : Fin 2 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,1,1] else #[1,1,1]) else (if i.val < 3 then #[1,1,1] else #[1,1,1])) else (if i.val < 6 then (if i.val < 5 then #[1,1,1] else #[1,1,1]) else (if i.val < 7 then #[0,1,1] else #[0,1,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[1,1,1] else #[0,0,1]) else (if i.val < 11 then #[1,1,1] else #[0,1,1])) else (if i.val < 14 then (if i.val < 13 then #[1,1,1] else #[0,1,1]) else (if i.val < 15 then #[0,1,1] else #[1,1,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[0,1,1] else #[0,1,1]) else (if i.val < 19 then #[1,0,0] else #[1,1,1])) else (if i.val < 22 then (if i.val < 21 then #[1,0,1] else #[0,1,1]) else (if i.val < 23 then #[0,1,1] else #[1,1,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[1,1,1] else #[0,1,1]) else (if i.val < 27 then #[0,1,1] else #[1,1,1])) else (if i.val < 30 then (if i.val < 29 then #[0,0,0] else #[0,1,1]) else (if i.val < 31 then #[1,1,0] else #[1,1,1]))))) : Array (Fin 2))[j.val]!
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 1) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N1

namespace N2
def normalGenerators (j : Fin 1) : Source := ⟨(40 : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 13 else 26) else (if i.val < 3 then 40 else 63)) : Fin 64)
private def next (i : Fin 4) (j : Fin 1) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[3] else #[0]) else (if i.val < 3 then #[1] else #[2])) : Array (Fin 4))[j.val]!
private def rank (i : Fin 4) : ℕ := (if i.val < 2 then (if i.val < 1 then 3 else 2) else (if i.val < 3 then 1 else 0))
private def parents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 3 else 3)) : Fin 4)
private def letters (i : Fin 4) : Fin 1 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) : Fin 1)

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

private def posWitness (i : Fin 3) (j : Fin 1) : Fin 4 := ((if i.val < 1 then #[0] else (if i.val < 2 then #[0] else #[0])) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 1) : Fin 4 := ((if i.val < 1 then #[0] else (if i.val < 2 then #[0] else #[0])) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 9 else 39) else (if i.val < 7 then 33 else 35))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 61 else 50) else (if i.val < 11 then 57 else 16)) else (if i.val < 14 then (if i.val < 13 then 41 else 43) else (if i.val < 15 then 5 else 1)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[4,5,6]) else (if i.val < 3 then #[7,0,8] else #[9,10,0])) else (if i.val < 6 then (if i.val < 5 then #[11,12,13] else #[2,1,14]) else (if i.val < 7 then #[3,15,1] else #[12,11,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[14,13,2] else #[13,14,11]) else (if i.val < 11 then #[15,3,12] else #[0,7,9])) else (if i.val < 14 then (if i.val < 13 then #[5,4,10] else #[6,8,4]) else (if i.val < 15 then #[10,9,5] else #[8,6,7])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,2,3] else #[0,5,6]) else (if i.val < 3 then #[5,0,8] else #[6,10,0])) else (if i.val < 6 then (if i.val < 5 then #[1,12,13] else #[12,1,14]) else (if i.val < 7 then #[13,15,1] else #[2,11,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[15,13,2] else #[3,14,11]) else (if i.val < 11 then #[14,3,12] else #[4,7,9])) else (if i.val < 14 then (if i.val < 13 then #[7,4,10] else #[9,8,4]) else (if i.val < 15 then #[8,9,5] else #[10,6,7])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 3 else 4)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 5 else 6)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 0) else (if i.val < 11 then 1 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 2 else 1)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3,3] else #[3,3,3]) else (if i.val < 3 then #[3,3,3] else #[3,3,3])) else (if i.val < 6 then (if i.val < 5 then #[3,3,3] else #[2,3,3]) else (if i.val < 7 then #[1,3,3] else #[1,2,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,0,3] else #[1,0,3]) else (if i.val < 11 then #[0,3,0] else #[1,0,3])) else (if i.val < 14 then (if i.val < 13 then #[0,3,2] else #[1,2,3]) else (if i.val < 15 then #[3,2,3] else #[1,3,3])))) : Array (Fin 4))[j.val]!
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
  generatorCount := 1
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 16
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 1) : Equiv.Perm (Fin 8) :=
  literalGenerator0

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 1) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N2

namespace N3
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 30 else 26) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 26 else 30) else (if i.val < 3 then 59 else 63)) : Fin 64)
private def next (i : Fin 4) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[2,3] else #[3,2]) else (if i.val < 3 then #[0,1] else #[1,0])) : Array (Fin 4))[j.val]!
private def rank (i : Fin 4) : ℕ := (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 3 else 0))
private def parents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 1 else 3)) : Fin 4)
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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[2,0] else (if i.val < 2 then #[1,0] else #[1,0])) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[2,0] else (if i.val < 2 then #[1,0] else #[1,0])) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 9 else 39) else (if i.val < 7 then 33 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 50 else 16) else (if i.val < 11 then 41 else 43)) else (if i.val < 14 then (if i.val < 13 then 5 else 55) else (if i.val < 15 then 48 else 15)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[4,5,6]) else (if i.val < 3 then #[5,0,7] else #[8,7,0])) else (if i.val < 6 then (if i.val < 5 then #[9,10,11] else #[10,1,12]) else (if i.val < 7 then #[3,12,1] else #[13,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,13,9] else #[0,14,8]) else (if i.val < 11 then #[14,4,15] else #[6,15,4])) else (if i.val < 14 then (if i.val < 13 then #[7,6,5] else #[15,8,14]) else (if i.val < 15 then #[2,9,13] else #[12,11,10])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[9,2,3] else #[0,5,6]) else (if i.val < 3 then #[14,0,7] else #[6,7,0])) else (if i.val < 6 then (if i.val < 5 then #[1,10,11] else #[2,1,12]) else (if i.val < 7 then #[11,12,1] else #[12,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,13,9] else #[4,14,8]) else (if i.val < 11 then #[5,4,15] else #[8,15,4])) else (if i.val < 14 then (if i.val < 13 then #[15,6,5] else #[7,8,14]) else (if i.val < 15 then #[10,9,13] else #[13,11,10])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 4 else 4)) else (if i.val < 14 then (if i.val < 13 then 5 else 7) else (if i.val < 15 then 9 else 10)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 1 else 2)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3,3] else #[3,3,3]) else (if i.val < 3 then #[1,3,3] else #[3,2,3])) else (if i.val < 6 then (if i.val < 5 then #[3,3,3] else #[2,3,3]) else (if i.val < 7 then #[0,1,3] else #[3,2,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,0,3] else #[0,3,3]) else (if i.val < 11 then #[1,3,3] else #[0,2,3])) else (if i.val < 14 then (if i.val < 13 then #[2,1,3] else #[3,0,2]) else (if i.val < 15 then #[1,3,2] else #[1,2,3])))) : Array (Fin 4))[j.val]!
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
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N3

namespace N4
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 40 else 1) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 13) else (if i.val < 3 then 22 else 26)) else (if i.val < 6 then (if i.val < 5 then 36 else 40) else (if i.val < 7 then 51 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,3] else #[7,6]) else (if i.val < 3 then #[0,1] else #[1,4])) else (if i.val < 6 then (if i.val < 5 then #[2,7] else #[3,2]) else (if i.val < 7 then #[4,5] else #[5,0]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 6) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 7 else 1) else (if i.val < 7 then 5 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 3) else (if i.val < 3 then 5 else 5)) else (if i.val < 6 then (if i.val < 5 then 3 else 7) else (if i.val < 7 then 0 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 2 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 0 else 0))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[1,2] else (if i.val < 2 then #[1,0] else #[1,2])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[1,2] else (if i.val < 2 then #[1,0] else #[1,2])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 9 else 39) else (if i.val < 7 then 50 else 57))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[4,5,2]) else (if i.val < 3 then #[3,0,1] else #[6,7,0])) else (if i.val < 6 then (if i.val < 5 then #[7,6,5] else #[2,1,4]) else (if i.val < 7 then #[5,4,7] else #[0,3,6]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,2,3] else #[0,5,2]) else (if i.val < 3 then #[5,0,1] else #[2,7,0])) else (if i.val < 6 then (if i.val < 5 then #[1,6,5] else #[6,1,4]) else (if i.val < 7 then #[3,4,7] else #[4,3,6]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 3 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 0 else 1))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,4]) else (if i.val < 3 then #[4,7,0] else #[7,7,7])) else (if i.val < 6 then (if i.val < 5 then #[6,0,6] else #[5,7,2]) else (if i.val < 7 then #[2,4,6] else #[6,7,2]))) : Array (Fin 8))[j.val]!
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
  generatorCount := 2
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
  toFun x := (#[3,2,5,4,7,6,1,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,6,1,0,3,2,5,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N4

namespace N5
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 40 else 55) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 13) else (if i.val < 3 then 18 else 26)) else (if i.val < 6 then (if i.val < 5 then 32 else 40) else (if i.val < 7 then 55 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,5] else #[7,4]) else (if i.val < 3 then #[0,3] else #[1,2])) else (if i.val < 6 then (if i.val < 5 then #[2,1] else #[3,0]) else (if i.val < 7 then #[4,7] else #[5,6]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 6) else (if i.val < 3 then 7 else 3)) else (if i.val < 6 then (if i.val < 5 then 5 else 1) else (if i.val < 7 then 2 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 3) else (if i.val < 3 then 3 else 5)) else (if i.val < 6 then (if i.val < 5 then 6 else 7) else (if i.val < 7 then 7 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 2 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 0))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[1,0] else (if i.val < 2 then #[1,2] else #[1,4])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[1,0] else (if i.val < 2 then #[1,2] else #[1,4])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 9 else 33) else (if i.val < 7 then 35 else 61))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[4,3,5]) else (if i.val < 3 then #[6,0,7] else #[2,1,0])) else (if i.val < 6 then (if i.val < 5 then #[7,5,6] else #[3,4,1]) else (if i.val < 7 then #[5,7,4] else #[0,6,2]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,2,3] else #[0,3,5]) else (if i.val < 3 then #[3,0,7] else #[5,1,0])) else (if i.val < 6 then (if i.val < 5 then #[1,5,6] else #[6,4,1]) else (if i.val < 7 then #[2,7,4] else #[4,6,2]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 0 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,0,7]) else (if i.val < 3 then #[7,7,7] else #[2,0,7])) else (if i.val < 6 then (if i.val < 5 then #[2,6,6] else #[3,6,7]) else (if i.val < 7 then #[2,0,6] else #[6,0,7]))) : Array (Fin 8))[j.val]!
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
  generatorCount := 2
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
  toFun x := (#[1,0,3,2,5,4,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N5

namespace N6
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 30 else (if j.val < 2 then 45 else 26)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 12) else (if i.val < 3 then 26 else 30)) else (if i.val < 6 then (if i.val < 5 then 41 else 45) else (if i.val < 7 then 59 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,2,5] else #[5,3,4]) else (if i.val < 3 then #[6,0,7] else #[7,1,6])) else (if i.val < 6 then (if i.val < 5 then #[0,6,1] else #[1,7,0]) else (if i.val < 7 then #[2,4,3] else #[3,5,2]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 6 else 4) else (if i.val < 3 then 3 else 1)) else (if i.val < 6 then (if i.val < 5 then 7 else 2) else (if i.val < 7 then 5 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 3) else (if i.val < 3 then 7 else 7)) else (if i.val < 6 then (if i.val < 5 then 1 else 7) else (if i.val < 7 then 3 else 7))) : Fin 8)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[6,4,2] else (if i.val < 2 then #[3,0,2] else #[3,1,2])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[6,1,2] else (if i.val < 2 then #[3,0,2] else #[3,1,2])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 39 else 33) else (if i.val < 7 then 61 else 50))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[2,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[0,1,7] else #[3,7,1]) else (if i.val < 7 then #[5,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,2,3] else #[0,4,5]) else (if i.val < 3 then #[1,0,6] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[6,7,1]) else (if i.val < 7 then #[7,3,2] else #[3,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[4,7,7]) else (if i.val < 3 then #[3,7,7] else #[7,6,7])) else (if i.val < 6 then (if i.val < 5 then #[5,7,0] else #[2,4,7]) else (if i.val < 7 then #[1,6,7] else #[1,4,0]))) : Array (Fin 8))[j.val]!
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
  toFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N6

namespace N7
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 27 else (if j.val < 2 then 30 else 26)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 27) else (if i.val < 3 then 30 else 31)) else (if i.val < 6 then (if i.val < 5 then 58 else 59) else (if i.val < 7 then 62 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,5,7] else #[7,4,6]) else (if i.val < 3 then #[4,7,5] else #[5,6,4])) else (if i.val < 6 then (if i.val < 5 then #[2,1,3] else #[3,0,2]) else (if i.val < 7 then #[0,3,1] else #[1,2,0]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 1) else (if i.val < 3 then 2 else 7)) else (if i.val < 6 then (if i.val < 5 then 4 else 6) else (if i.val < 7 then 5 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 7 else 4)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 1 else 7))) : Fin 8)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[3,5,0] else (if i.val < 2 then #[1,2,0] else #[3,2,0])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[4,5,0] else (if i.val < 2 then #[1,2,0] else #[3,2,0])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 25 else 9)) else (if i.val < 6 then (if i.val < 5 then 33 else 50) else (if i.val < 7 then 16 else 43))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[3,1,4]) else (if i.val < 3 then #[5,2,0] else #[6,3,7])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1] else #[7,5,6]) else (if i.val < 7 then #[0,6,5] else #[4,7,3]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,0,2] else #[0,1,4]) else (if i.val < 3 then #[4,2,0] else #[1,3,7])) else (if i.val < 6 then (if i.val < 5 then #[7,4,1] else #[2,5,6]) else (if i.val < 7 then #[3,6,5] else #[5,7,3]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 3 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 0)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 0 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,3,7] else #[7,6,7]) else (if i.val < 3 then #[7,1,7] else #[7,4,7])) else (if i.val < 6 then (if i.val < 5 then #[0,3,7] else #[0,4,7]) else (if i.val < 7 then #[0,1,7] else #[0,6,7]))) : Array (Fin 8))[j.val]!
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
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N7

namespace N8
def normalGenerators (j : Fin 1) : Source := ⟨(9 : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 9 else 26) else (if i.val < 3 then 44 else 63)) : Fin 64)
private def next (i : Fin 4) (j : Fin 1) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1] else #[2]) else (if i.val < 3 then #[3] else #[0])) : Array (Fin 4))[j.val]!
private def rank (i : Fin 4) : ℕ := (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 3 else 0))
private def parents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 3 else 0) else (if i.val < 3 then 1 else 3)) : Fin 4)
private def letters (i : Fin 4) : Fin 1 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) : Fin 1)

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

private def posWitness (i : Fin 3) (j : Fin 1) : Fin 4 := ((if i.val < 1 then #[0] else (if i.val < 2 then #[2] else #[2])) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 1) : Fin 4 := ((if i.val < 1 then #[0] else (if i.val < 2 then #[2] else #[2])) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 39 else 33) else (if i.val < 7 then 35 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 45) else (if i.val < 11 then 5 else 1)) else (if i.val < 14 then (if i.val < 13 then 3 else 29) else (if i.val < 15 then 13 else 37)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[5,8,0])) else (if i.val < 6 then (if i.val < 5 then #[9,1,10] else #[3,11,1]) else (if i.val < 7 then #[2,12,11] else #[11,13,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,3,9] else #[4,14,8]) else (if i.val < 11 then #[8,15,4] else #[7,5,6])) else (if i.val < 14 then (if i.val < 13 then #[14,6,15] else #[15,7,14]) else (if i.val < 15 then #[12,9,13] else #[13,10,12])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[5,8,0])) else (if i.val < 6 then (if i.val < 5 then #[9,1,10] else #[3,11,1]) else (if i.val < 7 then #[2,12,11] else #[11,13,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,3,9] else #[4,14,8]) else (if i.val < 11 then #[8,15,4] else #[7,5,6])) else (if i.val < 14 then (if i.val < 13 then #[14,6,15] else #[15,7,14]) else (if i.val < 15 then #[12,9,13] else #[13,10,12])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 7) else (if i.val < 15 then 9 else 10)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 2 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 1)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3,3] else #[2,3,3]) else (if i.val < 3 then #[3,3,3] else #[2,3,3])) else (if i.val < 6 then (if i.val < 5 then #[3,3,3] else #[1,3,3]) else (if i.val < 7 then #[0,3,3] else #[0,3,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,3,0] else #[0,3,2]) else (if i.val < 11 then #[3,3,3] else #[1,3,3])) else (if i.val < 14 then (if i.val < 13 then #[1,3,3] else #[0,3,0]) else (if i.val < 15 then #[0,3,2] else #[3,3,3])))) : Array (Fin 4))[j.val]!
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
  generatorCount := 1
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 16
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 1) : Equiv.Perm (Fin 8) :=
  literalGenerator0

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 1) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N8

namespace N9
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 9 else 54) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 9) else (if i.val < 3 then 19 else 26)) else (if i.val < 6 then (if i.val < 5 then 37 else 44) else (if i.val < 7 then 54 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[6,1] else #[3,0]) else (if i.val < 3 then #[0,3] else #[5,2])) else (if i.val < 6 then (if i.val < 5 then #[2,5] else #[7,4]) else (if i.val < 7 then #[4,7] else #[1,6]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 1) else (if i.val < 3 then 7 else 3)) else (if i.val < 6 then (if i.val < 5 then 5 else 6) else (if i.val < 7 then 2 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 7) else (if i.val < 3 then 3 else 1)) else (if i.val < 6 then (if i.val < 5 then 6 else 3) else (if i.val < 7 then 7 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 2 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 0))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[1,0] else (if i.val < 2 then #[5,2] else #[5,4])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[1,4] else (if i.val < 2 then #[5,2] else #[5,4])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 39 else 33) else (if i.val < 7 then 35 else 45))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,4] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[7,1,2] else #[3,7,1]) else (if i.val < 7 then #[2,3,7] else #[4,5,6]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,4] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[7,1,2] else #[3,7,1]) else (if i.val < 7 then #[2,3,7] else #[4,5,6]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 4))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 0))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[5,7,7]) else (if i.val < 3 then #[7,7,4] else #[5,4,7])) else (if i.val < 6 then (if i.val < 5 then #[7,7,4] else #[3,6,7]) else (if i.val < 7 then #[1,4,6] else #[1,6,6]))) : Array (Fin 8))[j.val]!
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
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 8
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,4,3,2,1,0,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,4,3,2,1,0,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N9

namespace N10
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 50 else 9) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 9) else (if i.val < 3 then 23 else 26)) else (if i.val < 6 then (if i.val < 5 then 33 else 44) else (if i.val < 7 then 50 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,6] else #[0,3]) else (if i.val < 3 then #[7,0] else #[2,5])) else (if i.val < 6 then (if i.val < 5 then #[1,2] else #[4,7]) else (if i.val < 7 then #[3,4] else #[6,1]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 2) else (if i.val < 3 then 6 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 7) else (if i.val < 7 then 1 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 7) else (if i.val < 3 then 3 else 6)) else (if i.val < 6 then (if i.val < 5 then 6 else 3) else (if i.val < 7 then 7 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 2 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 0 else 0))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[4,1] else (if i.val < 2 then #[2,5] else #[4,5])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[0,1] else (if i.val < 2 then #[2,5] else #[4,5])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 39)) else (if i.val < 6 then (if i.val < 5 then 35 else 45) else (if i.val < 7 then 3 else 13))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,1] else #[0,3,0]) else (if i.val < 3 then #[4,0,4] else #[5,1,5])) else (if i.val < 6 then (if i.val < 5 then #[2,6,2] else #[3,7,3]) else (if i.val < 7 then #[7,4,7] else #[6,5,6]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,1] else #[0,3,0]) else (if i.val < 3 then #[4,0,4] else #[5,1,5])) else (if i.val < 6 then (if i.val < 5 then #[2,6,2] else #[3,7,3]) else (if i.val < 7 then #[7,4,7] else #[6,5,6]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 5))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 1))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,4] else #[5,7,0]) else (if i.val < 3 then #[7,7,4] else #[7,7,2])) else (if i.val < 6 then (if i.val < 5 then #[1,7,0] else #[1,7,6]) else (if i.val < 7 then #[3,7,2] else #[1,7,6]))) : Array (Fin 8))[j.val]!
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
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 8
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,4,7,2,5,0,3,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,0,3,6,1,4,7,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N10

namespace N11
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 9 else 13) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 9 else 13) else (if i.val < 3 then 26 else 30)) else (if i.val < 6 then (if i.val < 5 then 40 else 44) else (if i.val < 7 then 59 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 2) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[2,3] else #[3,2]) else (if i.val < 3 then #[5,4] else #[4,5])) else (if i.val < 6 then (if i.val < 5 then #[6,7] else #[7,6]) else (if i.val < 7 then #[1,0] else #[0,1]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 3 else 4)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 7 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 5 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 2 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 1 else 0))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[0,4] else (if i.val < 2 then #[5,4] else #[5,4])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 8 := ((if i.val < 1 then #[0,4] else (if i.val < 2 then #[5,4] else #[5,4])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) else (if i.val < 6 then (if i.val < 5 then 39 else 33) else (if i.val < 7 then 61 else 5))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 4))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[5,7,7]) else (if i.val < 3 then #[3,7,7] else #[5,6,7])) else (if i.val < 6 then (if i.val < 5 then #[4,7,7] else #[2,3,7]) else (if i.val < 7 then #[4,6,7] else #[6,3,7]))) : Array (Fin 8))[j.val]!
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
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 8
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N11

namespace N12
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 9 else (if j.val < 2 then 13 else 55)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 5) else (if i.val < 3 then 9 else 13)) else (if i.val < 6 then (if i.val < 5 then 18 else 22) else (if i.val < 7 then 26 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 32 else 36) else (if i.val < 11 then 40 else 44)) else (if i.val < 14 then (if i.val < 13 then 51 else 55) else (if i.val < 15 then 59 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,5,2] else #[5,4,10]) else (if i.val < 3 then #[6,7,0] else #[7,6,8])) else (if i.val < 6 then (if i.val < 5 then #[9,8,6] else #[8,9,14]) else (if i.val < 7 then #[11,10,4] else #[10,11,12]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,13,3] else #[13,12,11]) else (if i.val < 11 then #[14,15,1] else #[15,14,9])) else (if i.val < 14 then (if i.val < 13 then #[1,0,7] else #[0,1,15]) else (if i.val < 15 then #[3,2,5] else #[2,3,13])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 6 else 8) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 11 else 13) else (if i.val < 7 then 4 else 5))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 15) else (if i.val < 11 then 10 else 9)) else (if i.val < 14 then (if i.val < 13 then 12 else 3) else (if i.val < 15 then 14 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 13) else (if i.val < 3 then 15 else 15)) else (if i.val < 6 then (if i.val < 5 then 6 else 0) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 11) else (if i.val < 11 then 6 else 6)) else (if i.val < 14 then (if i.val < 13 then 7 else 15) else (if i.val < 15 then 11 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 0 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 1 else 0)) else (if i.val < 14 then (if i.val < 13 then 2 else 2) else (if i.val < 15 then 1 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[2,10,1] else (if i.val < 2 then #[11,10,4] else #[11,10,8])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[2,10,1] else (if i.val < 2 then #[11,10,4] else #[11,10,8])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 25)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,3,2]) else (if i.val < 3 then #[3,0,1] else #[2,1,0])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,3,2]) else (if i.val < 3 then #[3,0,1] else #[2,1,0])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15,15] else #[11,1,9]) else (if i.val < 3 then #[9,15,0] else #[4,1,15])) : Array (Fin 16))[j.val]!
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
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,0,3,2,5,4,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N12

namespace N13
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 46 else (if j.val < 2 then 9 else 13)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 9 else 11) else (if i.val < 3 then 13 else 15)) else (if i.val < 6 then (if i.val < 5 then 24 else 26) else (if i.val < 7 then 28 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 40 else 42) else (if i.val < 11 then 44 else 46)) else (if i.val < 14 then (if i.val < 13 then 57 else 59) else (if i.val < 15 then 61 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[12,5,7] else #[13,6,4]) else (if i.val < 3 then #[14,7,5] else #[15,4,6])) else (if i.val < 6 then (if i.val < 5 then #[0,9,11] else #[1,10,8]) else (if i.val < 7 then #[2,11,9] else #[3,8,10]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[4,13,15] else #[5,14,12]) else (if i.val < 11 then #[6,15,13] else #[7,12,14])) else (if i.val < 14 then (if i.val < 13 then #[8,1,3] else #[9,2,0]) else (if i.val < 15 then #[10,3,1] else #[11,0,2])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 11) else (if i.val < 3 then 3 else 8)) else (if i.val < 6 then (if i.val < 5 then 12 else 7) else (if i.val < 7 then 13 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 15) else (if i.val < 11 then 10 else 1)) else (if i.val < 14 then (if i.val < 13 then 5 else 14) else (if i.val < 15 then 6 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 12) else (if i.val < 3 then 15 else 7)) else (if i.val < 6 then (if i.val < 5 then 3 else 0) else (if i.val < 7 then 3 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 4) else (if i.val < 11 then 7 else 15)) else (if i.val < 14 then (if i.val < 13 then 11 else 8) else (if i.val < 15 then 11 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 2 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 2 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[14,0,8] else (if i.val < 2 then #[3,10,8] else #[3,10,8])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[14,0,8] else (if i.val < 2 then #[3,10,8] else #[3,10,8])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 39)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,2] else #[0,3,3]) else (if i.val < 3 then #[3,0,0] else #[2,1,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,2] else #[0,3,3]) else (if i.val < 3 then #[3,0,0] else #[2,1,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15,14] else #[10,15,11]) else (if i.val < 3 then #[7,15,12] else #[8,15,3])) : Array (Fin 16))[j.val]!
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
  toFun x := (#[0,7,2,1,4,3,6,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,2,5,4,7,6,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N13

namespace N14
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 50 else (if j.val < 2 then 9 else 13)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 4) else (if i.val < 3 then 9 else 13)) else (if i.val < 6 then (if i.val < 5 then 19 else 23) else (if i.val < 7 then 26 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 33 else 37) else (if i.val < 11 then 40 else 44)) else (if i.val < 14 then (if i.val < 13 then 50 else 54) else (if i.val < 15 then 59 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,13,12] else #[11,12,13]) else (if i.val < 3 then #[1,6,7] else #[9,7,6])) else (if i.val < 6 then (if i.val < 5 then #[7,0,1] else #[15,1,0]) else (if i.val < 7 then #[5,11,10] else #[13,10,11]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,5,4] else #[10,4,5]) else (if i.val < 11 then #[0,14,15] else #[8,15,14])) else (if i.val < 14 then (if i.val < 13 then #[6,8,9] else #[14,9,8]) else (if i.val < 15 then #[4,3,2] else #[12,2,3])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 14 else 7) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 12 else 9) else (if i.val < 7 then 4 else 8))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 6) else (if i.val < 11 then 11 else 10)) else (if i.val < 14 then (if i.val < 13 then 1 else 13) else (if i.val < 15 then 15 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 2) else (if i.val < 3 then 15 else 15)) else (if i.val < 6 then (if i.val < 5 then 8 else 6) else (if i.val < 7 then 12 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 12 else 12) else (if i.val < 11 then 6 else 6)) else (if i.val < 14 then (if i.val < 13 then 15 else 1) else (if i.val < 15 then 11 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 2 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 2) else (if i.val < 15 then 2 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[8,2,10] else (if i.val < 2 then #[5,11,10] else #[8,11,10])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[1,2,10] else (if i.val < 2 then #[5,11,10] else #[8,11,10])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 39)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,1] else #[0,3,0]) else (if i.val < 3 then #[3,0,3] else #[2,1,2])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,1] else #[0,3,0]) else (if i.val < 3 then #[3,0,3] else #[2,1,2])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15,8] else #[11,15,1]) else (if i.val < 3 then #[7,15,9] else #[10,15,9])) : Array (Fin 16))[j.val]!
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
  toFun x := (#[1,4,7,2,5,0,3,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,0,3,6,1,4,7,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N14

namespace N15
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 9 else (if j.val < 2 then 13 else 43)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 9 else 10) else (if i.val < 3 then 13 else 14)) else (if i.val < 6 then (if i.val < 5 then 25 else 26) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 40 else 43) else (if i.val < 11 then 44 else 47)) else (if i.val < 14 then (if i.val < 13 then 56 else 59) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,7,14] else #[12,14,7]) else (if i.val < 3 then #[7,5,12] else #[14,12,5])) else (if i.val < 6 then (if i.val < 5 then #[3,1,10] else #[10,8,3]) else (if i.val < 7 then #[1,3,8] else #[8,10,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,15,6] else #[4,6,15]) else (if i.val < 11 then #[15,13,4] else #[6,4,13])) else (if i.val < 14 then (if i.val < 13 then #[11,9,2] else #[2,0,11]) else (if i.val < 15 then #[9,11,0] else #[0,2,9])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 13) else (if i.val < 3 then 2 else 12)) else (if i.val < 6 then (if i.val < 5 then 8 else 4) else (if i.val < 7 then 9 else 5))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 11 else 3) else (if i.val < 11 then 10 else 14)) else (if i.val < 14 then (if i.val < 13 then 7 else 15) else (if i.val < 15 then 6 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 7) else (if i.val < 3 then 15 else 5)) else (if i.val < 6 then (if i.val < 5 then 9 else 0) else (if i.val < 7 then 9 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 15) else (if i.val < 11 then 5 else 14)) else (if i.val < 14 then (if i.val < 13 then 2 else 10) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 0 else 1)) else (if i.val < 14 then (if i.val < 13 then 2 else 1) else (if i.val < 15 then 2 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[0,8,4] else (if i.val < 2 then #[10,8,1] else #[10,8,3])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[0,8,14] else (if i.val < 2 then #[10,8,1] else #[10,8,3])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 31 else 39)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,0] else #[0,3,1]) else (if i.val < 3 then #[3,0,2] else #[2,1,3])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,0] else #[0,3,1]) else (if i.val < 3 then #[3,0,2] else #[2,1,3])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15,4] else #[10,15,3]) else (if i.val < 3 then #[7,15,6] else #[8,15,11])) : Array (Fin 16))[j.val]!
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
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,6,1,4,7,2,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,6,1,4,7,2,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N15

namespace N16
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 35 else 9) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 6) else (if i.val < 3 then 9 else 13)) else (if i.val < 6 then (if i.val < 5 then 17 else 21) else (if i.val < 7 then 26 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 35 else 39) else (if i.val < 11 then 40 else 44)) else (if i.val < 14 then (if i.val < 13 then 48 else 52) else (if i.val < 15 then 59 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 2) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,12] else #[3,13]) else (if i.val < 3 then #[13,6] else #[5,7])) else (if i.val < 6 then (if i.val < 5 then #[7,1] else #[15,0]) else (if i.val < 7 then #[1,11] else #[9,10]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,4] else #[2,5]) else (if i.val < 11 then #[12,14] else #[4,15])) else (if i.val < 14 then (if i.val < 13 then #[6,9] else #[14,8]) else (if i.val < 15 then #[0,3] else #[8,2])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 10) else (if i.val < 3 then 2 else 14)) else (if i.val < 6 then (if i.val < 5 then 4 else 15) else (if i.val < 7 then 6 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 12) else (if i.val < 11 then 3 else 11)) else (if i.val < 14 then (if i.val < 13 then 7 else 5) else (if i.val < 15 then 8 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 14 else 4) else (if i.val < 3 then 15 else 14)) else (if i.val < 6 then (if i.val < 5 then 8 else 9) else (if i.val < 7 then 2 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 12) else (if i.val < 11 then 8 else 6)) else (if i.val < 14 then (if i.val < 13 then 10 else 2) else (if i.val < 15 then 10 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 2 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 0 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 1 else 0)))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 16 := ((if i.val < 1 then #[9,2] else (if i.val < 2 then #[9,11] else #[12,11])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 16 := ((if i.val < 1 then #[0,2] else (if i.val < 2 then #[9,11] else #[12,11])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 25 else 33)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,1,2] else #[0,0,3]) else (if i.val < 3 then #[3,3,0] else #[2,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,1,2] else #[0,0,3]) else (if i.val < 3 then #[3,3,0] else #[2,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,9,15] else #[11,13,15]) else (if i.val < 3 then #[11,8,15] else #[6,5,15])) : Array (Fin 16))[j.val]!
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
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 4
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
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N16

namespace N17
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 9 else (if j.val < 2 then 13 else 27)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 9) else (if i.val < 3 then 12 else 13)) else (if i.val < 6 then (if i.val < 5 then 26 else 27) else (if i.val < 7 then 30 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 40 else 41) else (if i.val < 11 then 44 else 45)) else (if i.val < 14 then (if i.val < 13 then 58 else 59) else (if i.val < 15 then 62 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[14,12,10] else #[4,6,11]) else (if i.val < 3 then #[12,14,8] else #[6,4,9])) else (if i.val < 6 then (if i.val < 5 then #[10,8,14] else #[0,2,15]) else (if i.val < 7 then #[8,10,12] else #[2,0,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,15,2] else #[7,5,3]) else (if i.val < 11 then #[15,13,0] else #[5,7,1])) else (if i.val < 14 then (if i.val < 13 then #[9,11,6] else #[3,1,7]) else (if i.val < 15 then #[11,9,4] else #[1,3,5])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 1) else (if i.val < 3 then 9 else 2)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 5 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 11 else 7) else (if i.val < 11 then 10 else 6)) else (if i.val < 14 then (if i.val < 13 then 13 else 15) else (if i.val < 15 then 12 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 15) else (if i.val < 3 then 5 else 15)) else (if i.val < 6 then (if i.val < 5 then 1 else 15) else (if i.val < 7 then 1 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 3) else (if i.val < 11 then 4 else 1)) else (if i.val < 14 then (if i.val < 13 then 6 else 10) else (if i.val < 15 then 4 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 0 else 2)) else (if i.val < 14 then (if i.val < 13 then 2 else 1) else (if i.val < 15 then 2 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[1,8,7] else (if i.val < 2 then #[10,8,5] else #[10,8,7])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[1,8,12] else (if i.val < 2 then #[10,8,5] else #[10,8,7])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 7) else (if i.val < 3 then 25 else 33)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[3,2,0] else #[2,3,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[3,2,0] else #[2,3,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,7,15] else #[10,14,15]) else (if i.val < 3 then #[10,5,15] else #[4,7,15])) : Array (Fin 16))[j.val]!
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
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N17

namespace N18
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 35 else (if j.val < 2 then 50 else 9)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 4 else 6)) else (if i.val < 6 then (if i.val < 5 then 9 else 11) else (if i.val < 7 then 13 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 19) else (if i.val < 11 then 21 else 23)) else (if i.val < 14 then (if i.val < 13 then 24 else 26) else (if i.val < 15 then 28 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 35) else (if i.val < 19 then 37 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 42) else (if i.val < 23 then 44 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 50) else (if i.val < 27 then 52 else 54)) else (if i.val < 30 then (if i.val < 29 then 57 else 59) else (if i.val < 31 then 61 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[14,6,27] else #[22,14,24]) else (if i.val < 3 then #[30,22,25] else #[6,30,26])) else (if i.val < 6 then (if i.val < 5 then #[26,2,13] else #[2,10,14]) else (if i.val < 7 then #[10,18,15] else #[18,26,12]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[15,7,3] else #[23,15,0]) else (if i.val < 11 then #[31,23,1] else #[7,31,2])) else (if i.val < 14 then (if i.val < 13 then #[27,3,21] else #[3,11,22]) else (if i.val < 15 then #[11,19,23] else #[19,27,20])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[12,4,11] else #[20,12,8]) else (if i.val < 19 then #[28,20,9] else #[4,28,10])) else (if i.val < 22 then (if i.val < 21 then #[24,0,29] else #[0,8,30]) else (if i.val < 23 then #[8,16,31] else #[16,24,28]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[13,5,19] else #[21,13,16]) else (if i.val < 27 then #[29,21,17] else #[5,29,18])) else (if i.val < 30 then (if i.val < 29 then #[25,1,5] else #[1,9,6]) else (if i.val < 31 then #[9,17,7] else #[17,25,4]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 26) else (if i.val < 3 then 11 else 16)) else (if i.val < 6 then (if i.val < 5 then 3 else 22) else (if i.val < 7 then 25 else 18))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 27) else (if i.val < 11 then 29 else 20)) else (if i.val < 14 then (if i.val < 13 then 5 else 8) else (if i.val < 15 then 24 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 1) else (if i.val < 19 then 28 else 23)) else (if i.val < 22 then (if i.val < 21 then 4 else 7) else (if i.val < 23 then 21 else 31))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 2) else (if i.val < 27 then 10 else 15)) else (if i.val < 30 then (if i.val < 29 then 30 else 14) else (if i.val < 31 then 19 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 20 else 29) else (if i.val < 3 then 4 else 12)) else (if i.val < 6 then (if i.val < 5 then 31 else 24) else (if i.val < 7 then 0 else 8))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 29) else (if i.val < 11 then 5 else 13)) else (if i.val < 14 then (if i.val < 13 then 17 else 25) else (if i.val < 15 then 0 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 25 else 31) else (if i.val < 19 then 27 else 24)) else (if i.val < 22 then (if i.val < 21 then 17 else 25) else (if i.val < 23 then 13 else 14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 20 else 31) else (if i.val < 27 then 4 else 12)) else (if i.val < 30 then (if i.val < 29 then 19 else 20) else (if i.val < 31 then 21 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 1) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 0) else (if i.val < 19 then 2 else 2)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 2 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 1) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 1 else 2) else (if i.val < 31 then 2 else 0))))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[19,16,4] else (if i.val < 2 then #[19,11,22] else #[24,16,22])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[1,2,4] else (if i.val < 2 then #[19,11,22] else #[24,16,22])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 7) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,1] else #[0,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,1] else #[0,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[31,19,16] else #[22,26,2]) : Array (Fin 32))[j.val]!
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
  toFun x := (#[1,4,7,2,5,0,3,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,0,3,6,1,4,7,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N18

namespace N19
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 50 else 9) else (if j.val < 3 then 13 else 27)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 4 else 5)) else (if i.val < 6 then (if i.val < 5 then 8 else 9) else (if i.val < 7 then 12 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 18 else 19) else (if i.val < 11 then 22 else 23)) else (if i.val < 14 then (if i.val < 13 then 26 else 27) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 33) else (if i.val < 19 then 36 else 37)) else (if i.val < 22 then (if i.val < 21 then 40 else 41) else (if i.val < 23 then 44 else 45))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 50 else 51) else (if i.val < 27 then 54 else 55)) else (if i.val < 30 then (if i.val < 29 then 58 else 59) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 4) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,26,24,18] else #[6,8,10,19]) else (if i.val < 3 then #[22,24,26,16] else #[23,10,8,17])) else (if i.val < 6 then (if i.val < 5 then #[3,30,28,22] else #[2,12,14,23]) else (if i.val < 7 then #[18,28,30,20] else #[19,14,12,21]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[15,18,16,26] else #[14,0,2,27]) else (if i.val < 11 then #[30,16,18,24] else #[31,2,0,25])) else (if i.val < 14 then (if i.val < 13 then #[11,22,20,30] else #[10,4,6,31]) else (if i.val < 15 then #[26,20,22,28] else #[27,6,4,29])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[4,25,27,2] else #[5,11,9,3]) else (if i.val < 19 then #[21,27,25,0] else #[20,9,11,1])) else (if i.val < 22 then (if i.val < 21 then #[0,29,31,6] else #[1,15,13,7]) else (if i.val < 23 then #[17,31,29,4] else #[16,13,15,5]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[12,17,19,10] else #[13,3,1,11]) else (if i.val < 27 then #[29,19,17,8] else #[28,1,3,9])) else (if i.val < 30 then (if i.val < 29 then #[8,21,23,14] else #[9,7,5,15]) else (if i.val < 31 then #[25,23,21,12] else #[24,5,7,13]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 27 else 21) else (if i.val < 3 then 9 else 20)) else (if i.val < 6 then (if i.val < 5 then 13 else 2) else (if i.val < 7 then 14 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 19) else (if i.val < 11 then 8 else 15)) else (if i.val < 14 then (if i.val < 13 then 5 else 4) else (if i.val < 15 then 10 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 6) else (if i.val < 19 then 23 else 7)) else (if i.val < 22 then (if i.val < 21 then 17 else 12) else (if i.val < 23 then 16 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 28) else (if i.val < 27 then 24 else 30)) else (if i.val < 30 then (if i.val < 29 then 25 else 29) else (if i.val < 31 then 18 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 11 else 19) else (if i.val < 3 then 5 else 17)) else (if i.val < 6 then (if i.val < 5 then 13 else 31) else (if i.val < 7 then 13 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 17) else (if i.val < 11 then 24 else 12)) else (if i.val < 14 then (if i.val < 13 then 24 else 31) else (if i.val < 15 then 5 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 24) else (if i.val < 19 then 10 else 24)) else (if i.val < 22 then (if i.val < 21 then 12 else 7) else (if i.val < 23 then 12 else 5))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 31 else 11) else (if i.val < 27 then 2 else 9)) else (if i.val < 30 then (if i.val < 29 then 14 else 22) else (if i.val < 31 then 12 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 4 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 0 else 3)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 3) else (if i.val < 15 then 2 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 1) else (if i.val < 19 then 2 else 2)) else (if i.val < 22 then (if i.val < 21 then 2 else 3) else (if i.val < 23 then 1 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 3) else (if i.val < 27 then 2 else 3)) else (if i.val < 30 then (if i.val < 29 then 3 else 2) else (if i.val < 31 then 3 else 0))))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[17,5,20,15] else (if i.val < 2 then #[11,22,20,13] else #[17,22,20,15])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[2,5,20,28] else (if i.val < 2 then #[11,22,20,13] else #[17,22,20,15])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 7) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,1] else #[0,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,1] else #[0,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[31,15,17] else #[22,30,2]) : Array (Fin 32))[j.val]!
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
  toFun x := (#[1,4,7,2,5,0,3,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,0,3,6,1,4,7,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N19

namespace N20
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 35 else (if j.val < 2 then 9 else 43)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 18) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 25 else 26) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 35) else (if i.val < 19 then 36 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 43) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 51) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 56 else 59) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[30,9,26] else #[22,24,11]) else (if i.val < 3 then #[14,11,24] else #[6,26,9])) else (if i.val < 6 then (if i.val < 5 then #[26,13,30] else #[18,28,15]) else (if i.val < 7 then #[10,15,28] else #[2,30,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[15,3,18] else #[7,18,3]) else (if i.val < 11 then #[31,1,16] else #[23,16,1])) else (if i.val < 14 then (if i.val < 13 then #[11,7,22] else #[3,22,7]) else (if i.val < 15 then #[27,5,20] else #[19,20,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[28,25,10] else #[20,8,27]) else (if i.val < 19 then #[12,27,8] else #[4,10,25])) else (if i.val < 22 then (if i.val < 21 then #[24,29,14] else #[16,12,31]) else (if i.val < 23 then #[8,31,12] else #[0,14,29]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[13,19,2] else #[5,2,19]) else (if i.val < 27 then #[29,17,0] else #[21,0,17])) else (if i.val < 30 then (if i.val < 29 then #[9,23,6] else #[1,6,23]) else (if i.val < 31 then #[25,21,4] else #[17,4,21]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 18 else 27) else (if i.val < 3 then 26 else 16)) else (if i.val < 6 then (if i.val < 5 then 2 else 30) else (if i.val < 7 then 28 else 20))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 31) else (if i.val < 11 then 23 else 24)) else (if i.val < 14 then (if i.val < 13 then 11 else 8) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 1) else (if i.val < 19 then 17 else 25)) else (if i.val < 22 then (if i.val < 21 then 4 else 3) else (if i.val < 23 then 19 else 29))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 21) else (if i.val < 27 then 7 else 6)) else (if i.val < 30 then (if i.val < 29 then 22 else 13) else (if i.val < 31 then 9 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 27 else 29) else (if i.val < 3 then 24 else 8)) else (if i.val < 6 then (if i.val < 5 then 31 else 14) else (if i.val < 7 then 29 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 3) else (if i.val < 11 then 16 else 12)) else (if i.val < 14 then (if i.val < 13 then 21 else 4) else (if i.val < 15 then 20 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 31) else (if i.val < 19 then 8 else 24)) else (if i.val < 22 then (if i.val < 21 then 17 else 31) else (if i.val < 23 then 13 else 29))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 20 else 30) else (if i.val < 27 then 4 else 17)) else (if i.val < 30 then (if i.val < 29 then 16 else 20) else (if i.val < 31 then 4 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 2 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 2 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 2 else 1)) else (if i.val < 22 then (if i.val < 21 then 0 else 2) else (if i.val < 23 then 1 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 2)) else (if i.val < 30 then (if i.val < 29 then 0 else 1) else (if i.val < 31 then 2 else 0))))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[19,4,12] else (if i.val < 2 then #[19,22,5] else #[24,22,7])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[1,4,30] else (if i.val < 2 then #[19,22,5] else #[24,22,7])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 7) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,0] else #[0,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,0] else #[0,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[31,19,12] else #[22,26,7]) : Array (Fin 32))[j.val]!
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
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,6,1,4,7,2,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,6,1,4,7,2,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N20

namespace N21
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 9 else 13) else (if j.val < 3 then 27 else 43)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 9) else (if i.val < 3 then 10 else 11)) else (if i.val < 6 then (if i.val < 5 then 12 else 13) else (if i.val < 7 then 14 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 25) else (if i.val < 11 then 26 else 27)) else (if i.val < 14 then (if i.val < 13 then 28 else 29) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 40 else 41) else (if i.val < 19 then 42 else 43)) else (if i.val < 22 then (if i.val < 21 then 44 else 45) else (if i.val < 23 then 46 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 4) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[30,26,20,12] else #[10,14,21,28]) else (if i.val < 3 then #[24,28,22,14] else #[12,8,23,30])) else (if i.val < 6 then (if i.val < 5 then #[26,30,16,8] else #[14,10,17,24]) else (if i.val < 7 then #[28,24,18,10] else #[8,12,19,26]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[18,22,28,4] else #[6,2,29,20]) else (if i.val < 11 then #[20,16,30,6] else #[0,4,31,22])) else (if i.val < 14 then (if i.val < 13 then #[22,18,24,0] else #[2,6,25,16]) else (if i.val < 15 then #[16,20,26,2] else #[4,0,27,18])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[27,31,4,13] else #[15,11,5,29]) else (if i.val < 19 then #[29,25,6,15] else #[9,13,7,31])) else (if i.val < 22 then (if i.val < 21 then #[31,27,0,9] else #[11,15,1,25]) else (if i.val < 23 then #[25,29,2,11] else #[13,9,3,27]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[23,19,12,5] else #[3,7,13,21]) else (if i.val < 27 then #[17,21,14,7] else #[5,1,15,23])) else (if i.val < 30 then (if i.val < 29 then #[19,23,8,1] else #[7,3,9,17]) else (if i.val < 31 then #[21,17,10,3] else #[1,5,11,19]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 11 else 1) else (if i.val < 3 then 22 else 30)) else (if i.val < 6 then (if i.val < 5 then 12 else 2) else (if i.val < 7 then 20 else 16))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 26 else 14) else (if i.val < 11 then 5 else 3)) else (if i.val < 14 then (if i.val < 13 then 28 else 15) else (if i.val < 15 then 6 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 18 else 9) else (if i.val < 19 then 31 else 4)) else (if i.val < 22 then (if i.val < 21 then 17 else 7) else (if i.val < 23 then 13 else 25))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 10 else 24) else (if i.val < 27 then 21 else 29)) else (if i.val < 30 then (if i.val < 29 then 8 else 27) else (if i.val < 31 then 19 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 11 else 31) else (if i.val < 3 then 14 else 30)) else (if i.val < 6 then (if i.val < 5 then 11 else 31) else (if i.val < 7 then 10 else 19))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 28 else 19) else (if i.val < 11 then 1 else 31)) else (if i.val < 14 then (if i.val < 13 then 24 else 19) else (if i.val < 15 then 1 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 5) else (if i.val < 19 then 6 else 31)) else (if i.val < 22 then (if i.val < 21 then 10 else 1) else (if i.val < 23 then 11 else 28))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 5 else 21) else (if i.val < 27 then 14 else 20)) else (if i.val < 30 then (if i.val < 29 then 1 else 17) else (if i.val < 31 then 10 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 4 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 3 else 3)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 3 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 0) else (if i.val < 11 then 0 else 2)) else (if i.val < 14 then (if i.val < 13 then 2 else 1) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 2) else (if i.val < 19 then 2 else 3)) else (if i.val < 22 then (if i.val < 21 then 0 else 2) else (if i.val < 23 then 3 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 3) else (if i.val < 27 then 2 else 1)) else (if i.val < 30 then (if i.val < 29 then 3 else 3) else (if i.val < 31 then 2 else 0))))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[1,16,15,9] else (if i.val < 2 then #[20,16,11,2] else #[20,16,15,6])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[1,16,26,28] else (if i.val < 2 then #[20,16,11,2] else #[20,16,15,6])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 7) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,0] else #[0,1,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,0] else #[0,1,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[31,15,9] else #[20,30,6]) : Array (Fin 32))[j.val]!
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
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,6,1,4,7,2,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,6,1,4,7,2,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N21

namespace N22
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 30) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 7) else (if i.val < 3 then 9 else 13)) else (if i.val < 6 then (if i.val < 5 then 16 else 20) else (if i.val < 7 then 26 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 34 else 38) else (if i.val < 11 then 40 else 44)) else (if i.val < 14 then (if i.val < 13 then 49 else 53) else (if i.val < 15 then 59 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 2) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,8] else #[2,9]) else (if i.val < 3 then #[4,10] else #[12,11])) else (if i.val < 6 then (if i.val < 5 then #[6,12] else #[14,13]) else (if i.val < 7 then #[8,14] else #[0,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,0] else #[3,1]) else (if i.val < 11 then #[5,2] else #[13,3])) else (if i.val < 14 then (if i.val < 13 then #[7,4] else #[15,5]) else (if i.val < 15 then #[9,6] else #[1,7])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 1) else (if i.val < 3 then 3 else 8)) else (if i.val < 6 then (if i.val < 5 then 6 else 12) else (if i.val < 7 then 10 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 4) else (if i.val < 11 then 7 else 13)) else (if i.val < 14 then (if i.val < 13 then 11 else 15) else (if i.val < 15 then 14 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 15) else (if i.val < 3 then 1 else 9)) else (if i.val < 6 then (if i.val < 5 then 2 else 10) else (if i.val < 7 then 4 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 2 else 3)) else (if i.val < 14 then (if i.val < 13 then 4 else 5) else (if i.val < 15 then 6 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 2 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 0)))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 16 := ((if i.val < 1 then #[1,14] else (if i.val < 2 then #[0,7] else #[4,7])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 16 := ((if i.val < 1 then #[1,14] else (if i.val < 2 then #[0,7] else #[4,7])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 25 else 61)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,3,0] else #[3,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,3,0] else #[3,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[13,15,15] else #[5,15,15]) else (if i.val < 3 then #[8,14,15] else #[9,14,15])) : Array (Fin 16))[j.val]!
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
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 4
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N22

namespace N23
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 7 else 46) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 5 else 7)) else (if i.val < 6 then (if i.val < 5 then 9 else 11) else (if i.val < 7 then 13 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 18) else (if i.val < 11 then 20 else 22)) else (if i.val < 14 then (if i.val < 13 then 24 else 26) else (if i.val < 15 then 28 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 34) else (if i.val < 19 then 36 else 38)) else (if i.val < 22 then (if i.val < 21 then 40 else 42) else (if i.val < 23 then 44 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 51) else (if i.val < 27 then 53 else 55)) else (if i.val < 30 then (if i.val < 29 then 57 else 59) else (if i.val < 31 then 61 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 2) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[12,24] else #[20,25]) else (if i.val < 3 then #[28,26] else #[4,27])) else (if i.val < 6 then (if i.val < 5 then #[8,28] else #[16,29]) else (if i.val < 7 then #[24,30] else #[0,31]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,0] else #[21,1]) else (if i.val < 11 then #[29,2] else #[5,3])) else (if i.val < 14 then (if i.val < 13 then #[9,4] else #[17,5]) else (if i.val < 15 then #[25,6] else #[1,7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[14,8] else #[22,9]) else (if i.val < 19 then #[30,10] else #[6,11])) else (if i.val < 22 then (if i.val < 21 then #[10,12] else #[18,13]) else (if i.val < 23 then #[26,14] else #[2,15]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,16] else #[23,17]) else (if i.val < 27 then #[31,18] else #[7,19])) else (if i.val < 30 then (if i.val < 29 then #[11,20] else #[19,21]) else (if i.val < 31 then #[27,22] else #[3,23]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 14 else 12) else (if i.val < 3 then 5 else 1)) else (if i.val < 6 then (if i.val < 5 then 3 else 21) else (if i.val < 7 then 17 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 27) else (if i.val < 11 then 24 else 15)) else (if i.val < 14 then (if i.val < 13 then 22 else 13) else (if i.val < 15 then 30 else 6)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 28 else 20) else (if i.val < 19 then 18 else 10)) else (if i.val < 22 then (if i.val < 21 then 16 else 31) else (if i.val < 23 then 26 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 23 else 19) else (if i.val < 27 then 11 else 4)) else (if i.val < 30 then (if i.val < 29 then 8 else 29) else (if i.val < 31 then 25 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 15) else (if i.val < 3 then 23 else 31)) else (if i.val < 6 then (if i.val < 5 then 3 else 13) else (if i.val < 7 then 19 else 27))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 17) else (if i.val < 11 then 20 else 28)) else (if i.val < 14 then (if i.val < 13 then 0 else 8) else (if i.val < 15 then 22 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 5 else 13) else (if i.val < 19 then 26 else 27)) else (if i.val < 22 then (if i.val < 21 then 28 else 9) else (if i.val < 23 then 17 else 31))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 1) else (if i.val < 27 then 2 else 3)) else (if i.val < 30 then (if i.val < 29 then 4 else 5) else (if i.val < 31 then 6 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 2 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 1 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 0) else (if i.val < 23 then 0 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 1) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 1 else 0))))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 32 := ((if i.val < 1 then #[3,30] else (if i.val < 2 then #[1,7] else #[8,7])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 32 := ((if i.val < 1 then #[3,30] else (if i.val < 2 then #[1,7] else #[8,7])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 31) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,1] else #[1,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,1] else #[1,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 1) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[26,31,30] else #[10,31,28]) : Array (Fin 32))[j.val]!
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
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 2
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,7,2,1,4,3,6,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,2,5,4,7,6,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N23

namespace N24
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 43 else 30)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 20 else 23)) else (if i.val < 14 then (if i.val < 13 then 25 else 26) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 34) else (if i.val < 19 then 37 else 38)) else (if i.val < 22 then (if i.val < 21 then 40 else 43) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 50) else (if i.val < 27 then 53 else 54)) else (if i.val < 30 then (if i.val < 29 then 56 else 59) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[28,10,16] else #[20,27,17]) else (if i.val < 3 then #[12,8,18] else #[4,25,19])) else (if i.val < 6 then (if i.val < 5 then #[8,30,20] else #[0,15,21]) else (if i.val < 7 then #[24,28,22] else #[16,13,23]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,2,24] else #[5,19,25]) else (if i.val < 11 then #[29,0,26] else #[21,17,27])) else (if i.val < 14 then (if i.val < 13 then #[25,22,28] else #[17,7,29]) else (if i.val < 15 then #[9,20,30] else #[1,5,31])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[30,26,0] else #[22,11,1]) else (if i.val < 19 then #[14,24,2] else #[6,9,3])) else (if i.val < 22 then (if i.val < 21 then #[10,14,4] else #[2,31,5]) else (if i.val < 23 then #[26,12,6] else #[18,29,7]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,18,8] else #[7,3,9]) else (if i.val < 27 then #[31,16,10] else #[23,1,11])) else (if i.val < 30 then (if i.val < 29 then #[27,6,12] else #[19,23,13]) else (if i.val < 31 then #[11,4,14] else #[3,21,15]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 18 else 9) else (if i.val < 3 then 7 else 1)) else (if i.val < 6 then (if i.val < 5 then 4 else 8) else (if i.val < 7 then 15 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 14) else (if i.val < 11 then 25 else 23)) else (if i.val < 14 then (if i.val < 13 then 16 else 21) else (if i.val < 15 then 24 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 20) else (if i.val < 19 then 17 else 6)) else (if i.val < 22 then (if i.val < 21 then 12 else 2) else (if i.val < 23 then 29 else 27))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 5) else (if i.val < 27 then 31 else 19)) else (if i.val < 30 then (if i.val < 29 then 28 else 30) else (if i.val < 31 then 11 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 15) else (if i.val < 3 then 21 else 31)) else (if i.val < 6 then (if i.val < 5 then 3 else 21) else (if i.val < 7 then 19 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 25) else (if i.val < 11 then 20 else 30)) else (if i.val < 14 then (if i.val < 13 then 2 else 8) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 7 else 1) else (if i.val < 19 then 2 else 3)) else (if i.val < 22 then (if i.val < 21 then 4 else 31) else (if i.val < 23 then 6 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 8 else 3) else (if i.val < 27 then 10 else 1)) else (if i.val < 30 then (if i.val < 29 then 6 else 13) else (if i.val < 31 then 4 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 2) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 2 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 2) else (if i.val < 19 then 2 else 2)) else (if i.val < 22 then (if i.val < 21 then 2 else 1) else (if i.val < 23 then 2 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 1) else (if i.val < 27 then 2 else 1)) else (if i.val < 30 then (if i.val < 29 then 1 else 2) else (if i.val < 31 then 1 else 0))))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[3,12,29] else (if i.val < 2 then #[1,5,15] else #[8,7,15])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[3,30,29] else (if i.val < 2 then #[1,5,15] else #[8,7,15])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 31) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,0] else #[1,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,0] else #[1,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 1) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[26,31,12] else #[10,31,14]) : Array (Fin 32))[j.val]!
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
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,6,1,4,7,2,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,3,6,1,4,7,2,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N24

namespace N25
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 27 else 30)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 6 else 7)) else (if i.val < 6 then (if i.val < 5 then 8 else 9) else (if i.val < 7 then 12 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 17) else (if i.val < 11 then 20 else 21)) else (if i.val < 14 then (if i.val < 13 then 26 else 27) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 35) else (if i.val < 19 then 38 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 41) else (if i.val < 23 then 44 else 45))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 49) else (if i.val < 27 then 52 else 53)) else (if i.val < 30 then (if i.val < 29 then 58 else 59) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,18,17] else #[20,19,16]) else (if i.val < 3 then #[21,16,19] else #[5,17,18])) else (if i.val < 6 then (if i.val < 5 then #[24,22,21] else #[8,23,20]) else (if i.val < 7 then #[9,20,23] else #[25,21,22]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,26,25] else #[28,27,24]) else (if i.val < 11 then #[29,24,27] else #[13,25,26])) else (if i.val < 14 then (if i.val < 13 then #[16,30,29] else #[0,31,28]) else (if i.val < 15 then #[1,28,31] else #[17,29,30])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[22,2,1] else #[6,3,0]) else (if i.val < 19 then #[7,0,3] else #[23,1,2])) else (if i.val < 22 then (if i.val < 21 then #[10,6,5] else #[26,7,4]) else (if i.val < 23 then #[27,4,7] else #[11,5,6]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[30,10,9] else #[14,11,8]) else (if i.val < 27 then #[15,8,11] else #[31,9,10])) else (if i.val < 30 then (if i.val < 29 then #[2,14,13] else #[18,15,12]) else (if i.val < 31 then #[19,12,15] else #[3,13,14]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 9) else (if i.val < 3 then 16 else 1)) else (if i.val < 6 then (if i.val < 5 then 15 else 4) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 24) else (if i.val < 11 then 23 else 22)) else (if i.val < 14 then (if i.val < 13 then 19 else 2) else (if i.val < 15 then 3 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 18 else 5) else (if i.val < 19 then 6 else 17)) else (if i.val < 22 then (if i.val < 21 then 12 else 25) else (if i.val < 23 then 26 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 27 else 21) else (if i.val < 27 then 20 else 31)) else (if i.val < 30 then (if i.val < 29 then 8 else 29) else (if i.val < 31 then 28 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 14) else (if i.val < 3 then 28 else 31)) else (if i.val < 6 then (if i.val < 5 then 0 else 3) else (if i.val < 7 then 17 else 18))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 6) else (if i.val < 11 then 20 else 23)) else (if i.val < 14 then (if i.val < 13 then 8 else 31) else (if i.val < 15 then 31 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 3) else (if i.val < 19 then 3 else 1)) else (if i.val < 22 then (if i.val < 21 then 5 else 7) else (if i.val < 23 then 7 else 5))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 8) else (if i.val < 27 then 8 else 10)) else (if i.val < 30 then (if i.val < 29 then 13 else 12) else (if i.val < 31 then 12 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 2 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 1) else (if i.val < 19 then 2 else 1)) else (if i.val < 22 then (if i.val < 21 then 2 else 1) else (if i.val < 23 then 2 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 2) else (if i.val < 27 then 1 else 2)) else (if i.val < 30 then (if i.val < 29 then 2 else 2) else (if i.val < 31 then 1 else 0))))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[3,15,29] else (if i.val < 2 then #[1,13,14] else #[8,15,14])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[3,28,29] else (if i.val < 2 then #[1,13,14] else #[8,15,14])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 25) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,0,1] else #[1,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,0,1] else #[1,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 2) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[27,15,31] else #[16,13,31]) : Array (Fin 32))[j.val]!
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
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
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

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N25

namespace N26
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 31 else 25)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63)))))) : Fin 64)
private def next (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[56,32,38] else #[24,33,35]) else (if i.val < 3 then #[8,34,32] else #[40,35,37])) else (if i.val < 6 then (if i.val < 5 then #[25,36,34] else #[57,37,39]) else (if i.val < 7 then #[41,38,36] else #[9,39,33]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[48,40,46] else #[16,41,43]) else (if i.val < 11 then #[0,42,40] else #[32,43,45])) else (if i.val < 14 then (if i.val < 13 then #[17,44,42] else #[49,45,47]) else (if i.val < 15 then #[33,46,44] else #[1,47,41])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[26,48,50] else #[58,49,55]) else (if i.val < 19 then #[42,50,52] else #[10,51,49])) else (if i.val < 22 then (if i.val < 21 then #[59,52,54] else #[27,53,51]) else (if i.val < 23 then #[11,54,48] else #[43,55,53]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,56,58] else #[50,57,63]) else (if i.val < 27 then #[34,58,60] else #[2,59,57])) else (if i.val < 30 then (if i.val < 29 then #[51,60,62] else #[19,61,59]) else (if i.val < 31 then #[3,62,56] else #[35,63,61]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[28,0,2] else #[60,1,7]) else (if i.val < 35 then #[44,2,4] else #[12,3,1])) else (if i.val < 38 then (if i.val < 37 then #[61,4,6] else #[29,5,3]) else (if i.val < 39 then #[13,6,0] else #[45,7,5]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[20,8,10] else #[52,9,15]) else (if i.val < 43 then #[36,10,12] else #[4,11,9])) else (if i.val < 46 then (if i.val < 45 then #[53,12,14] else #[21,13,11]) else (if i.val < 47 then #[5,14,8] else #[37,15,13])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[62,16,22] else #[30,17,19]) else (if i.val < 51 then #[14,18,16] else #[46,19,21])) else (if i.val < 54 then (if i.val < 53 then #[31,20,18] else #[63,21,23]) else (if i.val < 55 then #[47,22,20] else #[15,23,17]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[54,24,30] else #[22,25,27]) else (if i.val < 59 then #[6,26,24] else #[38,27,29])) else (if i.val < 62 then (if i.val < 61 then #[23,28,26] else #[55,29,31]) else (if i.val < 63 then #[39,30,28] else #[7,31,25])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 17) else (if i.val < 3 then 46 else 19)) else (if i.val < 6 then (if i.val < 5 then 30 else 15) else (if i.val < 7 then 61 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 59 else 4) else (if i.val < 11 then 58 else 31)) else (if i.val < 14 then (if i.val < 13 then 18 else 33) else (if i.val < 15 then 22 else 29)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 11 else 38) else (if i.val < 19 then 23 else 42)) else (if i.val < 22 then (if i.val < 21 then 50 else 32) else (if i.val < 23 then 24 else 35))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 37 else 3) else (if i.val < 27 then 26 else 25)) else (if i.val < 30 then (if i.val < 29 then 36 else 21) else (if i.val < 31 then 62 else 2))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 53 else 6) else (if i.val < 35 then 47 else 7)) else (if i.val < 38 then (if i.val < 37 then 52 else 34) else (if i.val < 39 then 60 else 5))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 41 else 12) else (if i.val < 43 then 40 else 13)) else (if i.val < 46 then (if i.val < 45 then 39 else 14) else (if i.val < 47 then 44 else 51)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 27 else 56) else (if i.val < 51 then 9 else 55)) else (if i.val < 54 then (if i.val < 53 then 28 else 54) else (if i.val < 55 then 45 else 20))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 10) else (if i.val < 59 then 48 else 43)) else (if i.val < 62 then (if i.val < 61 then 16 else 8) else (if i.val < 63 then 49 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 32 else 33) else (if i.val < 3 then 27 else 35)) else (if i.val < 6 then (if i.val < 5 then 43 else 39) else (if i.val < 7 then 58 else 63))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 40 else 7) else (if i.val < 11 then 42 else 43)) else (if i.val < 14 then (if i.val < 13 then 35 else 45) else (if i.val < 15 then 50 else 41)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 12) else (if i.val < 19 then 50 else 29)) else (if i.val < 22 then (if i.val < 21 then 52 else 45) else (if i.val < 23 then 57 else 60))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 63) else (if i.val < 27 then 16 else 57)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 11 else 7) else (if i.val < 35 then 26 else 31)) else (if i.val < 38 then (if i.val < 37 then 4 else 5) else (if i.val < 39 then 59 else 7))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 3 else 9) else (if i.val < 43 then 12 else 9)) else (if i.val < 46 then (if i.val < 45 then 12 else 39) else (if i.val < 47 then 14 else 15)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 13) else (if i.val < 51 then 25 else 21)) else (if i.val < 54 then (if i.val < 53 then 41 else 21) else (if i.val < 55 then 22 else 61))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 24 else 25) else (if i.val < 59 then 26 else 29)) else (if i.val < 62 then (if i.val < 61 then 33 else 31) else (if i.val < 63 then 48 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 3 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 0 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 1 else 0)) else (if i.val < 22 then (if i.val < 21 then 1 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 2) else (if i.val < 27 then 0 else 2)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 1 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 2) else (if i.val < 35 then 0 else 0)) else (if i.val < 38 then (if i.val < 37 then 1 else 1) else (if i.val < 39 then 0 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 1) else (if i.val < 43 then 2 else 2)) else (if i.val < 46 then (if i.val < 45 then 1 else 0) else (if i.val < 47 then 1 else 1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 1 else 0) else (if i.val < 51 then 0 else 2)) else (if i.val < 54 then (if i.val < 53 then 0 else 1) else (if i.val < 55 then 1 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 1 else 1) else (if i.val < 59 then 1 else 2)) else (if i.val < 62 then (if i.val < 61 then 0 else 2) else (if i.val < 63 then 0 else 0)))))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[7,62,14] else (if i.val < 2 then #[3,31,29] else #[16,27,25])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[7,27,43] else (if i.val < 2 then #[3,31,29] else #[16,27,25])) : Array (Fin 64))[j.val]!
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
private def stepWitness (i : Fin 1) (j : Fin 3) : Fin 64 := (#[53,31,25] : Array (Fin 64))[j.val]!
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
  generatorCount := 3
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 1
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,1,4,7,2,5,0,3] : Array (Fin 8))[x.val]!
  invFun x := (#[6,1,4,7,2,5,0,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T26.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T26.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T26.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T26.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N26

@[reducible] def states (i : Fin 27) : BinaryNormalState generators :=
  (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then N0.state else (if i.val < 2 then N1.state else N2.state)) else (if i.val < 4 then N3.state else (if i.val < 5 then N4.state else N5.state))) else (if i.val < 9 then (if i.val < 7 then N6.state else (if i.val < 8 then N7.state else N8.state)) else (if i.val < 11 then (if i.val < 10 then N9.state else N10.state) else (if i.val < 12 then N11.state else N12.state)))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then N13.state else (if i.val < 15 then N14.state else N15.state)) else (if i.val < 18 then (if i.val < 17 then N16.state else N17.state) else (if i.val < 19 then N18.state else N19.state))) else (if i.val < 23 then (if i.val < 21 then N20.state else (if i.val < 22 then N21.state else N22.state)) else (if i.val < 25 then (if i.val < 24 then N23.state else N24.state) else (if i.val < 26 then N25.state else N26.state)))))

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T26
