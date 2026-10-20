import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T31

/-! Exact original normal states and quotient rows for 8T31.
Selected by external selected_missing_normal_registry.py; all finite facts are checked
in Lean's kernel. This file certifies normal-state coverage, not the later
pair/character/transport acceptance of those states. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.RDTBinaryNormal8T31

abbrev Source := FiniteGroupRow 64
local instance : Group Source := BinaryMenuCayley8T31.group

def generators (j : Fin 3) : Source :=
  ⟨BinaryMenuCayley8T31.certificate.next BinaryMenuCayley8T31.certificate.identity j⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  apply binaryNormal_full_generators_of_equiv BinaryMenuCayley8T31.generators
    generators BinaryMenuCayley8T31.originalEquiv
  intro j
  change BinaryMenuCayley8T31.certificate.toCayley.elements
    (BinaryMenuCayley8T31.certificate.toCayley.next
      BinaryMenuCayley8T31.certificate.toCayley.identity j)=_
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

private def representatives (i : Fin 64) : Source := ⟨((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 38 else 19))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 45 else 39) else (if i.val < 11 then 23 else 47)) else (if i.val < 14 then (if i.val < 13 then 62 else 17) else (if i.val < 15 then 51 else 18)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 61 else 30) else (if i.val < 19 then 21 else 55)) else (if i.val < 22 then (if i.val < 21 then 22 else 29) else (if i.val < 23 then 9 else 49))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 4) else (if i.val < 27 then 50 else 2)) else (if i.val < 30 then (if i.val < 29 then 11 else 53) else (if i.val < 31 then 14 else 5))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 54 else 3) else (if i.val < 35 then 41 else 8)) else (if i.val < 38 then (if i.val < 37 then 36 else 44) else (if i.val < 39 then 59 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 34 else 43) else (if i.val < 43 then 10 else 37)) else (if i.val < 46 then (if i.val < 45 then 46 else 27) else (if i.val < 47 then 1 else 35)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 60) else (if i.val < 51 then 40 else 58)) else (if i.val < 54 then (if i.val < 53 then 57 else 32) else (if i.val < 55 then 20 else 28))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 42 else 26) else (if i.val < 59 then 25 else 33)) else (if i.val < 62 then (if i.val < 61 then 48 else 56) else (if i.val < 63 then 52 else 24)))))) : Fin 64)⟩
private def quotientNext (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[8,7,0])) else (if i.val < 6 then (if i.val < 5 then #[9,1,10] else #[11,10,1]) else (if i.val < 7 then #[2,12,13] else #[14,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,15,16] else #[4,17,18]) else (if i.val < 11 then #[19,5,4] else #[5,20,21])) else (if i.val < 14 then (if i.val < 13 then #[17,6,22] else #[23,22,6]) else (if i.val < 15 then #[7,24,25] else #[26,8,27])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,27,8] else #[12,9,28]) else (if i.val < 19 then #[29,28,9] else #[10,30,31])) else (if i.val < 22 then (if i.val < 21 then #[32,11,33] else #[16,33,11]) else (if i.val < 23 then #[34,13,12] else #[13,35,36]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[37,14,38] else #[36,38,14]) else (if i.val < 27 then #[15,37,39] else #[40,16,15])) else (if i.val < 30 then (if i.val < 29 then #[41,18,17] else #[18,42,43]) else (if i.val < 31 then #[44,19,45] else #[43,45,19]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[20,44,46] else #[47,21,20]) else (if i.val < 35 then #[22,48,49] else #[50,23,51])) else (if i.val < 38 then (if i.val < 37 then #[25,51,23] else #[24,26,52]) else (if i.val < 39 then #[45,25,24] else #[53,52,26]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[27,49,48] else #[28,54,55]) else (if i.val < 43 then #[56,29,57] else #[31,57,29])) else (if i.val < 46 then (if i.val < 45 then #[30,32,58] else #[38,31,30]) else (if i.val < 47 then #[59,58,32] else #[33,55,54])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[60,34,40] else #[55,40,34]) else (if i.val < 51 then #[35,60,61] else #[57,36,35])) else (if i.val < 54 then (if i.val < 53 then #[58,39,37] else #[39,61,60]) else (if i.val < 55 then #[62,41,47] else #[49,47,41]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[42,62,63] else #[51,43,42]) else (if i.val < 59 then #[52,46,44] else #[46,63,62])) else (if i.val < 62 then (if i.val < 61 then #[48,50,53] else #[63,53,50]) else (if i.val < 63 then #[54,56,59] else #[61,59,56])))))) : Array (Fin 64))[j.val]!
private def quotientPrev (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[8,7,0])) else (if i.val < 6 then (if i.val < 5 then #[9,1,10] else #[11,10,1]) else (if i.val < 7 then #[2,12,13] else #[14,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,15,16] else #[4,17,18]) else (if i.val < 11 then #[19,5,4] else #[5,20,21])) else (if i.val < 14 then (if i.val < 13 then #[17,6,22] else #[23,22,6]) else (if i.val < 15 then #[7,24,25] else #[26,8,27])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,27,8] else #[12,9,28]) else (if i.val < 19 then #[29,28,9] else #[10,30,31])) else (if i.val < 22 then (if i.val < 21 then #[32,11,33] else #[16,33,11]) else (if i.val < 23 then #[34,13,12] else #[13,35,36]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[37,14,38] else #[36,38,14]) else (if i.val < 27 then #[15,37,39] else #[40,16,15])) else (if i.val < 30 then (if i.val < 29 then #[41,18,17] else #[18,42,43]) else (if i.val < 31 then #[44,19,45] else #[43,45,19]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[20,44,46] else #[47,21,20]) else (if i.val < 35 then #[22,48,49] else #[50,23,51])) else (if i.val < 38 then (if i.val < 37 then #[25,51,23] else #[24,26,52]) else (if i.val < 39 then #[45,25,24] else #[53,52,26]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[27,49,48] else #[28,54,55]) else (if i.val < 43 then #[56,29,57] else #[31,57,29])) else (if i.val < 46 then (if i.val < 45 then #[30,32,58] else #[38,31,30]) else (if i.val < 47 then #[59,58,32] else #[33,55,54])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[60,34,40] else #[55,40,34]) else (if i.val < 51 then #[35,60,61] else #[57,36,35])) else (if i.val < 54 then (if i.val < 53 then #[58,39,37] else #[39,61,60]) else (if i.val < 55 then #[62,41,47] else #[49,47,41]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[42,62,63] else #[51,43,42]) else (if i.val < 59 then #[52,46,44] else #[46,63,62])) else (if i.val < 62 then (if i.val < 61 then #[48,50,53] else #[63,53,50]) else (if i.val < 63 then #[54,56,59] else #[61,59,56])))))) : Array (Fin 64))[j.val]!
private def quotientParents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 6) else (if i.val < 15 then 7 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8 else 9) else (if i.val < 19 then 9 else 10)) else (if i.val < 22 then (if i.val < 21 then 11 else 11) else (if i.val < 23 then 12 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 14 else 14) else (if i.val < 27 then 15 else 15)) else (if i.val < 30 then (if i.val < 29 then 17 else 18) else (if i.val < 31 then 19 else 19))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 20 else 20) else (if i.val < 35 then 22 else 23)) else (if i.val < 38 then (if i.val < 37 then 23 else 24) else (if i.val < 39 then 24 else 26))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 27 else 28) else (if i.val < 43 then 29 else 29)) else (if i.val < 46 then (if i.val < 45 then 30 else 30) else (if i.val < 47 then 32 else 33)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 34 else 34) else (if i.val < 51 then 35 else 35)) else (if i.val < 54 then (if i.val < 53 then 37 else 39) else (if i.val < 55 then 41 else 41))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 42 else 42) else (if i.val < 59 then 44 else 46)) else (if i.val < 62 then (if i.val < 61 then 48 else 50) else (if i.val < 63 then 54 else 56)))))) : Fin 64)
private def quotientLetters (i : Fin 64) : Fin 3 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 0 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 1) else (if i.val < 19 then 2 else 0)) else (if i.val < 22 then (if i.val < 21 then 1 else 2) else (if i.val < 23 then 2 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 2) else (if i.val < 27 then 0 else 2)) else (if i.val < 30 then (if i.val < 29 then 2 else 0) else (if i.val < 31 then 1 else 2))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 2) else (if i.val < 35 then 0 else 1)) else (if i.val < 38 then (if i.val < 37 then 2 else 0) else (if i.val < 39 then 2 else 2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 0) else (if i.val < 43 then 1 else 2)) else (if i.val < 46 then (if i.val < 45 then 0 else 2) else (if i.val < 47 then 2 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 1 else 2) else (if i.val < 51 then 0 else 2)) else (if i.val < 54 then (if i.val < 53 then 2 else 0) else (if i.val < 55 then 1 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 2) else (if i.val < 59 then 2 else 0)) else (if i.val < 62 then (if i.val < 61 then 0 else 2) else (if i.val < 63 then 0 else 2)))))) : Fin 3)
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

private def posWitness (i : Fin 3) (j : Fin 1) : Fin 2 := ((if i.val < 1 then #[0] else (if i.val < 2 then #[0] else #[0])) : Array (Fin 2))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 1) : Fin 2 := ((if i.val < 1 then #[0] else (if i.val < 2 then #[0] else #[0])) : Array (Fin 2))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 32) : Source := ⟨((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 38 else 19))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 45 else 39) else (if i.val < 11 then 23 else 47)) else (if i.val < 14 then (if i.val < 13 then 62 else 17) else (if i.val < 15 then 51 else 18)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 61 else 30) else (if i.val < 19 then 21 else 55)) else (if i.val < 22 then (if i.val < 21 then 22 else 29) else (if i.val < 23 then 9 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 2) else (if i.val < 27 then 11 else 14)) else (if i.val < 30 then (if i.val < 29 then 5 else 3) else (if i.val < 31 then 59 else 27))))) : Fin 64)⟩
private def quotientNext (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[8,7,0])) else (if i.val < 6 then (if i.val < 5 then #[9,1,10] else #[11,10,1]) else (if i.val < 7 then #[2,12,13] else #[14,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,15,16] else #[4,17,18]) else (if i.val < 11 then #[19,5,4] else #[5,20,21])) else (if i.val < 14 then (if i.val < 13 then #[17,6,22] else #[20,22,6]) else (if i.val < 15 then #[7,23,24] else #[18,8,25])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,25,8] else #[12,9,26]) else (if i.val < 19 then #[15,26,9] else #[10,27,28])) else (if i.val < 22 then (if i.val < 21 then #[13,11,29] else #[16,29,11]) else (if i.val < 23 then #[27,13,12] else #[26,14,30]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,30,14] else #[28,16,15]) else (if i.val < 27 then #[23,18,17] else #[22,19,31])) else (if i.val < 30 then (if i.val < 29 then #[25,31,19] else #[24,21,20]) else (if i.val < 31 then #[31,24,23] else #[30,28,27]))))) : Array (Fin 32))[j.val]!
private def quotientPrev (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[8,7,0])) else (if i.val < 6 then (if i.val < 5 then #[9,1,10] else #[11,10,1]) else (if i.val < 7 then #[2,12,13] else #[14,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,15,16] else #[4,17,18]) else (if i.val < 11 then #[19,5,4] else #[5,20,21])) else (if i.val < 14 then (if i.val < 13 then #[17,6,22] else #[20,22,6]) else (if i.val < 15 then #[7,23,24] else #[18,8,25])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,25,8] else #[12,9,26]) else (if i.val < 19 then #[15,26,9] else #[10,27,28])) else (if i.val < 22 then (if i.val < 21 then #[13,11,29] else #[16,29,11]) else (if i.val < 23 then #[27,13,12] else #[26,14,30]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,30,14] else #[28,16,15]) else (if i.val < 27 then #[23,18,17] else #[22,19,31])) else (if i.val < 30 then (if i.val < 29 then #[25,31,19] else #[24,21,20]) else (if i.val < 31 then #[31,24,23] else #[30,28,27]))))) : Array (Fin 32))[j.val]!
private def quotientParents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 6) else (if i.val < 15 then 7 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8 else 9) else (if i.val < 19 then 9 else 10)) else (if i.val < 22 then (if i.val < 21 then 11 else 11) else (if i.val < 23 then 12 else 14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 14 else 15) else (if i.val < 27 then 17 else 19)) else (if i.val < 30 then (if i.val < 29 then 19 else 20) else (if i.val < 31 then 23 else 27))))) : Fin 32)
private def quotientLetters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 0 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 1) else (if i.val < 19 then 2 else 0)) else (if i.val < 22 then (if i.val < 21 then 1 else 2) else (if i.val < 23 then 2 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 2) else (if i.val < 27 then 2 else 1)) else (if i.val < 30 then (if i.val < 29 then 2 else 2) else (if i.val < 31 then 2 else 2))))) : Fin 3)
private def stepWitness (i : Fin 32) (j : Fin 3) : Fin 2 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,1,1] else #[1,1,1]) else (if i.val < 3 then #[1,1,1] else #[1,1,1])) else (if i.val < 6 then (if i.val < 5 then #[1,1,1] else #[1,1,1]) else (if i.val < 7 then #[1,1,1] else #[1,1,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[1,1,1] else #[1,1,1]) else (if i.val < 11 then #[1,1,1] else #[1,1,1])) else (if i.val < 14 then (if i.val < 13 then #[1,1,1] else #[0,1,1]) else (if i.val < 15 then #[1,1,1] else #[0,1,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[1,1,1] else #[1,1,1]) else (if i.val < 19 then #[0,1,1] else #[1,1,1])) else (if i.val < 22 then (if i.val < 21 then #[0,1,1] else #[1,1,1]) else (if i.val < 23 then #[0,1,1] else #[0,1,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[0,1,1] else #[0,1,1]) else (if i.val < 27 then #[0,1,1] else #[0,1,1])) else (if i.val < 30 then (if i.val < 29 then #[0,1,1] else #[0,1,1]) else (if i.val < 31 then #[1,1,1] else #[1,1,1]))))) : Array (Fin 2))[j.val]!
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
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 24 else 27) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 24 else 27) else (if i.val < 3 then 60 else 63)) : Fin 64)
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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[0,1] else (if i.val < 2 then #[0,2] else #[0,2])) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[0,1] else (if i.val < 2 then #[0,2] else #[0,2])) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 38 else 19))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 45 else 39) else (if i.val < 11 then 23 else 47)) else (if i.val < 14 then (if i.val < 13 then 62 else 17) else (if i.val < 15 then 30 else 21)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[8,7,0])) else (if i.val < 6 then (if i.val < 5 then #[9,1,10] else #[11,10,1]) else (if i.val < 7 then #[2,12,13] else #[10,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,13,12] else #[4,14,15]) else (if i.val < 11 then #[7,5,4] else #[5,15,14])) else (if i.val < 14 then (if i.val < 13 then #[14,6,8] else #[15,8,6]) else (if i.val < 15 then #[12,9,11] else #[13,11,9])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[8,7,0])) else (if i.val < 6 then (if i.val < 5 then #[9,1,10] else #[11,10,1]) else (if i.val < 7 then #[2,12,13] else #[10,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,13,12] else #[4,14,15]) else (if i.val < 11 then #[7,5,4] else #[5,15,14])) else (if i.val < 14 then (if i.val < 13 then #[14,6,8] else #[15,8,6]) else (if i.val < 15 then #[12,9,11] else #[13,11,9])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 6) else (if i.val < 15 then 9 else 9)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 1 else 2)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3,3] else #[3,3,3]) else (if i.val < 3 then #[3,3,3] else #[3,3,3])) else (if i.val < 6 then (if i.val < 5 then #[3,3,3] else #[3,3,3]) else (if i.val < 7 then #[3,3,3] else #[1,3,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,2,2] else #[3,3,3]) else (if i.val < 11 then #[1,3,3] else #[3,2,2])) else (if i.val < 14 then (if i.val < 13 then #[3,3,2] else #[1,2,3]) else (if i.val < 15 then #[3,3,2] else #[1,2,3])))) : Array (Fin 4))[j.val]!
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
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 24 else 29) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 24 else 29) else (if i.val < 3 then 58 else 63)) : Fin 64)
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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[0,1] else (if i.val < 2 then #[0,2] else #[0,1])) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[0,1] else (if i.val < 2 then #[0,2] else #[0,1])) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 38 else 19))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 39 else 23) else (if i.val < 11 then 62 else 17)) else (if i.val < 14 then (if i.val < 13 then 30 else 21) else (if i.val < 15 then 9 else 11)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[8,1,9] else #[3,9,1]) else (if i.val < 7 then #[2,10,11] else #[11,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[4,12,13] else #[13,5,4]) else (if i.val < 11 then #[12,6,14] else #[7,14,6])) else (if i.val < 14 then (if i.val < 13 then #[10,8,15] else #[9,15,8]) else (if i.val < 15 then #[15,11,10] else #[14,13,12])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[8,1,9] else #[3,9,1]) else (if i.val < 7 then #[2,10,11] else #[11,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[4,12,13] else #[13,5,4]) else (if i.val < 11 then #[12,6,14] else #[7,14,6])) else (if i.val < 14 then (if i.val < 13 then #[10,8,15] else #[9,15,8]) else (if i.val < 15 then #[15,11,10] else #[14,13,12])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 4) else (if i.val < 11 then 6 else 6)) else (if i.val < 14 then (if i.val < 13 then 8 else 8) else (if i.val < 15 then 10 else 12)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 2) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 2 else 2)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3,3] else #[3,3,3]) else (if i.val < 3 then #[3,3,3] else #[1,3,3])) else (if i.val < 6 then (if i.val < 5 then #[3,3,3] else #[1,3,3]) else (if i.val < 7 then #[3,3,3] else #[2,3,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,3,3] else #[2,3,3]) else (if i.val < 11 then #[3,3,3] else #[2,3,3])) else (if i.val < 14 then (if i.val < 13 then #[3,3,3] else #[2,3,3]) else (if i.val < 15 then #[1,3,3] else #[1,3,3])))) : Array (Fin 4))[j.val]!
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

end N3

namespace N4
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 24 else 30) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 24 else 30) else (if i.val < 3 then 57 else 63)) : Fin 64)
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

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 19 else 45))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 23 else 47) else (if i.val < 11 then 51 else 61)) else (if i.val < 14 then (if i.val < 13 then 55 else 29) else (if i.val < 15 then 4 else 5)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,8] else #[9,8,1]) else (if i.val < 7 then #[10,3,2] else #[3,10,11]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,5,4] else #[5,12,13]) else (if i.val < 11 then #[6,7,14] else #[13,14,7])) else (if i.val < 14 then (if i.val < 13 then #[8,9,15] else #[11,15,9]) else (if i.val < 15 then #[15,11,10] else #[14,13,12])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,8] else #[9,8,1]) else (if i.val < 7 then #[10,3,2] else #[3,10,11]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,5,4] else #[5,12,13]) else (if i.val < 11 then #[6,7,14] else #[13,14,7])) else (if i.val < 14 then (if i.val < 13 then #[8,9,15] else #[11,15,9]) else (if i.val < 15 then #[15,11,10] else #[14,13,12])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 6 else 7)) else (if i.val < 14 then (if i.val < 13 then 8 else 9) else (if i.val < 15 then 10 else 12)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 0) else (if i.val < 11 then 0 else 2)) else (if i.val < 14 then (if i.val < 13 then 0 else 2) else (if i.val < 15 then 2 else 2)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3,3] else #[3,3,3]) else (if i.val < 3 then #[1,3,3] else #[3,3,3])) else (if i.val < 6 then (if i.val < 5 then #[1,3,3] else #[3,3,3]) else (if i.val < 7 then #[3,3,3] else #[3,2,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,3,3] else #[3,2,3]) else (if i.val < 11 then #[3,2,3] else #[3,2,3])) else (if i.val < 14 then (if i.val < 13 then #[3,2,3] else #[3,2,3]) else (if i.val < 15 then #[1,2,3] else #[1,2,3])))) : Array (Fin 4))[j.val]!
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

end N4

namespace N5
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 24 else (if j.val < 2 then 27 else 16)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 19) else (if i.val < 3 then 24 else 27)) else (if i.val < 6 then (if i.val < 5 then 52 else 55) else (if i.val < 7 then 60 else 63))) : Fin 64)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,6,5] else #[2,6,5])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,6,5] else #[2,6,5])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 7)) else (if i.val < 6 then (if i.val < 5 then 38 else 39) else (if i.val < 7 then 62 else 30))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,2] else #[0,3,3]) else (if i.val < 3 then #[4,0,0] else #[5,1,1])) else (if i.val < 6 then (if i.val < 5 then #[2,6,6] else #[3,7,7]) else (if i.val < 7 then #[7,4,4] else #[6,5,5]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,2] else #[0,3,3]) else (if i.val < 3 then #[4,0,0] else #[5,1,1])) else (if i.val < 6 then (if i.val < 5 then #[2,6,6] else #[3,7,7]) else (if i.val < 7 then #[7,4,4] else #[6,5,5]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 5))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 1))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,1] else #[7,7,5]) else (if i.val < 3 then #[7,7,1] else #[7,7,5])) else (if i.val < 6 then (if i.val < 5 then #[7,7,0] else #[7,7,4]) else (if i.val < 7 then #[7,7,0] else #[7,7,4]))) : Array (Fin 8))[j.val]!
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
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 24 else (if j.val < 2 then 27 else 21)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 22) else (if i.val < 3 then 24 else 27)) else (if i.val < 6 then (if i.val < 5 then 49 else 50) else (if i.val < 7 then 60 else 63))) : Fin 64)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,6,0] else #[2,6,5])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,6,0] else #[2,6,5])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 19 else 23))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[5,0,6] else #[4,6,0])) else (if i.val < 6 then (if i.val < 5 then #[3,1,7] else #[2,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[5,0,6] else #[4,6,0])) else (if i.val < 6 then (if i.val < 5 then #[3,1,7] else #[2,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 4))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[1,7,7] else #[0,7,7])) else (if i.val < 6 then (if i.val < 5 then #[5,7,7] else #[4,7,7]) else (if i.val < 7 then #[3,7,7] else #[3,7,7]))) : Array (Fin 8))[j.val]!
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

end N6

namespace N7
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 24 else (if j.val < 2 then 27 else 29)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 24 else 27) else (if i.val < 3 then 29 else 30)) else (if i.val < 6 then (if i.val < 5 then 57 else 58) else (if i.val < 7 then 60 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,6,5] else #[6,7,4]) else (if i.val < 3 then #[5,4,7] else #[4,5,6])) else (if i.val < 6 then (if i.val < 5 then #[3,2,1] else #[2,3,0]) else (if i.val < 7 then #[1,0,3] else #[0,1,2]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 3 else 7)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 4 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 7 else 6)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 0 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 1 else 0))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[0,1,2] else (if i.val < 2 then #[0,6,5] else #[0,6,2])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[0,1,2] else (if i.val < 2 then #[0,6,5] else #[0,6,2])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 19 else 23))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 4))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[3,7,7] else #[2,7,7])) else (if i.val < 6 then (if i.val < 5 then #[3,7,7] else #[2,7,7]) else (if i.val < 7 then #[1,7,7] else #[1,7,7]))) : Array (Fin 8))[j.val]!
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

end N7

namespace N8
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 24 else (if j.val < 2 then 29 else 8)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 13) else (if i.val < 3 then 24 else 29)) else (if i.val < 6 then (if i.val < 5 then 42 else 47) else (if i.val < 7 then 58 else 63))) : Fin 64)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,6,5] else #[2,3,0])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,6,5] else #[2,3,0])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 7)) else (if i.val < 6 then (if i.val < 5 then 38 else 39) else (if i.val < 7 then 62 else 30))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,0] else #[0,3,1]) else (if i.val < 3 then #[4,0,2] else #[5,1,3])) else (if i.val < 6 then (if i.val < 5 then #[2,6,4] else #[3,7,5]) else (if i.val < 7 then #[7,4,6] else #[6,5,7]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,0] else #[0,3,1]) else (if i.val < 3 then #[4,0,2] else #[5,1,3])) else (if i.val < 6 then (if i.val < 5 then #[2,6,4] else #[3,7,5]) else (if i.val < 7 then #[7,4,6] else #[6,5,7]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 5))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 1))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,1] else #[7,7,5]) else (if i.val < 3 then #[7,7,1] else #[7,7,5])) else (if i.val < 6 then (if i.val < 5 then #[7,7,0] else #[7,7,4]) else (if i.val < 7 then #[7,7,0] else #[7,7,4]))) : Array (Fin 8))[j.val]!
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

end N8

namespace N9
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 24 else (if j.val < 2 then 29 else 11)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 11 else 14) else (if i.val < 3 then 24 else 29)) else (if i.val < 6 then (if i.val < 5 then 41 else 44) else (if i.val < 7 then 58 else 63))) : Fin 64)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,6,0] else #[2,3,5])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,6,0] else #[2,3,5])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 38 else 19))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[7,1,6] else #[3,6,1]) else (if i.val < 7 then #[2,5,4] else #[4,3,2]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[6,0,7] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[7,1,6] else #[3,6,1]) else (if i.val < 7 then #[2,5,4] else #[4,3,2]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 0 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[7,7,7] else #[3,7,7])) else (if i.val < 6 then (if i.val < 5 then #[5,7,4] else #[3,4,7]) else (if i.val < 7 then #[7,1,1] else #[0,7,7]))) : Array (Fin 8))[j.val]!
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

end N9

namespace N10
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 24 else (if j.val < 2 then 30 else 0)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 6) else (if i.val < 3 then 24 else 30)) else (if i.val < 6 then (if i.val < 5 then 33 else 39) else (if i.val < 7 then 57 else 63))) : Fin 64)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,3,0] else #[2,6,5])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,3,0] else #[2,6,5])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 13 else 15)) else (if i.val < 6 then (if i.val < 5 then 45 else 47) else (if i.val < 7 then 61 else 29))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[4,2,0] else #[5,3,1])) else (if i.val < 6 then (if i.val < 5 then #[2,4,6] else #[3,5,7]) else (if i.val < 7 then #[7,6,4] else #[6,7,5]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[4,2,0] else #[5,3,1])) else (if i.val < 6 then (if i.val < 5 then #[2,4,6] else #[3,5,7]) else (if i.val < 7 then #[7,6,4] else #[6,7,5]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 5))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 2 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,1,7] else #[7,5,7]) else (if i.val < 3 then #[7,1,7] else #[7,5,7])) else (if i.val < 6 then (if i.val < 5 then #[7,0,7] else #[7,4,7]) else (if i.val < 7 then #[7,0,7] else #[7,4,7]))) : Array (Fin 8))[j.val]!
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

end N10

namespace N11
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 24 else (if j.val < 2 then 30 else 3)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 5) else (if i.val < 3 then 24 else 30)) else (if i.val < 6 then (if i.val < 5 then 34 else 36) else (if i.val < 7 then 57 else 63))) : Fin 64)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,3,5] else #[2,6,0])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[2,3,4] else (if i.val < 2 then #[2,3,5] else #[2,6,0])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) else (if i.val < 6 then (if i.val < 5 then 7 else 15) else (if i.val < 7 then 19 else 45))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[6,7,1]) else (if i.val < 7 then #[5,3,2] else #[3,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[6,7,1]) else (if i.val < 7 then #[5,3,2] else #[3,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[3,7,7] else #[7,7,7])) else (if i.val < 6 then (if i.val < 5 then #[3,7,4] else #[5,4,7]) else (if i.val < 7 then #[0,7,7] else #[7,1,1]))) : Array (Fin 8))[j.val]!
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

end N11

namespace N12
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 16 else 21)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 19) else (if i.val < 3 then 21 else 22)) else (if i.val < 6 then (if i.val < 5 then 24 else 27) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 50) else (if i.val < 11 then 52 else 55)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,10,15,13] else #[10,11,14,12]) else (if i.val < 3 then #[9,8,6,4] else #[8,9,7,5])) else (if i.val < 6 then (if i.val < 5 then #[15,14,11,9] else #[14,15,10,8]) else (if i.val < 7 then #[13,12,2,0] else #[12,13,3,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,2,12,14] else #[2,3,13,15]) else (if i.val < 11 then #[1,0,5,7] else #[0,1,4,6])) else (if i.val < 14 then (if i.val < 13 then #[7,6,8,10] else #[6,7,9,11]) else (if i.val < 15 then #[5,4,1,3] else #[4,5,0,2])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 12) else (if i.val < 3 then 4 else 13)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 11 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 7) else (if i.val < 11 then 8 else 6)) else (if i.val < 14 then (if i.val < 13 then 15 else 10) else (if i.val < 15 then 5 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 14) else (if i.val < 3 then 15 else 14)) else (if i.val < 6 then (if i.val < 5 then 15 else 15) else (if i.val < 7 then 2 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 4) else (if i.val < 11 then 5 else 4)) else (if i.val < 14 then (if i.val < 13 then 8 else 0) else (if i.val < 15 then 4 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 2) else (if i.val < 3 then 3 else 3)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 2 else 2)) else (if i.val < 14 then (if i.val < 13 then 2 else 3) else (if i.val < 15 then 1 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,10,8] else (if i.val < 2 then #[4,14,11,2] else #[4,14,11,9])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,10,8] else (if i.val < 2 then #[4,14,11,2] else #[4,14,11,9])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 7)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,2] else #[0,3,3]) else (if i.val < 3 then #[3,0,0] else #[2,1,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,2] else #[0,3,3]) else (if i.val < 3 then #[3,0,0] else #[2,1,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15,1] else #[15,15,11]) else (if i.val < 3 then #[7,15,1] else #[7,15,11])) : Array (Fin 16))[j.val]!
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

end N12

namespace N13
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else 0)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 24 else 27) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 33 else 34) else (if i.val < 11 then 36 else 39)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,10,9,15] else #[10,11,8,5]) else (if i.val < 3 then #[9,8,11,6] else #[8,9,10,12])) else (if i.val < 6 then (if i.val < 5 then #[15,14,13,11] else #[14,15,12,1]) else (if i.val < 7 then #[13,12,15,2] else #[12,13,14,8]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,2,1,7] else #[2,3,0,13]) else (if i.val < 11 then #[1,0,3,14] else #[0,1,2,4])) else (if i.val < 14 then (if i.val < 13 then #[7,6,5,3] else #[6,7,4,9]) else (if i.val < 15 then #[5,4,7,10] else #[4,5,6,0])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 9) else (if i.val < 3 then 10 else 14)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 3 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 12) else (if i.val < 11 then 11 else 7)) else (if i.val < 14 then (if i.val < 13 then 8 else 6) else (if i.val < 15 then 5 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 5) else (if i.val < 3 then 6 else 12)) else (if i.val < 6 then (if i.val < 5 then 15 else 15) else (if i.val < 7 then 15 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 0 else 4)) else (if i.val < 14 then (if i.val < 13 then 5 else 4) else (if i.val < 15 then 4 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 3 else 3)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 2 else 2) else (if i.val < 15 then 1 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,8] else (if i.val < 2 then #[4,14,13,0] else #[4,14,6,11])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,8] else (if i.val < 2 then #[4,14,13,0] else #[4,14,6,11])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 13 else 15)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[3,2,0] else #[2,3,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[3,2,0] else #[2,3,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,3,15] else #[15,11,15]) else (if i.val < 3 then #[6,3,15] else #[6,11,15])) : Array (Fin 16))[j.val]!
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

end N13

namespace N14
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else 1)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 24 else 27) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 32 else 35) else (if i.val < 11 then 37 else 38)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,10,9,7] else #[10,11,8,13]) else (if i.val < 3 then #[9,8,11,14] else #[8,9,10,4])) else (if i.val < 6 then (if i.val < 5 then #[15,14,13,11] else #[14,15,12,1]) else (if i.val < 7 then #[13,12,15,2] else #[12,13,14,8]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,2,1,15] else #[2,3,0,5]) else (if i.val < 11 then #[1,0,3,6] else #[0,1,2,12])) else (if i.val < 14 then (if i.val < 13 then #[7,6,5,3] else #[6,7,4,9]) else (if i.val < 15 then #[5,4,7,10] else #[4,5,6,0])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 9) else (if i.val < 3 then 10 else 14)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 3 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 12) else (if i.val < 11 then 11 else 7)) else (if i.val < 14 then (if i.val < 13 then 8 else 6) else (if i.val < 15 then 5 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 5) else (if i.val < 3 then 6 else 12)) else (if i.val < 6 then (if i.val < 5 then 15 else 15) else (if i.val < 7 then 15 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 0 else 4)) else (if i.val < 14 then (if i.val < 13 then 5 else 4) else (if i.val < 15 then 4 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 3 else 3)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 2 else 2) else (if i.val < 15 then 1 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,8] else (if i.val < 2 then #[4,14,13,8] else #[4,14,6,9])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,8] else (if i.val < 2 then #[4,14,13,8] else #[4,14,6,9])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 13 else 15)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,1,2] else #[0,0,3]) else (if i.val < 3 then #[3,3,0] else #[2,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,1,2] else #[0,0,3]) else (if i.val < 3 then #[3,3,0] else #[2,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,3,15] else #[15,11,15]) else (if i.val < 3 then #[6,3,15] else #[6,11,15])) : Array (Fin 16))[j.val]!
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

end N14

namespace N15
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else 8)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 11) else (if i.val < 3 then 13 else 14)) else (if i.val < 6 then (if i.val < 5 then 24 else 27) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 41 else 42) else (if i.val < 11 then 44 else 47)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,10,9,15] else #[10,11,8,5]) else (if i.val < 3 then #[9,8,11,13] else #[8,9,10,7])) else (if i.val < 6 then (if i.val < 5 then #[15,14,13,11] else #[14,15,12,1]) else (if i.val < 7 then #[13,12,15,9] else #[12,13,14,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,2,1,12] else #[2,3,0,6]) else (if i.val < 11 then #[1,0,3,14] else #[0,1,2,4])) else (if i.val < 14 then (if i.val < 13 then #[7,6,5,8] else #[6,7,4,2]) else (if i.val < 15 then #[5,4,7,10] else #[4,5,6,0])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 9) else (if i.val < 3 then 13 else 15)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 3 else 12))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 14 else 10) else (if i.val < 11 then 11 else 7)) else (if i.val < 14 then (if i.val < 13 then 8 else 6) else (if i.val < 15 then 5 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 5) else (if i.val < 3 then 13 else 9)) else (if i.val < 6 then (if i.val < 5 then 15 else 15) else (if i.val < 7 then 15 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 12 else 6) else (if i.val < 11 then 0 else 4)) else (if i.val < 14 then (if i.val < 13 then 5 else 4) else (if i.val < 15 then 4 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 3 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 2 else 2) else (if i.val < 15 then 1 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,9] else (if i.val < 2 then #[4,14,13,11] else #[4,14,6,0])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,9] else (if i.val < 2 then #[4,14,13,11] else #[4,14,6,0])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 7)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,0] else #[0,3,1]) else (if i.val < 3 then #[3,0,2] else #[2,1,3])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,0] else #[0,3,1]) else (if i.val < 3 then #[3,0,2] else #[2,1,3])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15,2] else #[15,15,11]) else (if i.val < 3 then #[7,15,2] else #[7,15,11])) : Array (Fin 16))[j.val]!
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

end N15

namespace N16
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else 9)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 9 else 10) else (if i.val < 3 then 12 else 15)) else (if i.val < 6 then (if i.val < 5 then 24 else 27) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 40 else 43) else (if i.val < 11 then 45 else 46)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,10,9,13] else #[10,11,8,7]) else (if i.val < 3 then #[9,8,11,15] else #[8,9,10,5])) else (if i.val < 6 then (if i.val < 5 then #[15,14,13,11] else #[14,15,12,1]) else (if i.val < 7 then #[13,12,15,9] else #[12,13,14,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,2,1,14] else #[2,3,0,4]) else (if i.val < 11 then #[1,0,3,12] else #[0,1,2,6])) else (if i.val < 14 then (if i.val < 13 then #[7,6,5,8] else #[6,7,4,2]) else (if i.val < 15 then #[5,4,7,10] else #[4,5,6,0])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 9) else (if i.val < 3 then 13 else 15)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 3 else 12))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 14 else 10) else (if i.val < 11 then 11 else 7)) else (if i.val < 14 then (if i.val < 13 then 8 else 6) else (if i.val < 15 then 5 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 5) else (if i.val < 3 then 13 else 9)) else (if i.val < 6 then (if i.val < 5 then 15 else 15) else (if i.val < 7 then 15 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 12 else 6) else (if i.val < 11 then 0 else 4)) else (if i.val < 14 then (if i.val < 13 then 5 else 4) else (if i.val < 15 then 4 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 3 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 2 else 2) else (if i.val < 15 then 1 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,9] else (if i.val < 2 then #[4,14,13,3] else #[4,14,6,2])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,9] else (if i.val < 2 then #[4,14,13,3] else #[4,14,6,2])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 7)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,1] else #[0,3,0]) else (if i.val < 3 then #[3,0,3] else #[2,1,2])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,1] else #[0,3,0]) else (if i.val < 3 then #[3,0,3] else #[2,1,2])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15,3] else #[15,15,10]) else (if i.val < 3 then #[7,15,3] else #[7,15,10])) : Array (Fin 16))[j.val]!
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

end N16

namespace N17
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else 17)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 17 else 18) else (if i.val < 3 then 20 else 23)) else (if i.val < 6 then (if i.val < 5 then 24 else 27) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 48 else 51) else (if i.val < 11 then 53 else 54)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,10,9,14] else #[10,11,8,15]) else (if i.val < 3 then #[9,8,11,7] else #[8,9,10,6])) else (if i.val < 6 then (if i.val < 5 then #[15,14,13,11] else #[14,15,12,10]) else (if i.val < 7 then #[13,12,15,2] else #[12,13,14,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,2,1,13] else #[2,3,0,12]) else (if i.val < 11 then #[1,0,3,4] else #[0,1,2,5])) else (if i.val < 14 then (if i.val < 13 then #[7,6,5,8] else #[6,7,4,9]) else (if i.val < 15 then #[5,4,7,1] else #[4,5,6,0])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 13) else (if i.val < 3 then 10 else 15)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 3 else 12))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 14 else 11) else (if i.val < 11 then 9 else 7)) else (if i.val < 14 then (if i.val < 13 then 8 else 6) else (if i.val < 15 then 5 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 14) else (if i.val < 3 then 6 else 10)) else (if i.val < 6 then (if i.val < 5 then 15 else 15) else (if i.val < 7 then 15 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 12 else 0) else (if i.val < 11 then 5 else 4)) else (if i.val < 14 then (if i.val < 13 then 5 else 4) else (if i.val < 15 then 4 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 3 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 2) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 2 else 2) else (if i.val < 15 then 1 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,10] else (if i.val < 2 then #[4,14,13,3] else #[4,14,6,9])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[4,5,6,10] else (if i.val < 2 then #[4,14,13,3] else #[4,14,6,9])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 31) else (if i.val < 3 then 6 else 13)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,3,2]) else (if i.val < 3 then #[3,0,1] else #[2,1,0])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,3,2]) else (if i.val < 3 then #[3,0,1] else #[2,1,0])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[15,15,15] else #[15,9,9]) else (if i.val < 3 then #[1,15,3] else #[0,3,15])) : Array (Fin 16))[j.val]!
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

end N17

namespace N18
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else 25)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 24 else 25) else (if i.val < 3 then 26 else 27)) else (if i.val < 6 then (if i.val < 5 then 28 else 29) else (if i.val < 7 then 30 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 56 else 57) else (if i.val < 11 then 58 else 59)) else (if i.val < 14 then (if i.val < 13 then 60 else 61) else (if i.val < 15 then 62 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[15,12,10,14] else #[14,13,11,15]) else (if i.val < 3 then #[13,14,8,12] else #[12,15,9,13])) else (if i.val < 6 then (if i.val < 5 then #[11,8,14,10] else #[10,9,15,11]) else (if i.val < 7 then #[9,10,12,8] else #[8,11,13,9]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[7,4,2,6] else #[6,5,3,7]) else (if i.val < 11 then #[5,6,0,4] else #[4,7,1,5])) else (if i.val < 14 then (if i.val < 13 then #[3,0,6,2] else #[2,1,7,3]) else (if i.val < 15 then #[1,2,4,0] else #[0,3,5,1])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 4) else (if i.val < 3 then 12 else 2)) else (if i.val < 6 then (if i.val < 5 then 13 else 3) else (if i.val < 7 then 11 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 8) else (if i.val < 11 then 6 else 10)) else (if i.val < 14 then (if i.val < 13 then 5 else 9) else (if i.val < 15 then 7 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 12 else 15)) else (if i.val < 6 then (if i.val < 5 then 10 else 15) else (if i.val < 7 then 12 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 3) else (if i.val < 11 then 0 else 5)) else (if i.val < 14 then (if i.val < 13 then 0 else 3) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 3 else 1)) else (if i.val < 6 then (if i.val < 5 then 3 else 2) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 2) else (if i.val < 11 then 2 else 3)) else (if i.val < 14 then (if i.val < 13 then 1 else 3) else (if i.val < 15 then 3 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[0,3,5,1] else (if i.val < 2 then #[0,12,10,8] else #[0,12,5,4])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[0,3,5,1] else (if i.val < 2 then #[0,12,10,8] else #[0,12,5,4])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 6) else (if i.val < 3 then 13 else 19)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,3,0] else #[3,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,3,0] else #[3,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[7,15,15] else #[14,15,15]) else (if i.val < 3 then #[13,15,15] else #[11,15,15])) : Array (Fin 16))[j.val]!
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

end N18

namespace N19
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 16 else (if j.val < 4 then 21 else 0))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 8 else 11) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 34) else (if i.val < 19 then 36 else 39)) else (if i.val < 22 then (if i.val < 21 then 41 else 42) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 50) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[19,18,23,21,31] else #[18,19,22,20,13]) else (if i.val < 3 then #[17,16,6,4,14] else #[16,17,7,5,28])) else (if i.val < 6 then (if i.val < 5 then #[23,22,19,17,27] else #[22,23,18,16,9]) else (if i.val < 7 then #[21,20,2,0,10] else #[20,21,3,1,24]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[27,26,31,29,23] else #[26,27,30,28,5]) else (if i.val < 11 then #[25,24,14,12,6] else #[24,25,15,13,20])) else (if i.val < 14 then (if i.val < 13 then #[31,30,27,25,19] else #[30,31,26,24,1]) else (if i.val < 15 then #[29,28,10,8,2] else #[28,29,11,9,16])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[3,2,20,22,15] else #[2,3,21,23,29]) else (if i.val < 19 then #[1,0,5,7,30] else #[0,1,4,6,12])) else (if i.val < 22 then (if i.val < 21 then #[7,6,16,18,11] else #[6,7,17,19,25]) else (if i.val < 23 then #[5,4,1,3,26] else #[4,5,0,2,8]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[11,10,28,30,7] else #[10,11,29,31,21]) else (if i.val < 27 then #[9,8,13,15,22] else #[8,9,12,14,4])) else (if i.val < 30 then (if i.val < 29 then #[15,14,24,26,3] else #[14,15,25,27,17]) else (if i.val < 31 then #[13,12,9,11,18] else #[12,13,8,10,0]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 12) else (if i.val < 3 then 29 else 31)) else (if i.val < 6 then (if i.val < 5 then 21 else 28) else (if i.val < 7 then 16 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 19) else (if i.val < 11 then 4 else 20)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 15 else 22)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 27) else (if i.val < 19 then 17 else 9)) else (if i.val < 22 then (if i.val < 21 then 26 else 18) else (if i.val < 23 then 23 else 14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 11 else 8) else (if i.val < 27 then 10 else 7)) else (if i.val < 30 then (if i.val < 29 then 24 else 13) else (if i.val < 31 then 6 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 13) else (if i.val < 3 then 23 else 22)) else (if i.val < 6 then (if i.val < 5 then 27 else 23) else (if i.val < 7 then 10 else 24))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 30) else (if i.val < 11 then 31 else 30)) else (if i.val < 14 then (if i.val < 13 then 31 else 31) else (if i.val < 15 then 10 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 15 else 29) else (if i.val < 19 then 0 else 12)) else (if i.val < 22 then (if i.val < 21 then 1 else 0) else (if i.val < 23 then 26 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 13 else 12) else (if i.val < 27 then 13 else 12)) else (if i.val < 30 then (if i.val < 29 then 24 else 8) else (if i.val < 31 then 12 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 4) else (if i.val < 3 then 3 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 1) else (if i.val < 7 then 4 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 2 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 4) else (if i.val < 19 then 1 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 3) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 3) else (if i.val < 27 then 2 else 2)) else (if i.val < 30 then (if i.val < 29 then 2 else 3) else (if i.val < 31 then 1 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,13,26,24,16] else (if i.val < 2 then #[12,30,27,10,0] else #[12,30,27,25,19])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,13,26,24,16] else (if i.val < 2 then #[12,30,27,10,0] else #[12,30,27,25,19])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 31) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,0] else #[0,1,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,0] else #[0,1,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[31,3,6] else #[31,19,23]) : Array (Fin 32))[j.val]!
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

end N19

namespace N20
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 16 else (if j.val < 4 then 21 else 1))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 12 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 35) else (if i.val < 19 then 37 else 38)) else (if i.val < 22 then (if i.val < 21 then 40 else 43) else (if i.val < 23 then 45 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 50) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[19,18,22,20,15] else #[18,19,23,21,29]) else (if i.val < 3 then #[17,16,7,5,30] else #[16,17,6,4,12])) else (if i.val < 6 then (if i.val < 5 then #[23,22,18,16,11] else #[22,23,19,17,25]) else (if i.val < 7 then #[21,20,3,1,26] else #[20,21,2,0,8]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[27,26,31,29,23] else #[26,27,30,28,5]) else (if i.val < 11 then #[25,24,14,12,6] else #[24,25,15,13,20])) else (if i.val < 14 then (if i.val < 13 then #[31,30,27,25,19] else #[30,31,26,24,1]) else (if i.val < 15 then #[29,28,10,8,2] else #[28,29,11,9,16])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[3,2,21,23,31] else #[2,3,20,22,13]) else (if i.val < 19 then #[1,0,4,6,14] else #[0,1,5,7,28])) else (if i.val < 22 then (if i.val < 21 then #[7,6,17,19,27] else #[6,7,16,18,9]) else (if i.val < 23 then #[5,4,0,2,10] else #[4,5,1,3,24]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[11,10,28,30,7] else #[10,11,29,31,21]) else (if i.val < 27 then #[9,8,13,15,22] else #[8,9,12,14,4])) else (if i.val < 30 then (if i.val < 29 then #[15,14,24,26,3] else #[14,15,25,27,17]) else (if i.val < 31 then #[13,12,9,11,18] else #[12,13,8,10,0]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 12) else (if i.val < 3 then 30 else 29)) else (if i.val < 6 then (if i.val < 5 then 23 else 25) else (if i.val < 7 then 16 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 21) else (if i.val < 11 then 4 else 22)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 15 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 31 else 28) else (if i.val < 19 then 17 else 9)) else (if i.val < 22 then (if i.val < 21 then 19 else 24) else (if i.val < 23 then 18 else 14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 11 else 8) else (if i.val < 27 then 10 else 7)) else (if i.val < 30 then (if i.val < 29 then 27 else 13) else (if i.val < 31 then 6 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 13) else (if i.val < 3 then 14 else 23)) else (if i.val < 6 then (if i.val < 5 then 27 else 19) else (if i.val < 7 then 10 else 19))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 30) else (if i.val < 11 then 31 else 30)) else (if i.val < 14 then (if i.val < 13 then 31 else 31) else (if i.val < 15 then 10 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 15 else 29) else (if i.val < 19 then 0 else 12)) else (if i.val < 22 then (if i.val < 21 then 0 else 25) else (if i.val < 23 then 0 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 13 else 12) else (if i.val < 27 then 13 else 12)) else (if i.val < 30 then (if i.val < 29 then 19 else 8) else (if i.val < 31 then 12 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 4) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 2) else (if i.val < 7 then 4 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 2 else 4)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 4) else (if i.val < 19 then 1 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 4) else (if i.val < 23 then 2 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 3) else (if i.val < 27 then 2 else 2)) else (if i.val < 30 then (if i.val < 29 then 4 else 3) else (if i.val < 31 then 1 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,13,26,24,16] else (if i.val < 2 then #[12,30,27,10,16] else #[12,30,27,25,17])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,13,26,24,16] else (if i.val < 2 then #[12,30,27,10,16] else #[12,30,27,25,17])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 31) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,1] else #[0,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,1] else #[0,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[31,3,7] else #[31,19,22]) : Array (Fin 32))[j.val]!
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

end N20

namespace N21
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 16 else (if j.val < 4 then 21 else 17))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 17) else (if i.val < 3 then 18 else 19)) else (if i.val < 6 then (if i.val < 5 then 20 else 21) else (if i.val < 7 then 22 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 25) else (if i.val < 11 then 26 else 27)) else (if i.val < 14 then (if i.val < 13 then 28 else 29) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 48 else 49) else (if i.val < 19 then 50 else 51)) else (if i.val < 22 then (if i.val < 21 then 52 else 53) else (if i.val < 23 then 54 else 55))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[23,20,31,26,30] else #[22,21,29,24,28]) else (if i.val < 3 then #[21,22,30,27,31] else #[20,23,28,25,29])) else (if i.val < 6 then (if i.val < 5 then #[19,16,15,10,14] else #[18,17,13,8,12]) else (if i.val < 7 then #[17,18,14,11,15] else #[16,19,12,9,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[31,28,23,18,22] else #[30,29,21,16,20]) else (if i.val < 11 then #[29,30,22,19,23] else #[28,31,20,17,21])) else (if i.val < 14 then (if i.val < 13 then #[27,24,7,2,6] else #[26,25,5,0,4]) else (if i.val < 15 then #[25,26,6,3,7] else #[24,27,4,1,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[7,4,27,30,26] else #[6,5,25,28,24]) else (if i.val < 19 then #[5,6,26,31,27] else #[4,7,24,29,25])) else (if i.val < 22 then (if i.val < 21 then #[3,0,11,14,10] else #[2,1,9,12,8]) else (if i.val < 23 then #[1,2,10,15,11] else #[0,3,8,13,9]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,12,19,22,18] else #[14,13,17,20,16]) else (if i.val < 27 then #[13,14,18,23,19] else #[12,15,16,21,17])) else (if i.val < 30 then (if i.val < 29 then #[11,8,3,6,2] else #[10,9,1,4,0]) else (if i.val < 31 then #[9,10,2,7,3] else #[8,11,0,5,1]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 5) else (if i.val < 3 then 21 else 19)) else (if i.val < 6 then (if i.val < 5 then 30 else 4) else (if i.val < 7 then 20 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 22) else (if i.val < 11 then 24 else 2)) else (if i.val < 14 then (if i.val < 13 then 16 else 15) else (if i.val < 15 then 26 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 31 else 11) else (if i.val < 19 then 8 else 28)) else (if i.val < 22 then (if i.val < 21 then 10 else 12) else (if i.val < 23 then 9 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 18 else 27) else (if i.val < 27 then 13 else 23)) else (if i.val < 30 then (if i.val < 29 then 6 else 17) else (if i.val < 31 then 14 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 28 else 28)) else (if i.val < 6 then (if i.val < 5 then 13 else 31) else (if i.val < 7 then 28 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 23) else (if i.val < 11 then 22 else 31)) else (if i.val < 14 then (if i.val < 13 then 5 else 5) else (if i.val < 15 then 20 else 22)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 11) else (if i.val < 19 then 8 else 26)) else (if i.val < 22 then (if i.val < 21 then 11 else 11) else (if i.val < 23 then 8 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 17) else (if i.val < 27 then 0 else 18)) else (if i.val < 30 then (if i.val < 29 then 8 else 1) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 4 else 2)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 3 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 4) else (if i.val < 11 then 2 else 1)) else (if i.val < 14 then (if i.val < 13 then 4 else 2) else (if i.val < 15 then 3 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 3) else (if i.val < 19 then 3 else 4)) else (if i.val < 22 then (if i.val < 21 then 2 else 4) else (if i.val < 23 then 4 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 2) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 1 else 2) else (if i.val < 31 then 4 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[8,11,20,17,21] else (if i.val < 2 then #[8,28,23,5,7] else #[8,28,23,18,19])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[8,11,20,17,21] else (if i.val < 2 then #[8,28,23,5,7] else #[8,28,23,18,19])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 6) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,1] else #[1,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,1] else #[1,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 1) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[15,31,3] else #[30,31,3]) : Array (Fin 32))[j.val]!
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

end N21

namespace N22
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else (if j.val < 4 then 0 else 1))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 25) else (if i.val < 11 then 26 else 27)) else (if i.val < 14 then (if i.val < 13 then 28 else 29) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 33) else (if i.val < 19 then 34 else 35)) else (if i.val < 22 then (if i.val < 21 then 36 else 37) else (if i.val < 23 then 38 else 39))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[23,20,18,31,30] else #[22,21,19,15,14]) else (if i.val < 3 then #[21,22,16,27,26] else #[20,23,17,11,10])) else (if i.val < 6 then (if i.val < 5 then #[19,16,22,29,28] else #[18,17,23,13,12]) else (if i.val < 7 then #[17,18,20,25,24] else #[16,19,21,9,8]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[31,28,26,23,22] else #[30,29,27,7,6]) else (if i.val < 11 then #[29,30,24,19,18] else #[28,31,25,3,2])) else (if i.val < 14 then (if i.val < 13 then #[27,24,30,21,20] else #[26,25,31,5,4]) else (if i.val < 15 then #[25,26,28,17,16] else #[24,27,29,1,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[7,4,2,30,31] else #[6,5,3,14,15]) else (if i.val < 19 then #[5,6,0,26,27] else #[4,7,1,10,11])) else (if i.val < 22 then (if i.val < 21 then #[3,0,6,28,29] else #[2,1,7,12,13]) else (if i.val < 23 then #[1,2,4,24,25] else #[0,3,5,8,9]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,12,10,22,23] else #[14,13,11,6,7]) else (if i.val < 27 then #[13,14,8,18,19] else #[12,15,9,2,3])) else (if i.val < 30 then (if i.val < 29 then #[11,8,14,20,21] else #[10,9,15,4,5]) else (if i.val < 31 then #[9,10,12,16,17] else #[8,11,13,0,1]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 5) else (if i.val < 3 then 12 else 11)) else (if i.val < 6 then (if i.val < 5 then 14 else 13) else (if i.val < 7 then 24 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 22) else (if i.val < 11 then 27 else 2)) else (if i.val < 14 then (if i.val < 13 then 30 else 3) else (if i.val < 15 then 21 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 28 else 26) else (if i.val < 19 then 16 else 19)) else (if i.val < 22 then (if i.val < 21 then 15 else 18) else (if i.val < 23 then 9 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 23 else 10) else (if i.val < 27 then 7 else 29)) else (if i.val < 30 then (if i.val < 29 then 6 else 31) else (if i.val < 31 then 17 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 11 else 11)) else (if i.val < 6 then (if i.val < 5 then 13 else 13) else (if i.val < 7 then 25 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 23) else (if i.val < 11 then 3 else 31)) else (if i.val < 14 then (if i.val < 13 then 5 else 31) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 3) else (if i.val < 19 then 0 else 1)) else (if i.val < 22 then (if i.val < 21 then 0 else 1) else (if i.val < 23 then 8 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 11) else (if i.val < 27 then 8 else 2)) else (if i.val < 30 then (if i.val < 29 then 8 else 4) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 4) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 3 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 4) else (if i.val < 11 then 4 else 1)) else (if i.val < 14 then (if i.val < 13 then 4 else 2) else (if i.val < 15 then 4 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 2 else 2)) else (if i.val < 22 then (if i.val < 21 then 1 else 1) else (if i.val < 23 then 4 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 2) else (if i.val < 27 then 2 else 3)) else (if i.val < 30 then (if i.val < 29 then 1 else 3) else (if i.val < 31 then 4 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[8,11,13,17,16] else (if i.val < 2 then #[8,28,26,0,16] else #[8,28,13,23,19])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[8,11,13,17,16] else (if i.val < 2 then #[8,28,26,0,16] else #[8,28,13,23,19])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 13) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,0,1] else #[1,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,0,1] else #[1,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 2) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[15,6,31] else #[29,6,31]) : Array (Fin 32))[j.val]!
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

end N22

namespace N23
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else (if j.val < 4 then 0 else 9))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 12 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 18) else (if i.val < 11 then 20 else 23)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 34) else (if i.val < 19 then 36 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 43) else (if i.val < 23 then 45 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 51) else (if i.val < 27 then 53 else 54)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[19,18,17,31,27] else #[18,19,16,13,9]) else (if i.val < 3 then #[17,16,19,14,25] else #[16,17,18,28,11])) else (if i.val < 6 then (if i.val < 5 then #[23,22,21,11,29] else #[22,23,20,25,15]) else (if i.val < 7 then #[21,20,23,26,31] else #[20,21,22,8,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[27,26,25,7,17] else #[26,27,24,21,3]) else (if i.val < 11 then #[25,24,27,22,19] else #[24,25,26,4,1])) else (if i.val < 14 then (if i.val < 13 then #[31,30,29,19,23] else #[30,31,28,1,5]) else (if i.val < 15 then #[29,28,31,2,21] else #[28,29,30,16,7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[3,2,1,15,24] else #[2,3,0,29,10]) else (if i.val < 19 then #[1,0,3,30,26] else #[0,1,2,12,8])) else (if i.val < 22 then (if i.val < 21 then #[7,6,5,27,30] else #[6,7,4,9,12]) else (if i.val < 23 then #[5,4,7,10,28] else #[4,5,6,24,14]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[11,10,9,23,18] else #[10,11,8,5,0]) else (if i.val < 27 then #[9,8,11,6,16] else #[8,9,10,20,2])) else (if i.val < 30 then (if i.val < 29 then #[15,14,13,3,20] else #[14,15,12,17,6]) else (if i.val < 31 then #[13,12,15,18,22] else #[12,13,14,0,4]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 11) else (if i.val < 3 then 13 else 24)) else (if i.val < 6 then (if i.val < 5 then 5 else 12) else (if i.val < 7 then 21 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 27) else (if i.val < 11 then 31 else 19)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 3 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 16) else (if i.val < 19 then 15 else 8)) else (if i.val < 22 then (if i.val < 21 then 25 else 14) else (if i.val < 23 then 18 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 23 else 28) else (if i.val < 27 then 30 else 17)) else (if i.val < 30 then (if i.val < 29 then 10 else 7) else (if i.val < 31 then 6 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 13) else (if i.val < 3 then 14 else 28)) else (if i.val < 6 then (if i.val < 5 then 31 else 13) else (if i.val < 7 then 29 else 21))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 19 else 1) else (if i.val < 11 then 17 else 4)) else (if i.val < 14 then (if i.val < 13 then 31 else 31) else (if i.val < 15 then 31 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 0) else (if i.val < 19 then 0 else 12)) else (if i.val < 22 then (if i.val < 21 then 28 else 14) else (if i.val < 23 then 4 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 23 else 5) else (if i.val < 27 then 18 else 0)) else (if i.val < 30 then (if i.val < 29 then 13 else 12) else (if i.val < 31 then 12 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 3 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 4) else (if i.val < 7 then 4 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 4) else (if i.val < 11 then 4 else 3)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 2 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 1 else 3)) else (if i.val < 22 then (if i.val < 21 then 4 else 4) else (if i.val < 23 then 1 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 3) else (if i.val < 27 then 4 else 4)) else (if i.val < 30 then (if i.val < 29 then 2 else 2) else (if i.val < 31 then 1 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,13,14,16,21] else (if i.val < 2 then #[12,30,29,0,7] else #[12,30,14,19,6])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,13,14,16,21] else (if i.val < 2 then #[12,30,29,0,7] else #[12,30,14,19,6])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 31) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,1] else #[0,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,1] else #[0,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[31,3,7] else #[31,19,22]) : Array (Fin 32))[j.val]!
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

end N23

namespace N24
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else (if j.val < 4 then 1 else 8))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 8 else 11) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 18) else (if i.val < 11 then 20 else 23)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 35) else (if i.val < 19 then 37 else 38)) else (if i.val < 22 then (if i.val < 21 then 41 else 42) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 51) else (if i.val < 27 then 53 else 54)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[19,18,17,15,25] else #[18,19,16,29,11]) else (if i.val < 3 then #[17,16,19,30,27] else #[16,17,18,12,9])) else (if i.val < 6 then (if i.val < 5 then #[23,22,21,27,31] else #[22,23,20,9,13]) else (if i.val < 7 then #[21,20,23,10,29] else #[20,21,22,24,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[27,26,25,7,17] else #[26,27,24,21,3]) else (if i.val < 11 then #[25,24,27,22,19] else #[24,25,26,4,1])) else (if i.val < 14 then (if i.val < 13 then #[31,30,29,19,23] else #[30,31,28,1,5]) else (if i.val < 15 then #[29,28,31,2,21] else #[28,29,30,16,7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[3,2,1,31,26] else #[2,3,0,13,8]) else (if i.val < 19 then #[1,0,3,14,24] else #[0,1,2,28,10])) else (if i.val < 22 then (if i.val < 21 then #[7,6,5,11,28] else #[6,7,4,25,14]) else (if i.val < 23 then #[5,4,7,26,30] else #[4,5,6,8,12]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[11,10,9,23,18] else #[10,11,8,5,0]) else (if i.val < 27 then #[9,8,11,6,16] else #[8,9,10,20,2])) else (if i.val < 30 then (if i.val < 29 then #[15,14,13,3,20] else #[14,15,12,17,6]) else (if i.val < 31 then #[13,12,15,18,22] else #[12,13,14,0,4]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 11) else (if i.val < 3 then 13 else 24)) else (if i.val < 6 then (if i.val < 5 then 5 else 12) else (if i.val < 7 then 21 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 23 else 28) else (if i.val < 11 then 22 else 27)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 3 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 16) else (if i.val < 19 then 15 else 8)) else (if i.val < 22 then (if i.val < 21 then 25 else 14) else (if i.val < 23 then 19 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 30 else 18) else (if i.val < 27 then 31 else 20)) else (if i.val < 30 then (if i.val < 29 then 10 else 7) else (if i.val < 31 then 6 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 13) else (if i.val < 3 then 14 else 28)) else (if i.val < 6 then (if i.val < 5 then 31 else 13) else (if i.val < 7 then 29 else 21))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 23 else 5) else (if i.val < 11 then 19 else 1)) else (if i.val < 14 then (if i.val < 13 then 31 else 31) else (if i.val < 15 then 31 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 0) else (if i.val < 19 then 0 else 12)) else (if i.val < 22 then (if i.val < 21 then 28 else 14) else (if i.val < 23 then 4 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 18 else 0) else (if i.val < 27 then 22 else 4)) else (if i.val < 30 then (if i.val < 29 then 13 else 12) else (if i.val < 31 then 12 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 3 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 4) else (if i.val < 7 then 4 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 4 else 4)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 2 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 1 else 3)) else (if i.val < 22 then (if i.val < 21 then 4 else 4) else (if i.val < 23 then 1 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 4) else (if i.val < 27 then 3 else 3)) else (if i.val < 30 then (if i.val < 29 then 2 else 2) else (if i.val < 31 then 1 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,13,14,16,21] else (if i.val < 2 then #[12,30,29,16,23] else #[12,30,14,17,4])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[12,13,14,16,21] else (if i.val < 2 then #[12,30,29,16,23] else #[12,30,14,17,4])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 31) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,0] else #[0,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,0] else #[0,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[31,3,6] else #[31,19,23]) : Array (Fin 32))[j.val]!
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

end N24

namespace N25
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 24 else 27) else (if j.val < 3 then 29 else (if j.val < 4 then 8 else 9))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 9) else (if i.val < 3 then 10 else 11)) else (if i.val < 6 then (if i.val < 5 then 12 else 13) else (if i.val < 7 then 14 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 25) else (if i.val < 11 then 26 else 27)) else (if i.val < 14 then (if i.val < 13 then 28 else 29) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 40 else 41) else (if i.val < 19 then 42 else 43)) else (if i.val < 22 then (if i.val < 21 then 44 else 45) else (if i.val < 23 then 46 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[23,20,18,31,30] else #[22,21,19,27,26]) else (if i.val < 3 then #[21,22,16,15,14] else #[20,23,17,11,10])) else (if i.val < 6 then (if i.val < 5 then #[19,16,22,30,31] else #[18,17,23,26,27]) else (if i.val < 7 then #[17,18,20,14,15] else #[16,19,21,10,11]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[31,28,26,23,22] else #[30,29,27,19,18]) else (if i.val < 11 then #[29,30,24,7,6] else #[28,31,25,3,2])) else (if i.val < 14 then (if i.val < 13 then #[27,24,30,22,23] else #[26,25,31,18,19]) else (if i.val < 15 then #[25,26,28,6,7] else #[24,27,29,2,3])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[7,4,2,29,28] else #[6,5,3,25,24]) else (if i.val < 19 then #[5,6,0,13,12] else #[4,7,1,9,8])) else (if i.val < 22 then (if i.val < 21 then #[3,0,6,28,29] else #[2,1,7,24,25]) else (if i.val < 23 then #[1,2,4,12,13] else #[0,3,5,8,9]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,12,10,21,20] else #[14,13,11,17,16]) else (if i.val < 27 then #[13,14,8,5,4] else #[12,15,9,1,0])) else (if i.val < 30 then (if i.val < 29 then #[11,8,14,20,21] else #[10,9,15,16,17]) else (if i.val < 31 then #[9,10,12,4,5] else #[8,11,13,0,1]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 5) else (if i.val < 3 then 12 else 11)) else (if i.val < 6 then (if i.val < 5 then 21 else 20) else (if i.val < 7 then 28 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 22) else (if i.val < 11 then 26 else 2)) else (if i.val < 14 then (if i.val < 13 then 23 else 3) else (if i.val < 15 then 19 else 27)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 25 else 24) else (if i.val < 19 then 13 else 14)) else (if i.val < 22 then (if i.val < 21 then 15 else 17) else (if i.val < 23 then 9 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 31 else 10) else (if i.val < 27 then 7 else 18)) else (if i.val < 30 then (if i.val < 29 then 6 else 30) else (if i.val < 31 then 16 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 11 else 11)) else (if i.val < 6 then (if i.val < 5 then 26 else 26) else (if i.val < 7 then 18 else 19))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 23) else (if i.val < 11 then 3 else 31)) else (if i.val < 14 then (if i.val < 13 then 22 else 31) else (if i.val < 15 then 28 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 25 else 25) else (if i.val < 19 then 13 else 13)) else (if i.val < 22 then (if i.val < 21 then 0 else 1) else (if i.val < 23 then 8 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 11) else (if i.val < 27 then 8 else 1)) else (if i.val < 30 then (if i.val < 29 then 8 else 20) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 4) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 4) else (if i.val < 11 then 4 else 1)) else (if i.val < 14 then (if i.val < 13 then 3 else 2) else (if i.val < 15 then 2 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 3) else (if i.val < 19 then 3 else 4)) else (if i.val < 22 then (if i.val < 21 then 1 else 1) else (if i.val < 23 then 4 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 2) else (if i.val < 27 then 2 else 3)) else (if i.val < 30 then (if i.val < 29 then 1 else 4) else (if i.val < 31 then 4 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[8,11,13,18,19] else (if i.val < 2 then #[8,28,26,23,7] else #[8,28,13,0,4])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[8,11,13,18,19] else (if i.val < 2 then #[8,28,26,23,7] else #[8,28,13,0,4])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 6) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,0] else #[1,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,0] else #[1,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 1) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[15,31,5] else #[30,31,5]) : Array (Fin 32))[j.val]!
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

end N25

namespace N26
def normalGenerators (j : Fin 6) : Source := ⟨((if j.val < 3 then (if j.val < 1 then 24 else (if j.val < 2 then 27 else 16)) else (if j.val < 4 then 21 else (if j.val < 5 then 0 else 1))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63)))))) : Fin 64)
private def next (i : Fin 64) (j : Fin 6) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[39,36,47,42,63,62] else #[38,37,45,40,31,30]) else (if i.val < 3 then #[37,38,46,43,59,58] else #[36,39,44,41,27,26])) else (if i.val < 6 then (if i.val < 5 then #[35,32,15,10,61,60] else #[34,33,13,8,29,28]) else (if i.val < 7 then #[33,34,14,11,57,56] else #[32,35,12,9,25,24]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[47,44,39,34,55,54] else #[46,45,37,32,23,22]) else (if i.val < 11 then #[45,46,38,35,51,50] else #[44,47,36,33,19,18])) else (if i.val < 14 then (if i.val < 13 then #[43,40,7,2,53,52] else #[42,41,5,0,21,20]) else (if i.val < 15 then #[41,42,6,3,49,48] else #[40,43,4,1,17,16])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[55,52,63,58,47,46] else #[54,53,61,56,15,14]) else (if i.val < 19 then #[53,54,62,59,43,42] else #[52,55,60,57,11,10])) else (if i.val < 22 then (if i.val < 21 then #[51,48,31,26,45,44] else #[50,49,29,24,13,12]) else (if i.val < 23 then #[49,50,30,27,41,40] else #[48,51,28,25,9,8]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[63,60,55,50,39,38] else #[62,61,53,48,7,6]) else (if i.val < 27 then #[61,62,54,51,35,34] else #[60,63,52,49,3,2])) else (if i.val < 30 then (if i.val < 29 then #[59,56,23,18,37,36] else #[58,57,21,16,5,4]) else (if i.val < 31 then #[57,58,22,19,33,32] else #[56,59,20,17,1,0]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[7,4,43,46,62,63] else #[6,5,41,44,30,31]) else (if i.val < 35 then #[5,6,42,47,58,59] else #[4,7,40,45,26,27])) else (if i.val < 38 then (if i.val < 37 then #[3,0,11,14,60,61] else #[2,1,9,12,28,29]) else (if i.val < 39 then #[1,2,10,15,56,57] else #[0,3,8,13,24,25]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[15,12,35,38,54,55] else #[14,13,33,36,22,23]) else (if i.val < 43 then #[13,14,34,39,50,51] else #[12,15,32,37,18,19])) else (if i.val < 46 then (if i.val < 45 then #[11,8,3,6,52,53] else #[10,9,1,4,20,21]) else (if i.val < 47 then #[9,10,2,7,48,49] else #[8,11,0,5,16,17])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[23,20,59,62,46,47] else #[22,21,57,60,14,15]) else (if i.val < 51 then #[21,22,58,63,42,43] else #[20,23,56,61,10,11])) else (if i.val < 54 then (if i.val < 53 then #[19,16,27,30,44,45] else #[18,17,25,28,12,13]) else (if i.val < 55 then #[17,18,26,31,40,41] else #[16,19,24,29,8,9]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[31,28,51,54,38,39] else #[30,29,49,52,6,7]) else (if i.val < 59 then #[29,30,50,55,34,35] else #[28,31,48,53,2,3])) else (if i.val < 62 then (if i.val < 61 then #[27,24,19,22,36,37] else #[26,25,17,20,4,5]) else (if i.val < 63 then #[25,26,18,23,32,33] else #[24,27,16,21,0,1])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 6) else (if i.val < 3 then 15 else 14)) else (if i.val < 6 then (if i.val < 5 then 52 else 48) else (if i.val < 7 then 63 else 50))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 32 else 33) else (if i.val < 11 then 36 else 47)) else (if i.val < 14 then (if i.val < 13 then 21 else 20) else (if i.val < 15 then 41 else 37)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 49) else (if i.val < 19 then 57 else 30)) else (if i.val < 22 then (if i.val < 21 then 53 else 4) else (if i.val < 23 then 31 else 58))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 35) else (if i.val < 27 then 43 else 2)) else (if i.val < 30 then (if i.val < 29 then 61 else 19) else (if i.val < 31 then 29 else 28))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 59 else 60) else (if i.val < 35 then 45 else 46)) else (if i.val < 38 then (if i.val < 37 then 22 else 25) else (if i.val < 39 then 11 else 10))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 27 else 42) else (if i.val < 43 then 23 else 34)) else (if i.val < 46 then (if i.val < 45 then 40 else 26) else (if i.val < 47 then 18 else 17)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 51 else 13) else (if i.val < 51 then 9 else 56)) else (if i.val < 54 then (if i.val < 53 then 12 else 54) else (if i.val < 55 then 62 else 8))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 39) else (if i.val < 59 then 16 else 44)) else (if i.val < 62 then (if i.val < 61 then 7 else 55) else (if i.val < 63 then 24 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 63) else (if i.val < 3 then 27 else 27)) else (if i.val < 6 then (if i.val < 5 then 29 else 47) else (if i.val < 7 then 25 else 46))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 55 else 55) else (if i.val < 11 then 38 else 47)) else (if i.val < 14 then (if i.val < 13 then 21 else 21) else (if i.val < 15 then 49 else 38)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 63 else 47) else (if i.val < 19 then 62 else 60)) else (if i.val < 22 then (if i.val < 21 then 13 else 63) else (if i.val < 23 then 60 else 62))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 63 else 39) else (if i.val < 27 then 3 else 63)) else (if i.val < 30 then (if i.val < 29 then 37 else 21) else (if i.val < 31 then 1 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 62 else 62) else (if i.val < 35 then 58 else 58)) else (if i.val < 38 then (if i.val < 37 then 0 else 1) else (if i.val < 39 then 24 else 24))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 1 else 3) else (if i.val < 43 then 0 else 50)) else (if i.val < 46 then (if i.val < 45 then 52 else 1) else (if i.val < 47 then 16 else 16)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 46 else 27) else (if i.val < 51 then 24 else 42)) else (if i.val < 54 then (if i.val < 53 then 27 else 12) else (if i.val < 55 then 40 else 24))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 38) else (if i.val < 59 then 16 else 2)) else (if i.val < 62 then (if i.val < 61 then 24 else 36) else (if i.val < 63 then 0 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 6 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 5) else (if i.val < 3 then 5 else 4)) else (if i.val < 6 then (if i.val < 5 then 5 else 3) else (if i.val < 7 then 5 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 2 else 1)) else (if i.val < 14 then (if i.val < 13 then 5 else 4) else (if i.val < 15 then 4 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 5) else (if i.val < 19 then 2 else 2)) else (if i.val < 22 then (if i.val < 21 then 5 else 3) else (if i.val < 23 then 3 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 5) else (if i.val < 27 then 5 else 1)) else (if i.val < 30 then (if i.val < 29 then 4 else 2) else (if i.val < 31 then 5 else 4))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 4 else 5) else (if i.val < 35 then 4 else 5)) else (if i.val < 38 then (if i.val < 37 then 1 else 1) else (if i.val < 39 then 5 else 4))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 3 else 3) else (if i.val < 43 then 3 else 5)) else (if i.val < 46 then (if i.val < 45 then 4 else 2) else (if i.val < 47 then 5 else 4)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 4 else 3) else (if i.val < 51 then 3 else 5)) else (if i.val < 54 then (if i.val < 53 then 2 else 4) else (if i.val < 55 then 4 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 4 else 5) else (if i.val < 59 then 3 else 4)) else (if i.val < 62 then (if i.val < 61 then 1 else 5) else (if i.val < 63 then 5 else 0)))))) : Fin 6)

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

private def posWitness (i : Fin 3) (j : Fin 6) : Fin 64 := ((if i.val < 1 then #[24,27,52,49,33,32] else (if i.val < 2 then #[24,60,55,21,0,32] else #[24,60,55,50,39,35])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 6) : Fin 64 := ((if i.val < 1 then #[24,27,52,49,33,32] else (if i.val < 2 then #[24,60,55,21,0,32] else #[24,60,55,50,39,35])) : Array (Fin 64))[j.val]!
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
private def stepWitness (i : Fin 1) (j : Fin 3) : Fin 64 := (#[31,6,13] : Array (Fin 64))[j.val]!
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

end N26

@[reducible] def states (i : Fin 27) : BinaryNormalState generators :=
  (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then N0.state else (if i.val < 2 then N1.state else N2.state)) else (if i.val < 4 then N3.state else (if i.val < 5 then N4.state else N5.state))) else (if i.val < 9 then (if i.val < 7 then N6.state else (if i.val < 8 then N7.state else N8.state)) else (if i.val < 11 then (if i.val < 10 then N9.state else N10.state) else (if i.val < 12 then N11.state else N12.state)))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then N13.state else (if i.val < 15 then N14.state else N15.state)) else (if i.val < 18 then (if i.val < 17 then N16.state else N17.state) else (if i.val < 19 then N18.state else N19.state))) else (if i.val < 23 then (if i.val < 21 then N20.state else (if i.val < 22 then N21.state else N22.state)) else (if i.val < 25 then (if i.val < 24 then N23.state else N24.state) else (if i.val < 26 then N25.state else N26.state)))))

end SymmetricSubgroupAsymptotics.RDTBinaryNormal8T31
