import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T29

/-! Exact original normal states and quotient rows for 8T29.
Selected by external selected_missing_normal_registry.py; all finite facts are checked
in Lean's kernel. This file certifies normal-state coverage, not the later
pair/character/transport acceptance of those states. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.RDTBinaryNormal8T29

abbrev Source := FiniteGroupRow 64
local instance : Group Source := BinaryMenuCayley8T29.group

def generators (j : Fin 5) : Source :=
  ⟨BinaryMenuCayley8T29.certificate.next BinaryMenuCayley8T29.certificate.identity j⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  apply binaryNormal_full_generators_of_equiv BinaryMenuCayley8T29.generators
    generators BinaryMenuCayley8T29.originalEquiv
  intro j
  change BinaryMenuCayley8T29.certificate.toCayley.elements
    (BinaryMenuCayley8T29.certificate.toCayley.next
      BinaryMenuCayley8T29.certificate.toCayley.identity j)=_
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

private def representatives (i : Fin 64) : Source := ⟨((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 5) else (if i.val < 3 then 10 else 28)) else (if i.val < 6 then (if i.val < 5 then 57 else 59) else (if i.val < 7 then 16 else 35))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 1) else (if i.val < 11 then 41 else 12)) else (if i.val < 14 then (if i.val < 13 then 14 else 31) else (if i.val < 15 then 24 else 22)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 58) else (if i.val < 19 then 61 else 20)) else (if i.val < 22 then (if i.val < 21 then 56 else 54) else (if i.val < 23 then 39 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 7 else 2) else (if i.val < 27 then 42 else 45)) else (if i.val < 30 then (if i.val < 29 then 53 else 15) else (if i.val < 31 then 8 else 13))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 25 else 27) else (if i.val < 35 then 50 else 30)) else (if i.val < 38 then (if i.val < 37 then 21 else 18) else (if i.val < 39 then 38 else 36))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 44 else 60) else (if i.val < 43 then 62 else 23)) else (if i.val < 46 then (if i.val < 45 then 52 else 33) else (if i.val < 47 then 51 else 6)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 4 else 43) else (if i.val < 51 then 46 else 49)) else (if i.val < 54 then (if i.val < 53 then 9 else 11) else (if i.val < 55 then 26 else 29))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 19 else 17) else (if i.val < 59 then 37 else 34)) else (if i.val < 62 then (if i.val < 61 then 47 else 40) else (if i.val < 63 then 48 else 55)))))) : Fin 64)⟩
private def quotientNext (i : Fin 64) (j : Fin 5) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3,4,5] else #[0,6,7,8,9]) else (if i.val < 3 then #[6,0,10,11,12] else #[7,10,0,13,14])) else (if i.val < 6 then (if i.val < 5 then #[15,11,16,17,18] else #[19,12,14,20,0]) else (if i.val < 7 then #[2,1,21,15,19] else #[3,21,1,16,22]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,15,13,23,24] else #[12,19,22,25,1]) else (if i.val < 11 then #[21,3,2,26,27] else #[8,4,28,29,30])) else (if i.val < 14 then (if i.val < 13 then #[9,5,27,31,2] else #[28,26,8,32,33]) else (if i.val < 15 then #[34,27,5,35,3] else #[4,8,26,36,37])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[26,28,4,38,39] else #[23,29,40,41,42]) else (if i.val < 19 then #[24,30,39,5,4] else #[5,9,34,43,6])) else (if i.val < 22 then (if i.val < 21 then #[25,31,44,42,41] else #[10,7,6,28,34]) else (if i.val < 23 then #[27,34,9,45,7] else #[17,36,46,47,48]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,37,33,9,8] else #[20,43,49,48,47]) else (if i.val < 27 then #[16,13,15,40,50] else #[22,14,12,49,10])) else (if i.val < 30 then (if i.val < 29 then #[13,16,11,46,51] else #[36,17,32,52,53]) else (if i.val < 31 then #[37,18,51,12,11] else #[43,20,45,53,52]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[38,40,29,54,55] else #[39,50,24,14,13]) else (if i.val < 35 then #[14,22,19,44,21] else #[45,49,43,55,54])) else (if i.val < 38 then (if i.val < 37 then #[29,23,38,56,57] else #[30,24,50,19,15]) else (if i.val < 39 then #[32,46,36,58,59] else #[33,51,18,22,16]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[46,32,17,60,61] else #[56,52,62,0,20]) else (if i.val < 43 then #[57,53,61,18,17] else #[31,25,35,57,56])) else (if i.val < 46 then (if i.val < 45 then #[49,45,20,63,62] else #[35,44,31,59,58]) else (if i.val < 47 then #[40,38,23,62,63] else #[52,56,60,1,25])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[53,57,63,24,23] else #[44,35,25,61,60]) else (if i.val < 51 then #[51,33,37,27,26] else #[50,39,30,34,28])) else (if i.val < 54 then (if i.val < 53 then #[47,41,58,2,31] else #[48,42,55,30,29]) else (if i.val < 55 then #[62,60,56,3,35] else #[63,61,53,33,32]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[41,47,54,6,43] else #[42,48,59,37,36]) else (if i.val < 59 then #[60,62,52,7,45] else #[61,63,57,39,38])) else (if i.val < 62 then (if i.val < 61 then #[58,54,47,10,49] else #[59,55,42,50,40]) else (if i.val < 63 then #[54,58,41,21,44] else #[55,59,48,51,46])))))) : Array (Fin 64))[j.val]!
private def quotientPrev (i : Fin 64) (j : Fin 5) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3,41,5] else #[0,6,7,47,9]) else (if i.val < 3 then #[6,0,10,52,12] else #[7,10,0,54,14])) else (if i.val < 6 then (if i.val < 5 then #[15,11,16,0,18] else #[19,12,14,18,0]) else (if i.val < 7 then #[2,1,21,56,19] else #[3,21,1,58,22]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,15,13,1,24] else #[12,19,22,24,1]) else (if i.val < 11 then #[21,3,2,60,27] else #[8,4,28,2,30])) else (if i.val < 14 then (if i.val < 13 then #[9,5,27,30,2] else #[28,26,8,3,33]) else (if i.val < 15 then #[34,27,5,33,3] else #[4,8,26,6,37])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[26,28,4,7,39] else #[23,29,40,4,42]) else (if i.val < 19 then #[24,30,39,42,4] else #[5,9,34,37,6])) else (if i.val < 22 then (if i.val < 21 then #[25,31,44,5,41] else #[10,7,6,62,34]) else (if i.val < 23 then #[27,34,9,39,7] else #[17,36,46,8,48]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,37,33,48,8] else #[20,43,49,9,47]) else (if i.val < 27 then #[16,13,15,10,50] else #[22,14,12,50,10])) else (if i.val < 30 then (if i.val < 29 then #[13,16,11,21,51] else #[36,17,32,11,53]) else (if i.val < 31 then #[37,18,51,53,11] else #[43,20,45,12,52]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[38,40,29,13,55] else #[39,50,24,55,13]) else (if i.val < 35 then #[14,22,19,51,21] else #[45,49,43,14,54])) else (if i.val < 38 then (if i.val < 37 then #[29,23,38,15,57] else #[30,24,50,57,15]) else (if i.val < 39 then #[32,46,36,16,59] else #[33,51,18,59,16]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[46,32,17,26,61] else #[56,52,62,17,20]) else (if i.val < 43 then #[57,53,61,20,17] else #[31,25,35,19,56])) else (if i.val < 46 then (if i.val < 45 then #[49,45,20,34,62] else #[35,44,31,22,58]) else (if i.val < 47 then #[40,38,23,28,63] else #[52,56,60,23,25])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[53,57,63,25,23] else #[44,35,25,27,60]) else (if i.val < 51 then #[51,33,37,61,26] else #[50,39,30,63,28])) else (if i.val < 54 then (if i.val < 53 then #[47,41,58,29,31] else #[48,42,55,31,29]) else (if i.val < 55 then #[62,60,56,32,35] else #[63,61,53,35,32]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[41,47,54,36,43] else #[42,48,59,43,36]) else (if i.val < 59 then #[60,62,52,38,45] else #[61,63,57,45,38])) else (if i.val < 62 then (if i.val < 61 then #[58,54,47,40,49] else #[59,55,42,49,40]) else (if i.val < 63 then #[54,58,41,46,44] else #[55,59,48,44,46])))))) : Array (Fin 64))[j.val]!
private def quotientParents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 2 else 2)) else (if i.val < 14 then (if i.val < 13 then 2 else 3) else (if i.val < 15 then 3 else 4)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 4) else (if i.val < 19 then 4 else 5)) else (if i.val < 22 then (if i.val < 21 then 5 else 6) else (if i.val < 23 then 7 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 8 else 9) else (if i.val < 27 then 10 else 10)) else (if i.val < 30 then (if i.val < 29 then 11 else 11) else (if i.val < 31 then 11 else 12))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 13 else 13) else (if i.val < 35 then 14 else 14)) else (if i.val < 38 then (if i.val < 37 then 15 else 15) else (if i.val < 39 then 16 else 16))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 17 else 17) else (if i.val < 43 then 17 else 19)) else (if i.val < 46 then (if i.val < 45 then 20 else 22) else (if i.val < 47 then 23 else 23)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 23 else 25) else (if i.val < 51 then 26 else 28)) else (if i.val < 54 then (if i.val < 53 then 29 else 29) else (if i.val < 55 then 32 else 32))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 36 else 36) else (if i.val < 59 then 38 else 38)) else (if i.val < 62 then (if i.val < 61 then 40 else 40) else (if i.val < 63 then 41 else 44)))))) : Fin 64)
private def quotientLetters (i : Fin 64) : Fin 5 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 3 else 4) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 2 else 3)) else (if i.val < 14 then (if i.val < 13 then 4 else 3) else (if i.val < 15 then 4 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 3) else (if i.val < 19 then 4 else 0)) else (if i.val < 22 then (if i.val < 21 then 3 else 2) else (if i.val < 23 then 4 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 3) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 2 else 3) else (if i.val < 31 then 4 else 3))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 3 else 4) else (if i.val < 35 then 0 else 3)) else (if i.val < 38 then (if i.val < 37 then 3 else 4) else (if i.val < 39 then 3 else 4))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 2 else 3) else (if i.val < 43 then 4 else 3)) else (if i.val < 46 then (if i.val < 45 then 2 else 3) else (if i.val < 47 then 2 else 3)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 4 else 2) else (if i.val < 51 then 4 else 4)) else (if i.val < 54 then (if i.val < 53 then 3 else 4) else (if i.val < 55 then 3 else 4))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 3 else 4) else (if i.val < 59 then 3 else 4)) else (if i.val < 62 then (if i.val < 61 then 3 else 4) else (if i.val < 63 then 2 else 3)))))) : Fin 5)
private def stepWitness (i : Fin 64) (j : Fin 5) : Fin 1 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 3 then #[0,0,0,0,0] else #[0,0,0,0,0])) else (if i.val < 6 then (if i.val < 5 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 7 then #[0,0,0,0,0] else #[0,0,0,0,0]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 11 then #[0,0,0,0,0] else #[0,0,0,0,0])) else (if i.val < 14 then (if i.val < 13 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 15 then #[0,0,0,0,0] else #[0,0,0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 19 then #[0,0,0,0,0] else #[0,0,0,0,0])) else (if i.val < 22 then (if i.val < 21 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 23 then #[0,0,0,0,0] else #[0,0,0,0,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 27 then #[0,0,0,0,0] else #[0,0,0,0,0])) else (if i.val < 30 then (if i.val < 29 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 31 then #[0,0,0,0,0] else #[0,0,0,0,0]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 35 then #[0,0,0,0,0] else #[0,0,0,0,0])) else (if i.val < 38 then (if i.val < 37 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 39 then #[0,0,0,0,0] else #[0,0,0,0,0]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 43 then #[0,0,0,0,0] else #[0,0,0,0,0])) else (if i.val < 46 then (if i.val < 45 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 47 then #[0,0,0,0,0] else #[0,0,0,0,0])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 51 then #[0,0,0,0,0] else #[0,0,0,0,0])) else (if i.val < 54 then (if i.val < 53 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 55 then #[0,0,0,0,0] else #[0,0,0,0,0]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 59 then #[0,0,0,0,0] else #[0,0,0,0,0])) else (if i.val < 62 then (if i.val < 61 then #[0,0,0,0,0] else #[0,0,0,0,0]) else (if i.val < 63 then #[0,0,0,0,0] else #[0,0,0,0,0])))))) : Array (Fin 1))[j.val]!
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
def normalGenerators (j : Fin 1) : Source := ⟨(10 : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 2) : Fin 64 := ((if i.val < 1 then 10 else 63) : Fin 64)
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

private def posWitness (i : Fin 5) (j : Fin 1) : Fin 2 := ((if i.val < 2 then (if i.val < 1 then #[0] else #[0]) else (if i.val < 3 then #[0] else (if i.val < 4 then #[0] else #[0]))) : Array (Fin 2))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 1) : Fin 2 := ((if i.val < 2 then (if i.val < 1 then #[0] else #[0]) else (if i.val < 3 then #[0] else (if i.val < 4 then #[0] else #[0]))) : Array (Fin 2))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 32) : Source := ⟨((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 5) else (if i.val < 3 then 28 else 57)) else (if i.val < 6 then (if i.val < 5 then 59 else 35) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 24) else (if i.val < 11 then 32 else 58)) else (if i.val < 14 then (if i.val < 13 then 61 else 56) else (if i.val < 15 then 39 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 7 else 2) else (if i.val < 19 then 25 else 27)) else (if i.val < 22 then (if i.val < 21 then 30 else 38) else (if i.val < 23 then 36 else 60))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 62 else 52) else (if i.val < 27 then 6 else 4)) else (if i.val < 30 then (if i.val < 29 then 26 else 29) else (if i.val < 31 then 37 else 34))))) : Fin 64)⟩
private def quotientNext (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,4] else #[0,1,5,6,7]) else (if i.val < 3 then #[5,2,0,8,9] else #[6,3,10,11,12])) else (if i.val < 6 then (if i.val < 5 then #[7,4,9,13,0] else #[2,5,1,10,14]) else (if i.val < 7 then #[3,6,8,15,16] else #[4,7,14,17,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,8,6,18,19] else #[14,9,4,20,2]) else (if i.val < 11 then #[8,10,3,21,22] else #[15,11,18,23,24])) else (if i.val < 14 then (if i.val < 13 then #[16,12,22,4,3] else #[17,13,25,24,23]) else (if i.val < 15 then #[9,14,7,25,5] else #[11,15,21,26,27])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[12,16,19,7,6] else #[13,17,20,27,26]) else (if i.val < 19 then #[21,18,11,28,29] else #[22,19,16,9,8])) else (if i.val < 22 then (if i.val < 21 then #[25,20,17,29,28] else #[18,21,15,30,31]) else (if i.val < 23 then #[19,22,12,14,10] else #[26,23,30,0,13]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,24,29,12,11] else #[20,25,13,31,30]) else (if i.val < 27 then #[23,26,28,1,17] else #[24,27,31,16,15])) else (if i.val < 30 then (if i.val < 29 then #[30,28,26,2,20] else #[31,29,24,19,18]) else (if i.val < 31 then #[28,30,23,5,25] else #[29,31,27,22,21]))))) : Array (Fin 32))[j.val]!
private def quotientPrev (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,23,4] else #[0,1,5,26,7]) else (if i.val < 3 then #[5,2,0,28,9] else #[6,3,10,0,12])) else (if i.val < 6 then (if i.val < 5 then #[7,4,9,12,0] else #[2,5,1,30,14]) else (if i.val < 7 then #[3,6,8,1,16] else #[4,7,14,16,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,8,6,2,19] else #[14,9,4,19,2]) else (if i.val < 11 then #[8,10,3,5,22] else #[15,11,18,3,24])) else (if i.val < 14 then (if i.val < 13 then #[16,12,22,24,3] else #[17,13,25,4,23]) else (if i.val < 15 then #[9,14,7,22,5] else #[11,15,21,6,27])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[12,16,19,27,6] else #[13,17,20,7,26]) else (if i.val < 19 then #[21,18,11,8,29] else #[22,19,16,29,8])) else (if i.val < 22 then (if i.val < 21 then #[25,20,17,9,28] else #[18,21,15,10,31]) else (if i.val < 23 then #[19,22,12,31,10] else #[26,23,30,11,13]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,24,29,13,11] else #[20,25,13,14,30]) else (if i.val < 27 then #[23,26,28,15,17] else #[24,27,31,17,15])) else (if i.val < 30 then (if i.val < 29 then #[30,28,26,18,20] else #[31,29,24,20,18]) else (if i.val < 31 then #[28,30,23,21,25] else #[29,31,27,25,21]))))) : Array (Fin 32))[j.val]!
private def quotientParents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 3 else 4) else (if i.val < 15 then 5 else 6)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 7) else (if i.val < 19 then 8 else 8)) else (if i.val < 22 then (if i.val < 21 then 9 else 10) else (if i.val < 23 then 10 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 11 else 13) else (if i.val < 27 then 15 else 15)) else (if i.val < 30 then (if i.val < 29 then 18 else 18) else (if i.val < 31 then 21 else 21))))) : Fin 32)
private def quotientLetters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 2) else (if i.val < 7 then 3 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 2 else 3)) else (if i.val < 14 then (if i.val < 13 then 4 else 3) else (if i.val < 15 then 4 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 3) else (if i.val < 19 then 3 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 3) else (if i.val < 23 then 4 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 2) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 3 else 4) else (if i.val < 31 then 3 else 4))))) : Fin 5)
private def stepWitness (i : Fin 32) (j : Fin 5) : Fin 2 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,1,1,1] else #[1,0,1,1,1]) else (if i.val < 3 then #[1,0,1,1,1] else #[0,0,1,1,1])) else (if i.val < 6 then (if i.val < 5 then #[0,0,1,1,1] else #[1,0,1,1,1]) else (if i.val < 7 then #[0,0,1,1,1] else #[0,0,1,1,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,0,1,1,1] else #[0,0,1,1,1]) else (if i.val < 11 then #[0,0,1,1,1] else #[1,0,0,1,1])) else (if i.val < 14 then (if i.val < 13 then #[1,0,1,1,1] else #[1,0,1,1,1]) else (if i.val < 15 then #[0,0,1,0,1] else #[1,0,0,1,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[1,0,1,1,1] else #[1,0,0,1,1]) else (if i.val < 19 then #[1,0,0,1,1] else #[1,0,1,1,1])) else (if i.val < 22 then (if i.val < 21 then #[0,0,0,1,1] else #[1,0,0,1,1]) else (if i.val < 23 then #[1,0,1,1,1] else #[0,0,0,1,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[0,0,0,1,1] else #[0,0,1,0,0]) else (if i.val < 27 then #[0,0,0,1,1] else #[0,0,0,1,1])) else (if i.val < 30 then (if i.val < 29 then #[0,0,0,1,1] else #[0,0,0,1,1]) else (if i.val < 31 then #[0,0,0,1,0] else #[0,0,0,1,1]))))) : Array (Fin 2))[j.val]!
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
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 10 else 0) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 0 else 10) else (if i.val < 3 then 21 else 63)) : Fin 64)
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

private def posWitness (i : Fin 5) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0] else #[1,0]) else (if i.val < 3 then #[1,2] else (if i.val < 4 then #[1,2] else #[1,2]))) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0] else #[1,0]) else (if i.val < 3 then #[1,2] else (if i.val < 4 then #[1,2] else #[1,2]))) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 5) else (if i.val < 3 then 28 else 57)) else (if i.val < 6 then (if i.val < 5 then 59 else 35) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 24) else (if i.val < 11 then 32 else 61)) else (if i.val < 14 then (if i.val < 13 then 56 else 39) else (if i.val < 15 then 27 else 30)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 5) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,4] else #[0,1,5,6,7]) else (if i.val < 3 then #[5,2,0,8,9] else #[6,3,10,1,11])) else (if i.val < 6 then (if i.val < 5 then #[7,4,9,12,0] else #[2,5,1,10,13]) else (if i.val < 7 then #[3,6,8,0,12] else #[4,7,13,11,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,8,6,5,14] else #[13,9,4,15,2]) else (if i.val < 11 then #[8,10,3,2,15] else #[12,11,15,4,3])) else (if i.val < 14 then (if i.val < 13 then #[11,12,14,7,6] else #[9,13,7,14,5]) else (if i.val < 15 then #[15,14,12,9,8] else #[14,15,11,13,10])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 5) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,6,4] else #[0,1,5,3,7]) else (if i.val < 3 then #[5,2,0,10,9] else #[6,3,10,0,11])) else (if i.val < 6 then (if i.val < 5 then #[7,4,9,11,0] else #[2,5,1,8,13]) else (if i.val < 7 then #[3,6,8,1,12] else #[4,7,13,12,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,8,6,2,14] else #[13,9,4,14,2]) else (if i.val < 11 then #[8,10,3,5,15] else #[12,11,15,7,3])) else (if i.val < 14 then (if i.val < 13 then #[11,12,14,4,6] else #[9,13,7,15,5]) else (if i.val < 15 then #[15,14,12,13,8] else #[14,15,11,9,10])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 4 else 5) else (if i.val < 15 then 8 else 9)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 5 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 2) else (if i.val < 7 then 3 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 2 else 4)) else (if i.val < 14 then (if i.val < 13 then 3 else 4) else (if i.val < 15 then 4 else 3)))) : Fin 5)
private def stepWitness (i : Fin 16) (j : Fin 5) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,1,3,3,3] else #[3,1,3,3,3]) else (if i.val < 3 then #[3,1,3,3,3] else #[1,1,3,0,3])) else (if i.val < 6 then (if i.val < 5 then #[1,1,3,3,3] else #[3,1,3,3,3]) else (if i.val < 7 then #[1,1,3,0,0] else #[1,1,3,0,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[1,1,3,2,3] else #[1,1,3,3,3]) else (if i.val < 11 then #[1,1,3,2,2] else #[0,1,2,3,3])) else (if i.val < 14 then (if i.val < 13 then #[0,1,0,0,0] else #[1,1,3,2,3]) else (if i.val < 15 then #[2,1,0,3,3] else #[2,1,2,2,2])))) : Array (Fin 4))[j.val]!
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
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 10 else 5) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 5 else 10) else (if i.val < 3 then 16 else 63)) : Fin 64)
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

private def posWitness (i : Fin 5) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0] else #[1,0]) else (if i.val < 3 then #[1,0] else (if i.val < 4 then #[1,2] else #[1,2]))) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0] else #[1,0]) else (if i.val < 3 then #[1,0] else (if i.val < 4 then #[1,2] else #[1,2]))) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 57 else 59)) else (if i.val < 6 then (if i.val < 5 then 31 else 24) else (if i.val < 7 then 58 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 56 else 25) else (if i.val < 11 then 27 else 30)) else (if i.val < 14 then (if i.val < 13 then 60 else 62) else (if i.val < 15 then 26 else 29)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 5) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,1,2,3] else #[1,1,0,4,5]) else (if i.val < 3 then #[2,2,4,6,7] else #[3,3,5,8,0])) else (if i.val < 6 then (if i.val < 5 then #[4,4,2,9,10] else #[5,5,3,11,1]) else (if i.val < 7 then #[6,6,9,12,13] else #[7,7,10,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[8,8,11,13,12] else #[9,9,6,14,15]) else (if i.val < 11 then #[10,10,7,5,4] else #[11,11,8,15,14])) else (if i.val < 14 then (if i.val < 13 then #[12,12,14,0,8] else #[13,13,15,7,6]) else (if i.val < 15 then #[14,14,12,1,11] else #[15,15,13,10,9])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 5) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,1,12,3] else #[1,1,0,14,5]) else (if i.val < 3 then #[2,2,4,0,7] else #[3,3,5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[4,4,2,1,10] else #[5,5,3,10,1]) else (if i.val < 7 then #[6,6,9,2,13] else #[7,7,10,13,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[8,8,11,3,12] else #[9,9,6,4,15]) else (if i.val < 11 then #[10,10,7,15,4] else #[11,11,8,5,14])) else (if i.val < 14 then (if i.val < 13 then #[12,12,14,6,8] else #[13,13,15,8,6]) else (if i.val < 15 then #[14,14,12,9,11] else #[15,15,13,11,9])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 6) else (if i.val < 15 then 9 else 9)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 5 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 3 else 4)) else (if i.val < 6 then (if i.val < 5 then 3 else 4) else (if i.val < 7 then 3 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 4 else 3)) else (if i.val < 14 then (if i.val < 13 then 3 else 4) else (if i.val < 15 then 3 else 4)))) : Fin 5)
private def stepWitness (i : Fin 16) (j : Fin 5) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1,3,3,3] else #[0,1,3,3,3]) else (if i.val < 3 then #[2,1,0,3,3] else #[2,1,3,3,3])) else (if i.val < 6 then (if i.val < 5 then #[2,1,0,3,3] else #[2,1,3,3,3]) else (if i.val < 7 then #[0,1,1,3,3] else #[0,1,0,3,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,1,2,3,3] else #[0,1,1,3,3]) else (if i.val < 11 then #[0,1,0,3,3] else #[0,1,2,3,3])) else (if i.val < 14 then (if i.val < 13 then #[2,1,2,3,3] else #[2,1,1,3,3]) else (if i.val < 15 then #[2,1,2,3,3] else #[2,1,1,3,3])))) : Array (Fin 4))[j.val]!
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
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 10 else 15) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then 10 else 15) else (if i.val < 3 then 58 else 63)) : Fin 64)
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

private def posWitness (i : Fin 5) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1] else #[0,1]) else (if i.val < 3 then #[0,2] else (if i.val < 4 then #[0,1] else #[0,1]))) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 2) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1] else #[0,1]) else (if i.val < 3 then #[0,2] else (if i.val < 4 then #[0,1] else #[0,1]))) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 5) else (if i.val < 3 then 28 else 57)) else (if i.val < 6 then (if i.val < 5 then 59 else 35) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 24) else (if i.val < 11 then 32 else 61)) else (if i.val < 14 then (if i.val < 13 then 39 else 7) else (if i.val < 15 then 27 else 36)))) : Fin 64)⟩
private def quotientNext (i : Fin 16) (j : Fin 5) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,4] else #[0,1,5,6,7]) else (if i.val < 3 then #[5,2,0,8,9] else #[6,3,10,0,11])) else (if i.val < 6 then (if i.val < 5 then #[7,4,9,11,0] else #[2,5,1,10,12]) else (if i.val < 7 then #[3,6,8,1,13] else #[4,7,12,13,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,8,6,2,14] else #[12,9,4,14,2]) else (if i.val < 11 then #[8,10,3,5,15] else #[13,11,15,4,3])) else (if i.val < 14 then (if i.val < 13 then #[9,12,7,15,5] else #[11,13,14,7,6]) else (if i.val < 15 then #[15,14,13,9,8] else #[14,15,11,12,10])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 5) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,4] else #[0,1,5,6,7]) else (if i.val < 3 then #[5,2,0,8,9] else #[6,3,10,0,11])) else (if i.val < 6 then (if i.val < 5 then #[7,4,9,11,0] else #[2,5,1,10,12]) else (if i.val < 7 then #[3,6,8,1,13] else #[4,7,12,13,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,8,6,2,14] else #[12,9,4,14,2]) else (if i.val < 11 then #[8,10,3,5,15] else #[13,11,15,4,3])) else (if i.val < 14 then (if i.val < 13 then #[9,12,7,15,5] else #[11,13,14,7,6]) else (if i.val < 15 then #[15,14,13,9,8] else #[14,15,11,12,10])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 5 else 6) else (if i.val < 15 then 8 else 10)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 5 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 2) else (if i.val < 7 then 3 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 2 else 4)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 4 else 4)))) : Fin 5)
private def stepWitness (i : Fin 16) (j : Fin 5) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,0,3,3,3] else #[3,0,3,3,3]) else (if i.val < 3 then #[3,0,3,3,3] else #[0,0,3,2,3])) else (if i.val < 6 then (if i.val < 5 then #[0,0,3,2,3] else #[3,0,3,3,3]) else (if i.val < 7 then #[0,0,3,2,3] else #[0,0,3,2,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,0,3,1,3] else #[0,0,3,1,3]) else (if i.val < 11 then #[0,0,3,1,3] else #[3,0,3,3,3])) else (if i.val < 14 then (if i.val < 13 then #[0,0,3,1,3] else #[3,0,3,3,3]) else (if i.val < 15 then #[3,0,3,3,3] else #[3,0,3,3,3])))) : Array (Fin 4))[j.val]!
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
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 0 else 5)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 5) else (if i.val < 3 then 10 else 15)) else (if i.val < 6 then (if i.val < 5 then 16 else 21) else (if i.val < 7 then 58 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,7,6] else #[4,6,7]) else (if i.val < 3 then #[7,5,4] else #[6,4,5])) else (if i.val < 6 then (if i.val < 5 then #[1,3,2] else #[0,2,3]) else (if i.val < 7 then #[3,1,0] else #[2,0,1]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 1 else 7)) else (if i.val < 6 then (if i.val < 5 then 5 else 4) else (if i.val < 7 then 6 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 7 else 5)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 0 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 0 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1] else #[2,0,1]) else (if i.val < 3 then #[2,5,1] else (if i.val < 4 then #[2,5,4] else #[2,5,4]))) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1] else #[2,0,1]) else (if i.val < 3 then #[2,5,1] else (if i.val < 4 then #[2,5,4] else #[2,5,4]))) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 57 else 59)) else (if i.val < 6 then (if i.val < 5 then 31 else 24) else (if i.val < 7 then 61 else 27))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,1,2,3] else #[1,1,0,4,5]) else (if i.val < 3 then #[2,2,4,0,6] else #[3,3,5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[4,4,2,1,7] else #[5,5,3,7,1]) else (if i.val < 7 then #[6,6,7,3,2] else #[7,7,6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,1,2,3] else #[1,1,0,4,5]) else (if i.val < 3 then #[2,2,4,0,6] else #[3,3,5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[4,4,2,1,7] else #[5,5,3,7,1]) else (if i.val < 7 then #[6,6,7,3,2] else #[7,7,6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 4))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 5 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 3 else 4)) else (if i.val < 6 then (if i.val < 5 then 3 else 4) else (if i.val < 7 then 4 else 4))) : Fin 5)
private def stepWitness (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,7,7,7] else #[1,2,7,7,7]) else (if i.val < 3 then #[4,2,1,6,7] else #[4,2,7,6,7])) else (if i.val < 6 then (if i.val < 5 then #[4,2,1,3,7] else #[4,2,7,3,7]) else (if i.val < 7 then #[1,2,1,7,7] else #[1,2,1,7,7]))) : Array (Fin 8))[j.val]!
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
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 0 else 24)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 10) else (if i.val < 3 then 21 else 24)) else (if i.val < 6 then (if i.val < 5 then 34 else 45) else (if i.val < 7 then 55 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[2,7,6] else #[7,2,5]) else (if i.val < 3 then #[0,1,4] else #[5,6,7])) else (if i.val < 6 then (if i.val < 5 then #[6,5,2] else #[3,4,1]) else (if i.val < 7 then #[4,3,0] else #[1,0,3]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 7 else 5) else (if i.val < 7 then 6 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 1 else 7)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 0 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[1,0,5] else #[1,0,3]) else (if i.val < 3 then #[1,2,3] else (if i.val < 4 then #[1,2,4] else #[1,2,3]))) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[1,0,5] else #[1,0,3]) else (if i.val < 3 then #[1,2,3] else (if i.val < 4 then #[1,2,6] else #[1,2,3]))) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 5) else (if i.val < 3 then 28 else 57)) else (if i.val < 6 then (if i.val < 5 then 35 else 3) else (if i.val < 7 then 31 else 32))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,2] else #[0,1,4,5,4]) else (if i.val < 3 then #[4,2,0,6,0] else #[5,3,7,1,7])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1,7,1] else #[3,5,6,0,6]) else (if i.val < 7 then #[7,6,5,4,5] else #[6,7,3,2,3]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,5,2] else #[0,1,4,3,4]) else (if i.val < 3 then #[4,2,0,7,0] else #[5,3,7,0,7])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1,6,1] else #[3,5,6,1,6]) else (if i.val < 7 then #[7,6,5,2,5] else #[6,7,3,4,3]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 5 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 3 else 2))) : Fin 5)
private def stepWitness (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,1,7,7,3] else #[7,1,7,7,5]) else (if i.val < 3 then #[7,1,7,7,3] else #[1,1,7,0,4])) else (if i.val < 6 then (if i.val < 5 then #[7,1,7,7,5] else #[1,1,7,0,6]) else (if i.val < 7 then #[1,1,7,2,6] else #[1,1,7,2,4]))) : Array (Fin 8))[j.val]!
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
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 0 else 29)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 10) else (if i.val < 3 then 21 else 29)) else (if i.val < 6 then (if i.val < 5 then 39 else 40) else (if i.val < 7 then 50 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[2,7,6] else #[7,2,5]) else (if i.val < 3 then #[0,1,4] else #[5,6,1])) else (if i.val < 6 then (if i.val < 5 then #[6,5,0] else #[3,4,7]) else (if i.val < 7 then #[4,3,2] else #[1,0,3]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 7 else 5) else (if i.val < 7 then 6 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 1 else 7)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 0 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[1,0,5] else #[1,0,3]) else (if i.val < 3 then #[1,2,5] else (if i.val < 4 then #[1,2,4] else #[1,2,3]))) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[1,0,5] else #[1,0,3]) else (if i.val < 3 then #[1,2,5] else (if i.val < 4 then #[1,2,6] else #[1,2,3]))) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 5) else (if i.val < 3 then 28 else 57)) else (if i.val < 6 then (if i.val < 5 then 59 else 3) else (if i.val < 7 then 31 else 32))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,4] else #[0,1,4,5,2]) else (if i.val < 3 then #[4,2,0,6,1] else #[5,3,7,1,6])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1,7,0] else #[3,5,6,0,7]) else (if i.val < 7 then #[7,6,5,4,3] else #[6,7,3,2,5]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,5,4] else #[0,1,4,3,2]) else (if i.val < 3 then #[4,2,0,7,1] else #[5,3,7,0,6])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1,6,0] else #[3,5,6,1,7]) else (if i.val < 7 then #[7,6,5,2,3] else #[6,7,3,4,5]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 5 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 3 else 2))) : Fin 5)
private def stepWitness (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,1,7,7,7] else #[7,1,6,7,6]) else (if i.val < 3 then #[6,1,7,7,4] else #[1,1,7,0,3])) else (if i.val < 6 then (if i.val < 5 then #[4,1,4,4,7] else #[1,1,7,0,5]) else (if i.val < 7 then #[1,1,7,5,5] else #[1,1,7,2,3]))) : Array (Fin 8))[j.val]!
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
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 5 else 25)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 10) else (if i.val < 3 then 16 else 25)) else (if i.val < 6 then (if i.val < 5 then 38 else 44) else (if i.val < 7 then 51 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[2,7,4] else #[7,2,5]) else (if i.val < 3 then #[0,1,6] else #[5,4,1])) else (if i.val < 6 then (if i.val < 5 then #[6,3,2] else #[3,6,7]) else (if i.val < 7 then #[4,5,0] else #[1,0,3]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 7 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 1 else 7)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[1,0,3] else #[1,0,3]) else (if i.val < 3 then #[1,0,5] else (if i.val < 4 then #[1,2,4] else #[1,2,3]))) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[1,0,3] else #[1,0,3]) else (if i.val < 3 then #[1,0,5] else (if i.val < 4 then #[1,2,6] else #[1,2,3]))) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 57 else 59)) else (if i.val < 6 then (if i.val < 5 then 31 else 24) else (if i.val < 7 then 61 else 56))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,1,2,3] else #[1,1,0,4,5]) else (if i.val < 3 then #[2,2,4,1,6] else #[3,3,5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[4,4,2,0,7] else #[5,5,3,6,1]) else (if i.val < 7 then #[6,6,7,3,2] else #[7,7,6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,1,4,3] else #[1,1,0,2,5]) else (if i.val < 3 then #[2,2,4,0,6] else #[3,3,5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[4,4,2,1,7] else #[5,5,3,7,1]) else (if i.val < 7 then #[6,6,7,5,2] else #[7,7,6,3,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 5 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 3 else 4)) else (if i.val < 6 then (if i.val < 5 then 3 else 4) else (if i.val < 7 then 4 else 3))) : Fin 5)
private def stepWitness (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1,7,7,7] else #[0,1,7,7,7]) else (if i.val < 3 then #[2,1,0,3,7] else #[2,1,7,7,7])) else (if i.val < 6 then (if i.val < 5 then #[2,1,0,5,5] else #[2,1,7,5,7]) else (if i.val < 7 then #[0,1,6,7,7] else #[0,1,4,3,3]))) : Array (Fin 8))[j.val]!
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
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 5 else 28)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 10) else (if i.val < 3 then 16 else 28)) else (if i.val < 6 then (if i.val < 5 then 35 else 41) else (if i.val < 7 then 54 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[2,7,4] else #[7,2,5]) else (if i.val < 3 then #[0,1,6] else #[5,4,7])) else (if i.val < 6 then (if i.val < 5 then #[6,3,0] else #[3,6,1]) else (if i.val < 7 then #[4,5,2] else #[1,0,3]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 7 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 1 else 7)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[1,0,3] else #[1,0,3]) else (if i.val < 3 then #[1,0,3] else (if i.val < 4 then #[1,2,4] else #[1,2,3]))) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[1,0,3] else #[1,0,3]) else (if i.val < 3 then #[1,0,3] else (if i.val < 4 then #[1,2,6] else #[1,2,3]))) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 57) else (if i.val < 3 then 59 else 58)) else (if i.val < 6 then (if i.val < 5 then 61 else 56) else (if i.val < 7 then 60 else 62))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,0,1,2] else #[1,1,1,3,4]) else (if i.val < 3 then #[2,2,2,5,0] else #[3,3,3,6,7])) else (if i.val < 6 then (if i.val < 5 then #[4,4,4,2,1] else #[5,5,5,7,6]) else (if i.val < 7 then #[6,6,6,0,5] else #[7,7,7,4,3]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,0,6,2] else #[1,1,1,0,4]) else (if i.val < 3 then #[2,2,2,4,0] else #[3,3,3,1,7])) else (if i.val < 6 then (if i.val < 5 then #[4,4,4,7,1] else #[5,5,5,2,6]) else (if i.val < 7 then #[6,6,6,3,5] else #[7,7,7,5,3]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 3 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 5 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 3 else 4))) : Fin 5)
private def stepWitness (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1,3,7,7] else #[2,1,4,7,7]) else (if i.val < 3 then #[2,1,3,7,7] else #[0,1,5,7,7])) else (if i.val < 6 then (if i.val < 5 then #[0,1,4,7,7] else #[0,1,6,7,7]) else (if i.val < 7 then #[2,1,6,7,7] else #[2,1,5,7,7]))) : Array (Fin 8))[j.val]!
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
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 15 else 1)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 4) else (if i.val < 3 then 10 else 15)) else (if i.val < 6 then (if i.val < 5 then 17 else 20) else (if i.val < 7 then 58 else 63))) : Fin 64)
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

private def posWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[2,3,5] else #[2,3,0]) else (if i.val < 3 then #[2,6,0] else (if i.val < 4 then #[2,3,4] else #[2,3,5]))) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[2,3,5] else #[2,3,0]) else (if i.val < 3 then #[2,6,0] else (if i.val < 4 then #[2,3,4] else #[2,3,5]))) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 5) else (if i.val < 3 then 28 else 57)) else (if i.val < 6 then (if i.val < 5 then 35 else 3) else (if i.val < 7 then 31 else 32))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,1] else #[0,1,4,5,0]) else (if i.val < 3 then #[4,2,0,6,4] else #[5,3,7,0,5])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1,7,2] else #[3,5,6,1,3]) else (if i.val < 7 then #[7,6,5,2,7] else #[6,7,3,4,6]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,1] else #[0,1,4,5,0]) else (if i.val < 3 then #[4,2,0,6,4] else #[5,3,7,0,5])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1,7,2] else #[3,5,6,1,3]) else (if i.val < 7 then #[7,6,5,2,7] else #[6,7,3,4,6]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 5 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 3 else 2))) : Fin 5)
private def stepWitness (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,2,7,7,0] else #[7,2,7,7,5]) else (if i.val < 3 then #[7,2,7,7,0] else #[2,2,7,6,1])) else (if i.val < 6 then (if i.val < 5 then #[7,2,7,7,5] else #[2,2,7,6,4]) else (if i.val < 7 then #[2,2,7,3,4] else #[2,2,7,3,1]))) : Array (Fin 8))[j.val]!
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
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 10 else (if j.val < 2 then 15 else 11)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 64 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 11) else (if i.val < 3 then 14 else 15)) else (if i.val < 6 then (if i.val < 5 then 58 else 59) else (if i.val < 7 then 62 else 63))) : Fin 64)
private def next (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,4,6] else #[6,5,7]) else (if i.val < 3 then #[5,6,4] else #[4,7,5])) else (if i.val < 6 then (if i.val < 5 then #[3,0,2] else #[2,1,3]) else (if i.val < 7 then #[1,2,0] else #[0,3,1]))) : Array (Fin 8))[j.val]!
private def rank (i : Fin 8) : ℕ := (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 7 else 2)) else (if i.val < 6 then (if i.val < 5 then 4 else 6) else (if i.val < 7 then 5 else 0)))
private def parents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 7) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 0 else 3) else (if i.val < 7 then 0 else 7))) : Fin 8)
private def letters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 2 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)

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

private def posWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[0,3,6] else #[0,3,1]) else (if i.val < 3 then #[0,4,6] else (if i.val < 4 then #[0,3,2] else #[0,3,1]))) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 3) : Fin 8 := ((if i.val < 2 then (if i.val < 1 then #[0,3,6] else #[0,3,1]) else (if i.val < 3 then #[0,4,6] else (if i.val < 4 then #[0,3,2] else #[0,3,1]))) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 5) else (if i.val < 3 then 28 else 57)) else (if i.val < 6 then (if i.val < 5 then 35 else 3) else (if i.val < 7 then 31 else 32))) : Fin 64)⟩
private def quotientNext (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,0] else #[0,1,4,5,1]) else (if i.val < 3 then #[4,2,0,6,2] else #[5,3,7,0,3])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1,7,4] else #[3,5,6,1,5]) else (if i.val < 7 then #[7,6,5,2,6] else #[6,7,3,4,7]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2,3,0] else #[0,1,4,5,1]) else (if i.val < 3 then #[4,2,0,6,2] else #[5,3,7,0,3])) else (if i.val < 6 then (if i.val < 5 then #[2,4,1,7,4] else #[3,5,6,1,5]) else (if i.val < 7 then #[7,6,5,2,6] else #[6,7,3,4,7]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 5 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 3 else 2))) : Fin 5)
private def stepWitness (i : Fin 8) (j : Fin 5) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,0,7,7,5] else #[7,0,7,7,2]) else (if i.val < 3 then #[7,0,7,7,5] else #[0,0,7,4,6])) else (if i.val < 6 then (if i.val < 5 then #[7,0,7,7,2] else #[0,0,7,4,1]) else (if i.val < 7 then #[0,0,7,3,1] else #[0,0,7,3,6]))) : Array (Fin 8))[j.val]!
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
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else 1)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 4 else 5)) else (if i.val < 6 then (if i.val < 5 then 10 else 11) else (if i.val < 7 then 14 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 17) else (if i.val < 11 then 20 else 21)) else (if i.val < 14 then (if i.val < 13 then 58 else 59) else (if i.val < 15 then 62 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,15,12,14] else #[10,5,6,4]) else (if i.val < 3 then #[9,6,5,7] else #[8,12,15,13])) else (if i.val < 6 then (if i.val < 5 then #[15,11,8,10] else #[14,1,2,0]) else (if i.val < 7 then #[13,2,1,3] else #[12,8,11,9]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,7,4,6] else #[2,13,14,12]) else (if i.val < 11 then #[1,14,13,15] else #[0,4,7,5])) else (if i.val < 14 then (if i.val < 13 then #[7,3,0,2] else #[6,9,10,8]) else (if i.val < 15 then #[5,10,9,11] else #[4,0,3,1])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 14 else 3)) else (if i.val < 6 then (if i.val < 5 then 1 else 11) else (if i.val < 7 then 12 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 15) else (if i.val < 11 then 7 else 5)) else (if i.val < 14 then (if i.val < 13 then 8 else 10) else (if i.val < 15 then 9 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 12 else 15)) else (if i.val < 6 then (if i.val < 5 then 15 else 1) else (if i.val < 7 then 1 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 14) else (if i.val < 11 then 4 else 4)) else (if i.val < 14 then (if i.val < 13 then 0 else 3) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 3 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 1)) else (if i.val < 14 then (if i.val < 13 then 2 else 3) else (if i.val < 15 then 3 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[4,0,3,10] else #[4,0,3,1]) else (if i.val < 3 then #[4,11,3,1] else (if i.val < 4 then #[4,11,8,9] else #[4,11,8,10]))) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[4,0,3,10] else #[4,0,3,1]) else (if i.val < 3 then #[4,11,3,1] else (if i.val < 4 then #[4,11,8,9] else #[4,11,8,10]))) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 57 else 31)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,2,0] else #[1,1,0,3,1]) else (if i.val < 3 then #[2,2,3,0,2] else #[3,3,2,1,3])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,2,0] else #[1,1,0,3,1]) else (if i.val < 3 then #[2,2,3,0,2] else #[3,3,2,1,3])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 5 := ((if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 3 else 3)) : Fin 5)
private def stepWitness (i : Fin 4) (j : Fin 5) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[3,4,15,15,13] else #[3,4,15,15,13]) else (if i.val < 3 then #[8,4,3,12,14] else #[8,4,3,7,5])) : Array (Fin 16))[j.val]!
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
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else 2)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 5 else 7)) else (if i.val < 6 then (if i.val < 5 then 8 else 10) else (if i.val < 7 then 13 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 18) else (if i.val < 11 then 21 else 23)) else (if i.val < 14 then (if i.val < 13 then 56 else 58) else (if i.val < 15 then 61 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,15,13,14] else #[11,14,12,15]) else (if i.val < 3 then #[8,13,15,12] else #[9,12,14,13])) else (if i.val < 6 then (if i.val < 5 then #[14,11,9,10] else #[15,10,8,11]) else (if i.val < 7 then #[12,9,11,8] else #[13,8,10,9]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,7,5,6] else #[3,6,4,7]) else (if i.val < 11 then #[0,5,7,4] else #[1,4,6,5])) else (if i.val < 14 then (if i.val < 13 then #[6,3,1,2] else #[7,2,0,3]) else (if i.val < 15 then #[4,1,3,0] else #[5,0,2,1])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 3 else 14)) else (if i.val < 6 then (if i.val < 5 then 12 else 1) else (if i.val < 7 then 13 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 15) else (if i.val < 11 then 5 else 7)) else (if i.val < 14 then (if i.val < 13 then 10 else 8) else (if i.val < 15 then 9 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 15 else 13)) else (if i.val < 6 then (if i.val < 5 then 10 else 15) else (if i.val < 7 then 8 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 7) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 0) else (if i.val < 7 then 3 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 3 else 2) else (if i.val < 15 then 3 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,1] else #[5,0,2,1]) else (if i.val < 3 then #[5,10,2,6] else (if i.val < 4 then #[5,10,8,9] else #[5,10,8,9]))) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,1] else #[5,0,2,1]) else (if i.val < 3 then #[5,10,2,6] else (if i.val < 4 then #[5,10,8,9] else #[5,10,8,9]))) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 57 else 31)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,2,2] else #[1,1,0,3,3]) else (if i.val < 3 then #[2,2,3,0,0] else #[3,3,2,1,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,2,2] else #[1,1,0,3,3]) else (if i.val < 3 then #[2,2,3,0,0] else #[3,3,2,1,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 5 := ((if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 3 else 3)) : Fin 5)
private def stepWitness (i : Fin 4) (j : Fin 5) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,5,15,15,14] else #[2,5,15,15,3]) else (if i.val < 3 then #[8,5,2,13,14] else #[8,5,2,7,3])) : Array (Fin 16))[j.val]!
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
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else 3)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 12 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 60 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,15,13,14] else #[11,4,6,7]) else (if i.val < 3 then #[8,13,15,12] else #[9,6,4,5])) else (if i.val < 6 then (if i.val < 5 then #[14,1,3,2] else #[15,10,8,11]) else (if i.val < 7 then #[12,3,1,0] else #[13,8,10,9]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,7,5,6] else #[3,12,14,15]) else (if i.val < 11 then #[0,5,7,4] else #[1,14,12,13])) else (if i.val < 14 then (if i.val < 13 then #[6,9,11,10] else #[7,2,0,3]) else (if i.val < 15 then #[4,11,9,8] else #[5,0,2,1])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 3 else 14)) else (if i.val < 6 then (if i.val < 5 then 11 else 1) else (if i.val < 7 then 12 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 15) else (if i.val < 11 then 5 else 7)) else (if i.val < 14 then (if i.val < 13 then 10 else 8) else (if i.val < 15 then 9 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 15 else 13)) else (if i.val < 6 then (if i.val < 5 then 1 else 15) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 14) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 3 else 2) else (if i.val < 15 then 3 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,11] else #[5,0,2,1]) else (if i.val < 3 then #[5,10,2,12] else (if i.val < 4 then #[5,10,8,11] else #[5,10,8,9]))) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,11] else #[5,0,2,1]) else (if i.val < 3 then #[5,10,2,12] else (if i.val < 4 then #[5,10,8,11] else #[5,10,8,9]))) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 59 else 24)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,0,2] else #[1,1,0,1,3]) else (if i.val < 3 then #[2,2,3,2,0] else #[3,3,2,3,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,0,2] else #[1,1,0,1,3]) else (if i.val < 3 then #[2,2,3,2,0] else #[3,3,2,3,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 5 := ((if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 4 else 4)) : Fin 5)
private def stepWitness (i : Fin 4) (j : Fin 5) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,5,15,14,15] else #[2,5,15,9,15]) else (if i.val < 3 then #[8,5,15,12,15] else #[8,5,15,1,15])) : Array (Fin 16))[j.val]!
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
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else 24)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 5) else (if i.val < 3 then 10 else 15)) else (if i.val < 6 then (if i.val < 5 then 16 else 21) else (if i.val < 7 then 24 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 34 else 39) else (if i.val < 11 then 40 else 45)) else (if i.val < 14 then (if i.val < 13 then 50 else 55) else (if i.val < 15 then 58 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,15,14,13] else #[4,14,15,9]) else (if i.val < 3 then #[15,5,4,11] else #[14,4,5,7])) else (if i.val < 6 then (if i.val < 5 then #[1,3,2,12] else #[0,2,3,8]) else (if i.val < 7 then #[11,13,12,15] else #[10,12,13,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,11,10,5] else #[12,10,11,1]) else (if i.val < 11 then #[7,9,8,14] else #[6,8,9,2])) else (if i.val < 14 then (if i.val < 13 then #[9,7,6,4] else #[8,6,7,0]) else (if i.val < 15 then #[3,1,0,10] else #[2,0,1,6])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 1 else 12)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 4 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 10) else (if i.val < 11 then 14 else 7)) else (if i.val < 14 then (if i.val < 13 then 11 else 9) else (if i.val < 15 then 8 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 15 else 5)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 15 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 1) else (if i.val < 11 then 14 else 2)) else (if i.val < 14 then (if i.val < 13 then 6 else 0) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 0 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 3 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 2 else 3) else (if i.val < 15 then 2 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1,11] else #[2,0,1,6]) else (if i.val < 3 then #[2,5,1,6] else (if i.val < 4 then #[2,5,4,8] else #[2,5,4,6]))) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1,11] else #[2,0,1,6]) else (if i.val < 3 then #[2,5,1,6] else (if i.val < 4 then #[2,5,4,13] else #[2,5,4,6]))) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 57 else 31)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,2,1] else #[1,1,0,3,0]) else (if i.val < 3 then #[2,2,3,0,3] else #[3,3,2,1,2])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,2,1] else #[1,1,0,3,0]) else (if i.val < 3 then #[2,2,3,0,3] else #[3,3,2,1,2])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 5 := ((if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 3 else 3)) : Fin 5)
private def stepWitness (i : Fin 4) (j : Fin 5) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[1,2,15,15,6] else #[1,2,15,15,6]) else (if i.val < 3 then #[4,2,1,14,7] else #[4,2,1,3,10])) : Array (Fin 16))[j.val]!
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
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else 25)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 5) else (if i.val < 3 then 10 else 15)) else (if i.val < 6 then (if i.val < 5 then 16 else 21) else (if i.val < 7 then 25 else 28))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 35 else 38) else (if i.val < 11 then 41 else 44)) else (if i.val < 14 then (if i.val < 13 then 51 else 54) else (if i.val < 15 then 58 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,15,14,13] else #[4,14,15,9]) else (if i.val < 3 then #[15,5,4,11] else #[14,4,5,7])) else (if i.val < 6 then (if i.val < 5 then #[1,3,2,12] else #[0,2,3,8]) else (if i.val < 7 then #[11,8,9,2] else #[10,9,8,14]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,6,7,0] else #[12,7,6,4]) else (if i.val < 11 then #[7,12,13,3] else #[6,13,12,15])) else (if i.val < 14 then (if i.val < 13 then #[9,10,11,1] else #[8,11,10,5]) else (if i.val < 15 then #[3,1,0,10] else #[2,0,1,6])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 1 else 12)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 4 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 11 else 10) else (if i.val < 11 then 14 else 7)) else (if i.val < 14 then (if i.val < 13 then 13 else 9) else (if i.val < 15 then 8 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 15 else 5)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 15 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 1) else (if i.val < 11 then 14 else 2)) else (if i.val < 14 then (if i.val < 13 then 4 else 0) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 0 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 3) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 3 else 3) else (if i.val < 15 then 2 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1,6] else #[2,0,1,6]) else (if i.val < 3 then #[2,5,1,11] else (if i.val < 4 then #[2,5,4,9] else #[2,5,4,6]))) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1,6] else #[2,0,1,6]) else (if i.val < 3 then #[2,5,1,11] else (if i.val < 4 then #[2,5,4,12] else #[2,5,4,6]))) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 57) else (if i.val < 3 then 59 else 61)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,0,1,2] else #[1,1,1,0,3]) else (if i.val < 3 then #[2,2,2,3,0] else #[3,3,3,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,0,1,2] else #[1,1,1,0,3]) else (if i.val < 3 then #[2,2,2,3,0] else #[3,3,3,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 5 := ((if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 4 else 4)) : Fin 5)
private def stepWitness (i : Fin 4) (j : Fin 5) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[1,2,7,15,15] else #[4,2,8,14,15]) else (if i.val < 3 then #[4,2,7,14,15] else #[1,2,8,15,15])) : Array (Fin 16))[j.val]!
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
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else 26)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 5) else (if i.val < 3 then 10 else 15)) else (if i.val < 6 then (if i.val < 5 then 16 else 21) else (if i.val < 7 then 26 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 32 else 37) else (if i.val < 11 then 42 else 47)) else (if i.val < 14 then (if i.val < 13 then 48 else 53) else (if i.val < 15 then 58 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,15,14,13] else #[4,14,15,9]) else (if i.val < 3 then #[15,5,4,11] else #[14,4,5,7])) else (if i.val < 6 then (if i.val < 5 then #[1,3,2,12] else #[0,2,3,8]) else (if i.val < 7 then #[11,13,12,5] else #[10,12,13,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,11,10,15] else #[12,10,11,3]) else (if i.val < 11 then #[7,9,8,4] else #[6,8,9,0])) else (if i.val < 14 then (if i.val < 13 then #[9,7,6,14] else #[8,6,7,2]) else (if i.val < 15 then #[3,1,0,10] else #[2,0,1,6])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 1 else 12)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 4 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 10) else (if i.val < 11 then 14 else 7)) else (if i.val < 14 then (if i.val < 13 then 11 else 9) else (if i.val < 15 then 8 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 15 else 5)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 15 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 1) else (if i.val < 11 then 14 else 2)) else (if i.val < 14 then (if i.val < 13 then 6 else 0) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 0 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 3 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 2 else 3) else (if i.val < 15 then 2 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1,11] else #[2,0,1,6]) else (if i.val < 3 then #[2,5,1,12] else (if i.val < 4 then #[2,5,4,9] else #[2,5,4,7]))) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1,11] else #[2,0,1,6]) else (if i.val < 3 then #[2,5,1,12] else (if i.val < 4 then #[2,5,4,12] else #[2,5,4,7]))) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 59 else 24)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,1,2] else #[1,1,0,0,3]) else (if i.val < 3 then #[2,2,3,3,0] else #[3,3,2,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,1,2] else #[1,1,0,0,3]) else (if i.val < 3 then #[2,2,3,3,0] else #[3,3,2,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 5 := ((if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 4 else 4)) : Fin 5)
private def stepWitness (i : Fin 4) (j : Fin 5) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[1,2,15,6,15] else #[1,2,15,12,15]) else (if i.val < 3 then #[4,2,15,7,15] else #[4,2,15,8,15])) : Array (Fin 16))[j.val]!
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
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else 27)) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 64 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 5) else (if i.val < 3 then 10 else 15)) else (if i.val < 6 then (if i.val < 5 then 16 else 21) else (if i.val < 7 then 27 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 33 else 36) else (if i.val < 11 then 43 else 46)) else (if i.val < 14 then (if i.val < 13 then 49 else 52) else (if i.val < 15 then 58 else 63)))) : Fin 64)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,15,14,13] else #[4,14,15,9]) else (if i.val < 3 then #[15,5,4,11] else #[14,4,5,7])) else (if i.val < 6 then (if i.val < 5 then #[1,3,2,12] else #[0,2,3,8]) else (if i.val < 7 then #[11,8,9,1] else #[10,9,8,5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,6,7,3] else #[12,7,6,15]) else (if i.val < 11 then #[7,12,13,0] else #[6,13,12,4])) else (if i.val < 14 then (if i.val < 13 then #[9,10,11,2] else #[8,11,10,14]) else (if i.val < 15 then #[3,1,0,10] else #[2,0,1,6])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 3) else (if i.val < 3 then 1 else 12)) else (if i.val < 6 then (if i.val < 5 then 6 else 5) else (if i.val < 7 then 4 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 11 else 10) else (if i.val < 11 then 14 else 7)) else (if i.val < 14 then (if i.val < 13 then 13 else 9) else (if i.val < 15 then 8 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 15) else (if i.val < 3 then 15 else 5)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 15 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 1) else (if i.val < 11 then 14 else 2)) else (if i.val < 14 then (if i.val < 13 then 4 else 0) else (if i.val < 15 then 0 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 0 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 3) else (if i.val < 11 then 3 else 3)) else (if i.val < 14 then (if i.val < 13 then 3 else 3) else (if i.val < 15 then 2 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1,6] else #[2,0,1,6]) else (if i.val < 3 then #[2,5,1,9] else (if i.val < 4 then #[2,5,4,8] else #[2,5,4,7]))) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 4) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[2,0,1,6] else #[2,0,1,6]) else (if i.val < 3 then #[2,5,1,9] else (if i.val < 4 then #[2,5,4,13] else #[2,5,4,7]))) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 63 else 28) else (if i.val < 3 then 57 else 59)) : Fin 64)⟩
private def quotientNext (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,2,3] else #[1,1,0,3,2]) else (if i.val < 3 then #[2,2,3,0,1] else #[3,3,2,1,0])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 5) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,0,1,2,3] else #[1,1,0,3,2]) else (if i.val < 3 then #[2,2,3,0,1] else #[3,3,2,1,0])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 5 := ((if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 3 else 4)) : Fin 5)
private def stepWitness (i : Fin 4) (j : Fin 5) : Fin 16 := ((if i.val < 2 then (if i.val < 1 then #[1,2,15,15,15] else #[1,2,15,9,9]) else (if i.val < 3 then #[4,2,6,14,6] else #[4,2,9,7,15])) : Array (Fin 16))[j.val]!
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
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else (if j.val < 4 then 1 else 2))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[21,31,26,30,29] else #[20,11,14,10,12]) else (if i.val < 3 then #[23,29,24,28,31] else #[22,9,12,8,14])) else (if i.val < 6 then (if i.val < 5 then #[17,14,11,15,9] else #[16,26,31,27,24]) else (if i.val < 7 then #[19,12,9,13,11] else #[18,24,29,25,26]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[29,23,18,22,21] else #[28,3,6,2,4]) else (if i.val < 11 then #[31,21,16,20,23] else #[30,1,4,0,6])) else (if i.val < 14 then (if i.val < 13 then #[25,6,3,7,1] else #[24,18,23,19,16]) else (if i.val < 15 then #[27,4,1,5,3] else #[26,16,21,17,18])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[5,15,10,14,13] else #[4,27,30,26,28]) else (if i.val < 19 then #[7,13,8,12,15] else #[6,25,28,24,30])) else (if i.val < 22 then (if i.val < 21 then #[1,30,27,31,25] else #[0,10,15,11,8]) else (if i.val < 23 then #[3,28,25,29,27] else #[2,8,13,9,10]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[13,7,2,6,5] else #[12,19,22,18,20]) else (if i.val < 27 then #[15,5,0,4,7] else #[14,17,20,16,22])) else (if i.val < 30 then (if i.val < 29 then #[9,22,19,23,17] else #[8,2,7,3,0]) else (if i.val < 31 then #[11,20,17,21,19] else #[10,0,5,1,2]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 5 else 28)) else (if i.val < 6 then (if i.val < 5 then 24 else 3) else (if i.val < 7 then 30 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 20 else 23) else (if i.val < 11 then 1 else 15)) else (if i.val < 14 then (if i.val < 13 then 17 else 21) else (if i.val < 15 then 16 else 19)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 7 else 26) else (if i.val < 19 then 31 else 27)) else (if i.val < 22 then (if i.val < 21 then 8 else 6) else (if i.val < 23 then 29 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 14 else 22) else (if i.val < 27 then 10 else 13)) else (if i.val < 30 then (if i.val < 29 then 18 else 12) else (if i.val < 31 then 11 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 31 else 29)) else (if i.val < 6 then (if i.val < 5 then 26 else 31) else (if i.val < 7 then 24 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 23) else (if i.val < 11 then 31 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 16) else (if i.val < 15 then 1 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 30) else (if i.val < 19 then 15 else 30)) else (if i.val < 22 then (if i.val < 21 then 10 else 10) else (if i.val < 23 then 27 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 5 else 20) else (if i.val < 27 then 0 else 5)) else (if i.val < 30 then (if i.val < 29 then 2 else 0) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 2) else (if i.val < 7 then 3 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 3) else (if i.val < 11 then 0 else 1)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 2 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 1) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 4) else (if i.val < 27 then 2 else 3)) else (if i.val < 30 then (if i.val < 29 then 3 else 4) else (if i.val < 31 then 3 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[10,0,5,20,2] else #[10,0,5,1,2]) else (if i.val < 3 then #[10,21,5,1,13] else (if i.val < 4 then #[10,21,16,17,18] else #[10,21,16,20,18]))) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[10,0,5,20,2] else #[10,0,5,1,2]) else (if i.val < 3 then #[10,21,5,1,13] else (if i.val < 4 then #[10,21,16,17,18] else #[10,21,16,20,18]))) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 28) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,1,0,0] else #[1,1,0,1,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,1,0,0] else #[1,1,0,1,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 5 := ((if i.val < 1 then 0 else 2) : Fin 5)
private def stepWitness (i : Fin 2) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[5,10,31,28,27] else #[5,10,31,19,27]) : Array (Fin 32))[j.val]!
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
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else (if j.val < 4 then 1 else 24))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 4 else 5)) else (if i.val < 6 then (if i.val < 5 then 10 else 11) else (if i.val < 7 then 14 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 17) else (if i.val < 11 then 20 else 21)) else (if i.val < 14 then (if i.val < 13 then 24 else 25) else (if i.val < 15 then 28 else 29)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 35) else (if i.val < 19 then 38 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 41) else (if i.val < 23 then 44 else 45))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 50 else 51) else (if i.val < 27 then 54 else 55)) else (if i.val < 30 then (if i.val < 29 then 58 else 59) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,31,28,30,27] else #[10,5,6,4,17]) else (if i.val < 3 then #[9,6,5,7,25] else #[8,28,31,29,19])) else (if i.val < 6 then (if i.val < 5 then #[31,11,8,10,23] else #[30,1,2,0,13]) else (if i.val < 7 then #[29,2,1,3,21] else #[28,8,11,9,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,7,4,6,24] else #[2,29,30,28,18]) else (if i.val < 11 then #[1,30,29,31,26] else #[0,4,7,5,16])) else (if i.val < 14 then (if i.val < 13 then #[23,27,24,26,31] else #[22,17,18,16,5]) else (if i.val < 15 then #[21,18,17,19,29] else #[20,24,27,25,7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[27,23,20,22,11] else #[26,13,14,12,1]) else (if i.val < 19 then #[25,14,13,15,9] else #[24,20,23,21,3])) else (if i.val < 22 then (if i.val < 21 then #[15,19,16,18,28] else #[14,25,26,24,6]) else (if i.val < 23 then #[13,26,25,27,30] else #[12,16,19,17,4]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[19,15,12,14,8] else #[18,21,22,20,2]) else (if i.val < 27 then #[17,22,21,23,10] else #[16,12,15,13,0])) else (if i.val < 30 then (if i.val < 29 then #[7,3,0,2,20] else #[6,9,10,8,14]) else (if i.val < 31 then #[5,10,9,11,22] else #[4,0,3,1,12]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 22 else 3)) else (if i.val < 6 then (if i.val < 5 then 1 else 15) else (if i.val < 7 then 16 else 20))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 24) else (if i.val < 11 then 8 else 6)) else (if i.val < 14 then (if i.val < 13 then 5 else 27) else (if i.val < 15 then 28 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 17) else (if i.val < 19 then 31 else 14)) else (if i.val < 22 then (if i.val < 21 then 23 else 29) else (if i.val < 23 then 25 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 18 else 30) else (if i.val < 27 then 19 else 12)) else (if i.val < 30 then (if i.val < 29 then 10 else 13) else (if i.val < 31 then 11 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 28 else 31)) else (if i.val < 6 then (if i.val < 5 then 31 else 1) else (if i.val < 7 then 1 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 30) else (if i.val < 11 then 4 else 4)) else (if i.val < 14 then (if i.val < 13 then 31 else 27) else (if i.val < 15 then 29 else 27)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 11 else 1) else (if i.val < 19 then 20 else 3)) else (if i.val < 22 then (if i.val < 21 then 28 else 19) else (if i.val < 23 then 30 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 2) else (if i.val < 27 then 12 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 3) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 3 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 1)) else (if i.val < 14 then (if i.val < 13 then 4 else 3) else (if i.val < 15 then 4 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 4) else (if i.val < 19 then 3 else 4)) else (if i.val < 22 then (if i.val < 21 then 4 else 3) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 4) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 2 else 3) else (if i.val < 31 then 3 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[4,0,3,10,23] else #[4,0,3,1,12]) else (if i.val < 3 then #[4,11,3,1,12] else (if i.val < 4 then #[4,11,8,9,16] else #[4,11,8,10,12]))) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[4,0,3,10,23] else #[4,0,3,1,12]) else (if i.val < 3 then #[4,11,3,1,12] else (if i.val < 4 then #[4,11,8,9,27] else #[4,11,8,10,12]))) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 57) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,0,1,0] else #[1,1,1,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,0,1,0] else #[1,1,1,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 5 := ((if i.val < 1 then 0 else 3) : Fin 5)
private def stepWitness (i : Fin 2) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[3,4,14,31,29] else #[8,4,17,28,30]) : Array (Fin 32))[j.val]!
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
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else (if j.val < 4 then 1 else 26))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 4 else 5)) else (if i.val < 6 then (if i.val < 5 then 10 else 11) else (if i.val < 7 then 14 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 17) else (if i.val < 11 then 20 else 21)) else (if i.val < 14 then (if i.val < 13 then 26 else 27) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 33) else (if i.val < 19 then 36 else 37)) else (if i.val < 22 then (if i.val < 21 then 42 else 43) else (if i.val < 23 then 46 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 49) else (if i.val < 27 then 52 else 53)) else (if i.val < 30 then (if i.val < 29 then 58 else 59) else (if i.val < 31 then 62 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,31,28,30,27] else #[10,5,6,4,18]) else (if i.val < 3 then #[9,6,5,7,26] else #[8,28,31,29,19])) else (if i.val < 6 then (if i.val < 5 then #[31,11,8,10,23] else #[30,1,2,0,14]) else (if i.val < 7 then #[29,2,1,3,22] else #[28,8,11,9,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,7,4,6,24] else #[2,29,30,28,17]) else (if i.val < 11 then #[1,30,29,31,25] else #[0,4,7,5,16])) else (if i.val < 14 then (if i.val < 13 then #[23,27,24,26,11] else #[22,17,18,16,2]) else (if i.val < 15 then #[21,18,17,19,10] else #[20,24,27,25,3])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[27,23,20,22,31] else #[26,13,14,12,6]) else (if i.val < 19 then #[25,14,13,15,30] else #[24,20,23,21,7])) else (if i.val < 22 then (if i.val < 21 then #[15,19,16,18,8] else #[14,25,26,24,1]) else (if i.val < 23 then #[13,26,25,27,9] else #[12,16,19,17,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[19,15,12,14,28] else #[18,21,22,20,5]) else (if i.val < 27 then #[17,22,21,23,29] else #[16,12,15,13,4])) else (if i.val < 30 then (if i.val < 29 then #[7,3,0,2,20] else #[6,9,10,8,13]) else (if i.val < 31 then #[5,10,9,11,21] else #[4,0,3,1,12]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 24 else 3)) else (if i.val < 6 then (if i.val < 5 then 1 else 15) else (if i.val < 7 then 16 else 20))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 26) else (if i.val < 11 then 8 else 6)) else (if i.val < 14 then (if i.val < 13 then 5 else 29) else (if i.val < 15 then 30 else 28)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 23) else (if i.val < 19 then 17 else 14)) else (if i.val < 22 then (if i.val < 21 then 25 else 27) else (if i.val < 23 then 31 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 18 else 22) else (if i.val < 27 then 19 else 12)) else (if i.val < 30 then (if i.val < 29 then 10 else 13) else (if i.val < 31 then 11 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 28 else 31)) else (if i.val < 6 then (if i.val < 5 then 31 else 1) else (if i.val < 7 then 1 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 30) else (if i.val < 11 then 4 else 4)) else (if i.val < 14 then (if i.val < 13 then 31 else 27) else (if i.val < 15 then 5 else 27)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 11 else 23) else (if i.val < 19 then 1 else 3)) else (if i.val < 22 then (if i.val < 21 then 28 else 30) else (if i.val < 23 then 6 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 10) else (if i.val < 27 then 12 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 3) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 3 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 3 else 1)) else (if i.val < 14 then (if i.val < 13 then 4 else 3) else (if i.val < 15 then 4 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 3) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 4 else 4) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 4) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 2 else 3) else (if i.val < 31 then 3 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[4,0,3,10,23] else #[4,0,3,1,12]) else (if i.val < 3 then #[4,11,3,1,24] else (if i.val < 4 then #[4,11,8,9,19] else #[4,11,8,10,15]))) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[4,0,3,10,23] else #[4,0,3,1,12]) else (if i.val < 3 then #[4,11,3,1,24] else (if i.val < 4 then #[4,11,8,9,24] else #[4,11,8,10,15]))) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 28) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,1,1,0] else #[1,1,0,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,1,1,0] else #[1,1,0,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 5 := ((if i.val < 1 then 0 else 2) : Fin 5)
private def stepWitness (i : Fin 2) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[3,4,31,12,29] else #[3,4,31,24,29]) : Array (Fin 32))[j.val]!
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
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else (if j.val < 4 then 2 else 24))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 5 else 7)) else (if i.val < 6 then (if i.val < 5 then 8 else 10) else (if i.val < 7 then 13 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 18) else (if i.val < 11 then 21 else 23)) else (if i.val < 14 then (if i.val < 13 then 24 else 26) else (if i.val < 15 then 29 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 34) else (if i.val < 19 then 37 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 42) else (if i.val < 23 then 45 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 50) else (if i.val < 27 then 53 else 55)) else (if i.val < 30 then (if i.val < 29 then 56 else 58) else (if i.val < 31 then 61 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,31,29,30,27] else #[11,30,28,31,23]) else (if i.val < 3 then #[8,29,31,28,19] else #[9,28,30,29,15])) else (if i.val < 6 then (if i.val < 5 then #[30,11,9,10,26] else #[31,10,8,11,22]) else (if i.val < 7 then #[28,9,11,8,18] else #[29,8,10,9,14]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,7,5,6,25] else #[3,6,4,7,21]) else (if i.val < 11 then #[0,5,7,4,17] else #[1,4,6,5,13])) else (if i.val < 14 then (if i.val < 13 then #[22,27,25,26,31] else #[23,26,24,27,11]) else (if i.val < 15 then #[20,25,27,24,7] else #[21,24,26,25,3])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[26,23,21,22,30] else #[27,22,20,23,10]) else (if i.val < 19 then #[24,21,23,20,6] else #[25,20,22,21,2])) else (if i.val < 22 then (if i.val < 21 then #[14,19,17,18,29] else #[15,18,16,19,9]) else (if i.val < 23 then #[12,17,19,16,5] else #[13,16,18,17,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,15,13,14,28] else #[19,14,12,15,8]) else (if i.val < 27 then #[16,13,15,12,4] else #[17,12,14,13,0])) else (if i.val < 30 then (if i.val < 29 then #[6,3,1,2,24] else #[7,2,0,3,20]) else (if i.val < 31 then #[4,1,3,0,16] else #[5,0,2,1,12]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 3 else 24)) else (if i.val < 6 then (if i.val < 5 then 19 else 1) else (if i.val < 7 then 21 else 18))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 31) else (if i.val < 11 then 6 else 8)) else (if i.val < 14 then (if i.val < 13 then 5 else 22) else (if i.val < 15 then 26 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 23 else 20) else (if i.val < 19 then 29 else 14)) else (if i.val < 22 then (if i.val < 21 then 25 else 28) else (if i.val < 23 then 9 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 27 else 16) else (if i.val < 27 then 17 else 12)) else (if i.val < 30 then (if i.val < 29 then 13 else 10) else (if i.val < 31 then 11 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 31 else 29)) else (if i.val < 6 then (if i.val < 5 then 10 else 31) else (if i.val < 7 then 8 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 7) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 31 else 11) else (if i.val < 15 then 27 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 10) else (if i.val < 19 then 23 else 2)) else (if i.val < 22 then (if i.val < 21 then 29 else 19) else (if i.val < 23 then 5 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 28 else 12) else (if i.val < 27 then 12 else 0)) else (if i.val < 30 then (if i.val < 29 then 2 else 0) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 0) else (if i.val < 7 then 3 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 2 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 4) else (if i.val < 19 then 2 else 4)) else (if i.val < 22 then (if i.val < 21 then 4 else 3) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 2) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 3 else 2) else (if i.val < 31 then 3 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,1,22] else #[5,0,2,1,12]) else (if i.val < 3 then #[5,10,2,6,12] else (if i.val < 4 then #[5,10,8,9,17] else #[5,10,8,9,12]))) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,1,22] else #[5,0,2,1,12]) else (if i.val < 3 then #[5,10,2,6,12] else (if i.val < 4 then #[5,10,8,9,27] else #[5,10,8,9,12]))) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 28) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,1,1,1] else #[1,1,0,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,1,1,1] else #[1,1,0,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 5 := ((if i.val < 1 then 0 else 2) : Fin 5)
private def stepWitness (i : Fin 2) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[2,5,31,13,12] else #[2,5,31,24,12]) : Array (Fin 32))[j.val]!
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
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else (if j.val < 4 then 2 else 25))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 5 else 7)) else (if i.val < 6 then (if i.val < 5 then 8 else 10) else (if i.val < 7 then 13 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 18) else (if i.val < 11 then 21 else 23)) else (if i.val < 14 then (if i.val < 13 then 25 else 27) else (if i.val < 15 then 28 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 35) else (if i.val < 19 then 36 else 38)) else (if i.val < 22 then (if i.val < 21 then 41 else 43) else (if i.val < 23 then 44 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 51) else (if i.val < 27 then 52 else 54)) else (if i.val < 30 then (if i.val < 29 then 56 else 58) else (if i.val < 31 then 61 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,31,29,30,27] else #[11,30,28,31,23]) else (if i.val < 3 then #[8,29,31,28,19] else #[9,28,30,29,15])) else (if i.val < 6 then (if i.val < 5 then #[30,11,9,10,26] else #[31,10,8,11,22]) else (if i.val < 7 then #[28,9,11,8,18] else #[29,8,10,9,14]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,7,5,6,25] else #[3,6,4,7,21]) else (if i.val < 11 then #[0,5,7,4,17] else #[1,4,6,5,13])) else (if i.val < 14 then (if i.val < 13 then #[22,17,19,18,5] else #[23,16,18,19,1]) else (if i.val < 15 then #[20,19,17,16,29] else #[21,18,16,17,9])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[26,13,15,14,4] else #[27,12,14,15,0]) else (if i.val < 19 then #[24,15,13,12,28] else #[25,14,12,13,8])) else (if i.val < 22 then (if i.val < 21 then #[14,25,27,26,7] else #[15,24,26,27,3]) else (if i.val < 23 then #[12,27,25,24,31] else #[13,26,24,25,11]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,21,23,22,6] else #[19,20,22,23,2]) else (if i.val < 27 then #[16,23,21,20,30] else #[17,22,20,21,10])) else (if i.val < 30 then (if i.val < 29 then #[6,3,1,2,24] else #[7,2,0,3,20]) else (if i.val < 31 then #[4,1,3,0,16] else #[5,0,2,1,12]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 3 else 24)) else (if i.val < 6 then (if i.val < 5 then 19 else 1) else (if i.val < 7 then 20 else 18))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 31) else (if i.val < 11 then 6 else 8)) else (if i.val < 14 then (if i.val < 13 then 5 else 22) else (if i.val < 15 then 28 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 16) else (if i.val < 19 then 17 else 14)) else (if i.val < 22 then (if i.val < 21 then 25 else 27) else (if i.val < 23 then 9 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 23 else 21) else (if i.val < 27 then 29 else 12)) else (if i.val < 30 then (if i.val < 29 then 13 else 10) else (if i.val < 31 then 11 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 31 else 29)) else (if i.val < 6 then (if i.val < 5 then 10 else 31) else (if i.val < 7 then 8 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 7) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 31 else 11) else (if i.val < 15 then 19 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 12) else (if i.val < 19 then 12 else 2)) else (if i.val < 22 then (if i.val < 21 then 29 else 27) else (if i.val < 23 then 5 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 8) else (if i.val < 27 then 23 else 0)) else (if i.val < 30 then (if i.val < 29 then 2 else 0) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 0) else (if i.val < 7 then 3 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 1 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 1) else (if i.val < 19 then 3 else 4)) else (if i.val < 22 then (if i.val < 21 then 4 else 3) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 4) else (if i.val < 27 then 1 else 4)) else (if i.val < 30 then (if i.val < 29 then 3 else 2) else (if i.val < 31 then 3 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,1,12] else #[5,0,2,1,12]) else (if i.val < 3 then #[5,10,2,6,22] else (if i.val < 4 then #[5,10,8,9,19] else #[5,10,8,9,12]))) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,1,12] else #[5,0,2,1,12]) else (if i.val < 3 then #[5,10,2,6,22] else (if i.val < 4 then #[5,10,8,9,25] else #[5,10,8,9,12]))) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 57) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,0,1,1] else #[1,1,1,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,0,1,1] else #[1,1,1,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 5 := ((if i.val < 1 then 0 else 3) : Fin 5)
private def stepWitness (i : Fin 2) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[2,5,14,31,30] else #[8,5,17,29,30]) : Array (Fin 32))[j.val]!
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
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else (if j.val < 4 then 3 else 24))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 12 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 34) else (if i.val < 19 then 36 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 43) else (if i.val < 23 then 45 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 50) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,31,29,30,27] else #[11,4,6,7,13]) else (if i.val < 3 then #[8,29,31,28,19] else #[9,6,4,5,21])) else (if i.val < 6 then (if i.val < 5 then #[30,1,3,2,16] else #[31,10,8,11,22]) else (if i.val < 7 then #[28,3,1,0,24] else #[29,8,10,9,14]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,7,5,6,25] else #[3,28,30,31,15]) else (if i.val < 11 then #[0,5,7,4,17] else #[1,30,28,29,23])) else (if i.val < 14 then (if i.val < 13 then #[22,27,25,26,31] else #[23,16,18,19,1]) else (if i.val < 15 then #[20,25,27,24,7] else #[21,18,16,17,9])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[26,13,15,14,4] else #[27,22,20,23,10]) else (if i.val < 19 then #[24,15,13,12,28] else #[25,20,22,21,2])) else (if i.val < 22 then (if i.val < 21 then #[14,19,17,18,29] else #[15,24,26,27,3]) else (if i.val < 23 then #[12,17,19,16,5] else #[13,26,24,25,11]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,21,23,22,6] else #[19,14,12,15,8]) else (if i.val < 27 then #[16,23,21,20,30] else #[17,12,14,13,0])) else (if i.val < 30 then (if i.val < 29 then #[6,9,11,10,18] else #[7,2,0,3,20]) else (if i.val < 31 then #[4,11,9,8,26] else #[5,0,2,1,12]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 3 else 24)) else (if i.val < 6 then (if i.val < 5 then 15 else 1) else (if i.val < 7 then 16 else 17))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 26) else (if i.val < 11 then 6 else 8)) else (if i.val < 14 then (if i.val < 13 then 5 else 18) else (if i.val < 15 then 27 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 23 else 21) else (if i.val < 19 then 28 else 14)) else (if i.val < 22 then (if i.val < 21 then 25 else 29) else (if i.val < 23 then 9 else 22))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 30 else 19) else (if i.val < 27 then 20 else 12)) else (if i.val < 30 then (if i.val < 29 then 13 else 10) else (if i.val < 31 then 11 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 31 else 29)) else (if i.val < 6 then (if i.val < 5 then 1 else 31) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 30) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 31 else 1) else (if i.val < 15 then 27 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 10) else (if i.val < 19 then 28 else 2)) else (if i.val < 22 then (if i.val < 21 then 29 else 19) else (if i.val < 23 then 5 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6 else 12) else (if i.val < 27 then 12 else 0)) else (if i.val < 30 then (if i.val < 29 then 2 else 0) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 2 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 4) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 4 else 3) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 2) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 3 else 2) else (if i.val < 31 then 3 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,11,22] else #[5,0,2,1,12]) else (if i.val < 3 then #[5,10,2,28,12] else (if i.val < 4 then #[5,10,8,11,17] else #[5,10,8,9,12]))) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,11,22] else #[5,0,2,1,12]) else (if i.val < 3 then #[5,10,2,28,12] else (if i.val < 4 then #[5,10,8,11,27] else #[5,10,8,9,12]))) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 28) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,1,0,1] else #[1,1,0,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,1,0,1] else #[1,1,0,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 5 := ((if i.val < 1 then 0 else 2) : Fin 5)
private def stepWitness (i : Fin 2) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[2,5,31,30,12] else #[2,5,31,9,12]) : Array (Fin 32))[j.val]!
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
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 10 else 0) else (if j.val < 3 then 5 else (if j.val < 4 then 3 else 25))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 64 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 12 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 25 else 26) else (if i.val < 15 then 28 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 35) else (if i.val < 19 then 37 else 38)) else (if i.val < 22 then (if i.val < 21 then 41 else 42) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 51) else (if i.val < 27 then 53 else 54)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 60 else 63))))) : Fin 64)
private def next (i : Fin 32) (j : Fin 5) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,31,29,30,27] else #[11,4,6,7,13]) else (if i.val < 3 then #[8,29,31,28,19] else #[9,6,4,5,21])) else (if i.val < 6 then (if i.val < 5 then #[30,1,3,2,16] else #[31,10,8,11,22]) else (if i.val < 7 then #[28,3,1,0,24] else #[29,8,10,9,14]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,7,5,6,25] else #[3,28,30,31,15]) else (if i.val < 11 then #[0,5,7,4,17] else #[1,30,28,29,23])) else (if i.val < 14 then (if i.val < 13 then #[22,17,19,18,5] else #[23,26,24,27,11]) else (if i.val < 15 then #[20,19,17,16,29] else #[21,24,26,25,3])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[26,23,21,22,30] else #[27,12,14,15,0]) else (if i.val < 19 then #[24,21,23,20,6] else #[25,14,12,13,8])) else (if i.val < 22 then (if i.val < 21 then #[14,25,27,26,7] else #[15,18,16,19,9]) else (if i.val < 23 then #[12,27,25,24,31] else #[13,16,18,17,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,15,13,14,28] else #[19,20,22,23,2]) else (if i.val < 27 then #[16,13,15,12,4] else #[17,22,20,21,10])) else (if i.val < 30 then (if i.val < 29 then #[6,9,11,10,18] else #[7,2,0,3,20]) else (if i.val < 31 then #[4,11,9,8,26] else #[5,0,2,1,12]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 3 else 24)) else (if i.val < 6 then (if i.val < 5 then 15 else 1) else (if i.val < 7 then 16 else 17))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 26) else (if i.val < 11 then 6 else 8)) else (if i.val < 14 then (if i.val < 13 then 5 else 18) else (if i.val < 15 then 29 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 19) else (if i.val < 19 then 20 else 14)) else (if i.val < 22 then (if i.val < 21 then 25 else 28) else (if i.val < 23 then 9 else 22))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 23 else 21) else (if i.val < 27 then 27 else 12)) else (if i.val < 30 then (if i.val < 29 then 13 else 10) else (if i.val < 31 then 11 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 31) else (if i.val < 3 then 31 else 29)) else (if i.val < 6 then (if i.val < 5 then 1 else 31) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 30) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 31 else 1) else (if i.val < 15 then 19 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 12) else (if i.val < 19 then 12 else 2)) else (if i.val < 22 then (if i.val < 21 then 29 else 27) else (if i.val < 23 then 5 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 8) else (if i.val < 27 then 30 else 0)) else (if i.val < 30 then (if i.val < 29 then 2 else 0) else (if i.val < 31 then 0 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 5 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 1 else 3)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 1 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 1) else (if i.val < 19 then 3 else 4)) else (if i.val < 22 then (if i.val < 21 then 4 else 3) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 4) else (if i.val < 27 then 4 else 4)) else (if i.val < 30 then (if i.val < 29 then 3 else 2) else (if i.val < 31 then 3 else 0))))) : Fin 5)

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

private def posWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,11,12] else #[5,0,2,1,12]) else (if i.val < 3 then #[5,10,2,28,22] else (if i.val < 4 then #[5,10,8,11,19] else #[5,10,8,9,12]))) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 5) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[5,0,2,11,12] else #[5,0,2,1,12]) else (if i.val < 3 then #[5,10,2,28,22] else (if i.val < 4 then #[5,10,8,11,25] else #[5,10,8,9,12]))) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 63 else 59) : Fin 64)⟩
private def quotientNext (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,0,0,1] else #[1,1,1,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 5) : Fin 2 := ((if i.val < 1 then #[0,0,0,0,1] else #[1,1,1,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 5 := ((if i.val < 1 then 0 else 4) : Fin 5)
private def stepWitness (i : Fin 2) (j : Fin 5) : Fin 32 := ((if i.val < 1 then #[2,5,14,30,31] else #[8,5,14,28,31]) : Array (Fin 32))[j.val]!
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
def normalGenerators (j : Fin 6) : Source := ⟨((if j.val < 3 then (if j.val < 1 then 10 else (if j.val < 2 then 0 else 5)) else (if j.val < 4 then 1 else (if j.val < 5 then 2 else 24))) : Fin 64)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63)))))) : Fin 64)
private def next (i : Fin 64) (j : Fin 6) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[21,63,58,62,61,55] else #[20,11,14,10,12,35]) else (if i.val < 3 then #[23,61,56,60,63,47] else #[22,9,12,8,14,27])) else (if i.val < 6 then (if i.val < 5 then #[17,14,11,15,9,51] else #[16,58,63,59,56,39]) else (if i.val < 7 then #[19,12,9,13,11,43] else #[18,56,61,57,58,31]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[61,23,18,22,21,53] else #[60,3,6,2,4,33]) else (if i.val < 11 then #[63,21,16,20,23,45] else #[62,1,4,0,6,25])) else (if i.val < 14 then (if i.val < 13 then #[57,6,3,7,1,49] else #[56,18,23,19,16,37]) else (if i.val < 15 then #[59,4,1,5,3,41] else #[58,16,21,17,18,29])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[5,15,10,14,13,50] else #[4,59,62,58,60,38]) else (if i.val < 19 then #[7,13,8,12,15,42] else #[6,57,60,56,62,30])) else (if i.val < 22 then (if i.val < 21 then #[1,62,59,63,57,54] else #[0,10,15,11,8,34]) else (if i.val < 23 then #[3,60,57,61,59,46] else #[2,8,13,9,10,26]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[45,55,50,54,53,63] else #[44,35,38,34,36,11]) else (if i.val < 27 then #[47,53,48,52,55,23] else #[46,33,36,32,38,3])) else (if i.val < 30 then (if i.val < 29 then #[41,38,35,39,33,59] else #[40,50,55,51,48,15]) else (if i.val < 31 then #[43,36,33,37,35,19] else #[42,48,53,49,50,7]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[53,47,42,46,45,61] else #[52,27,30,26,28,9]) else (if i.val < 35 then #[55,45,40,44,47,21] else #[54,25,28,24,30,1])) else (if i.val < 38 then (if i.val < 37 then #[49,30,27,31,25,57] else #[48,42,47,43,40,13]) else (if i.val < 39 then #[51,28,25,29,27,17] else #[50,40,45,41,42,5]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[29,39,34,38,37,58] else #[28,51,54,50,52,14]) else (if i.val < 43 then #[31,37,32,36,39,18] else #[30,49,52,48,54,6])) else (if i.val < 46 then (if i.val < 45 then #[25,54,51,55,49,62] else #[24,34,39,35,32,10]) else (if i.val < 47 then #[27,52,49,53,51,22] else #[26,32,37,33,34,2])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[37,31,26,30,29,56] else #[36,43,46,42,44,12]) else (if i.val < 51 then #[39,29,24,28,31,16] else #[38,41,44,40,46,4])) else (if i.val < 54 then (if i.val < 53 then #[33,46,43,47,41,60] else #[32,26,31,27,24,8]) else (if i.val < 55 then #[35,44,41,45,43,20] else #[34,24,29,25,26,0]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[13,7,2,6,5,48] else #[12,19,22,18,20,36]) else (if i.val < 59 then #[15,5,0,4,7,40] else #[14,17,20,16,22,28])) else (if i.val < 62 then (if i.val < 61 then #[9,22,19,23,17,52] else #[8,2,7,3,0,32]) else (if i.val < 63 then #[11,20,17,21,19,44] else #[10,0,5,1,2,24])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 4) else (if i.val < 3 then 5 else 42)) else (if i.val < 6 then (if i.val < 5 then 36 else 3) else (if i.val < 7 then 47 else 37))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 29 else 33) else (if i.val < 11 then 1 else 19)) else (if i.val < 14 then (if i.val < 13 then 21 else 31) else (if i.val < 15 then 20 else 28)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8 else 39) else (if i.val < 19 then 59 else 40)) else (if i.val < 22 then (if i.val < 21 then 9 else 7) else (if i.val < 23 then 45 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6 else 44) else (if i.val < 27 then 34 else 58)) else (if i.val < 30 then (if i.val < 29 then 46 else 43) else (if i.val < 31 then 52 else 56))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 35 else 55) else (if i.val < 35 then 30 else 22)) else (if i.val < 38 then (if i.val < 37 then 60 else 54) else (if i.val < 39 then 63 else 18))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 49) else (if i.val < 43 then 50 else 57)) else (if i.val < 46 then (if i.val < 45 then 41 else 11) else (if i.val < 47 then 61 else 24)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 51) else (if i.val < 51 then 25 else 62)) else (if i.val < 54 then (if i.val < 53 then 53 else 27) else (if i.val < 55 then 26 else 15))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 17 else 32) else (if i.val < 59 then 12 else 16)) else (if i.val < 62 then (if i.val < 61 then 23 else 14) else (if i.val < 63 then 13 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 63) else (if i.val < 3 then 63 else 61)) else (if i.val < 6 then (if i.val < 5 then 58 else 63) else (if i.val < 7 then 56 else 58))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 23) else (if i.val < 11 then 63 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 16) else (if i.val < 15 then 1 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 62) else (if i.val < 19 then 15 else 62)) else (if i.val < 22 then (if i.val < 21 then 10 else 10) else (if i.val < 23 then 59 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 63 else 55) else (if i.val < 27 then 23 else 53)) else (if i.val < 30 then (if i.val < 29 then 59 else 55) else (if i.val < 31 then 35 else 50))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 45 else 47) else (if i.val < 35 then 21 else 1)) else (if i.val < 38 then (if i.val < 37 then 57 else 47) else (if i.val < 39 then 40 else 5))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 58 else 39) else (if i.val < 43 then 39 else 54)) else (if i.val < 46 then (if i.val < 45 then 62 else 10) else (if i.val < 47 then 32 else 2)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 56 else 12) else (if i.val < 51 then 24 else 4)) else (if i.val < 54 then (if i.val < 53 then 60 else 24) else (if i.val < 55 then 24 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 5 else 20) else (if i.val < 59 then 0 else 5)) else (if i.val < 62 then (if i.val < 61 then 2 else 0) else (if i.val < 63 then 0 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 6 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 4 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 2) else (if i.val < 7 then 3 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 3) else (if i.val < 11 then 0 else 1)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 2 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 1) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 5 else 3) else (if i.val < 27 then 5 else 3)) else (if i.val < 30 then (if i.val < 29 then 5 else 2) else (if i.val < 31 then 4 else 4))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 4 else 3) else (if i.val < 35 then 5 else 5)) else (if i.val < 38 then (if i.val < 37 then 5 else 2) else (if i.val < 39 then 3 else 5))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 5 else 3) else (if i.val < 43 then 4 else 4)) else (if i.val < 46 then (if i.val < 45 then 5 else 5) else (if i.val < 47 then 3 else 5)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 5 else 5) else (if i.val < 51 then 2 else 5)) else (if i.val < 54 then (if i.val < 53 then 5 else 4) else (if i.val < 55 then 3 else 5))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 4 else 4) else (if i.val < 59 then 2 else 3)) else (if i.val < 62 then (if i.val < 61 then 3 else 4) else (if i.val < 63 then 3 else 0)))))) : Fin 6)

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

private def posWitness (i : Fin 5) (j : Fin 6) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then #[10,0,5,20,2,45] else #[10,0,5,1,2,24]) else (if i.val < 3 then #[10,21,5,1,13,24] else (if i.val < 4 then #[10,21,16,17,18,34] else #[10,21,16,20,18,24]))) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 5) (j : Fin 6) : Fin 64 := ((if i.val < 2 then (if i.val < 1 then #[10,0,5,20,2,45] else #[10,0,5,1,2,24]) else (if i.val < 3 then #[10,21,5,1,13,24] else (if i.val < 4 then #[10,21,16,17,18,55] else #[10,21,16,20,18,24]))) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 1) : Source := ⟨(63 : Fin 64)⟩
private def quotientNext (i : Fin 1) (j : Fin 5) : Fin 1 := (#[0,0,0,0,0] : Array (Fin 1))[j.val]!
private def quotientPrev (i : Fin 1) (j : Fin 5) : Fin 1 := (#[0,0,0,0,0] : Array (Fin 1))[j.val]!
private def quotientParents (i : Fin 1) : Fin 1 := (0 : Fin 1)
private def quotientLetters (i : Fin 1) : Fin 5 := (0 : Fin 5)
private def stepWitness (i : Fin 1) (j : Fin 5) : Fin 64 := (#[5,10,28,60,59] : Array (Fin 64))[j.val]!
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

end SymmetricSubgroupAsymptotics.RDTBinaryNormal8T29
