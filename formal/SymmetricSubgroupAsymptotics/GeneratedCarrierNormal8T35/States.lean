import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T35

/-! Exact original normal states and quotient rows for 8T35.
Selected by export_lean_carrier_normal_registry_selected.py; all finite facts are checked
in Lean's kernel. This file certifies normal-state coverage, not the later
pair/character/transport acceptance of those states. -/

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T35

abbrev Source := FiniteGroupRow 128
local instance selectedStateSourceGroup : Group Source := BinaryMenuCayley8T35.group

def generators (j : Fin 3) : Source :=
  ⟨BinaryMenuCayley8T35.certificate.next BinaryMenuCayley8T35.certificate.identity j⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  apply binaryNormal_full_generators_of_equiv BinaryMenuCayley8T35.generators
    generators BinaryMenuCayley8T35.originalEquiv
  intro j
  change BinaryMenuCayley8T35.certificate.toCayley.elements
    (BinaryMenuCayley8T35.certificate.toCayley.next
      BinaryMenuCayley8T35.certificate.toCayley.identity j)=_
  rw [FiniteCayleyCertificate.next_eq,FiniteCayleyCertificate.identity_eq,one_mul]

theorem source_card : Nat.card Source=128 := by
  rw [Nat.card_eq_fintype_card]
  rfl

namespace N0
def normalGenerators (j : Fin 0) : Source := Fin.elim0 j
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 1) : Fin 128 := (127 : Fin 128)
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

private def representatives (i : Fin 128) : Source := ⟨((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 71))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 25) else (if i.val < 11 then 47 else 79)) else (if i.val < 14 then (if i.val < 13 then 11 else 27) else (if i.val < 15 then 103 else 42)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 29 else 74) else (if i.val < 19 then 17 else 89)) else (if i.val < 22 then (if i.val < 21 then 111 else 43) else (if i.val < 23 then 31 else 75))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 19 else 91) else (if i.val < 27 then 106 else 21)) else (if i.val < 30 then (if i.val < 29 then 93 else 115) else (if i.val < 31 then 81 else 28))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 40 else 34) else (if i.val < 35 then 107 else 23)) else (if i.val < 38 then (if i.val < 37 then 95 else 51) else (if i.val < 39 then 83 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 41 else 35) else (if i.val < 43 then 119 else 85)) else (if i.val < 46 then (if i.val < 45 then 24 else 8) else (if i.val < 47 then 2 else 126)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 37 else 92) else (if i.val < 51 then 32 else 104)) else (if i.val < 54 then (if i.val < 53 then 98 else 38) else (if i.val < 55 then 125 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 87 else 26) else (if i.val < 59 then 9 else 3)) else (if i.val < 62 then (if i.val < 61 then 62 else 45) else (if i.val < 63 then 94 else 33)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 105 else 99) else (if i.val < 67 then 46 else 61)) else (if i.val < 70 then (if i.val < 69 then 122 else 5) else (if i.val < 71 then 88 else 0))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 72 else 66) else (if i.val < 75 then 6 else 121)) else (if i.val < 78 then (if i.val < 77 then 101 else 96) else (if i.val < 79 then 36 else 124)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 118 else 102) else (if i.val < 83 then 117 else 58)) else (if i.val < 86 then (if i.val < 85 then 13 else 90) else (if i.val < 87 then 1 else 73))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 67 else 14) else (if i.val < 91 then 57 else 109)) else (if i.val < 94 then (if i.val < 93 then 97 else 44) else (if i.val < 95 then 60 else 54))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 110 else 53) else (if i.val < 99 then 69 else 64)) else (if i.val < 102 then (if i.val < 101 then 4 else 120) else (if i.val < 103 then 114 else 70))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 113 else 20) else (if i.val < 107 then 100 else 116)) else (if i.val < 110 then (if i.val < 109 then 77 else 65) else (if i.val < 111 then 12 else 56)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 50 else 78) else (if i.val < 115 then 49 else 22)) else (if i.val < 118 then (if i.val < 117 then 108 else 52) else (if i.val < 119 then 16 else 68))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 112 else 84) else (if i.val < 123 then 18 else 76)) else (if i.val < 126 then (if i.val < 125 then 48 else 86) else (if i.val < 127 then 80 else 82))))))) : Fin 128)⟩
private def quotientNext (i : Fin 128) (j : Fin 3) : Fin 128 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,8,9])) else (if i.val < 6 then (if i.val < 5 then #[2,1,10] else #[11,12,13]) else (if i.val < 7 then #[14,15,16] else #[3,17,18]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[17,3,2] else #[19,16,15]) else (if i.val < 11 then #[20,21,22] else #[5,23,24])) else (if i.val < 14 then (if i.val < 13 then #[23,5,4] else #[25,22,21]) else (if i.val < 15 then #[6,26,27] else #[26,6,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[28,9,8] else #[8,7,29]) else (if i.val < 19 then #[30,31,32] else #[9,28,33])) else (if i.val < 22 then (if i.val < 21 then #[10,34,35] else #[34,10,1]) else (if i.val < 23 then #[36,13,12] else #[12,11,37]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[38,39,40] else #[13,36,41]) else (if i.val < 27 then #[15,14,42] else #[43,44,45])) else (if i.val < 30 then (if i.val < 29 then #[16,19,46] else #[37,47,48]) else (if i.val < 31 then #[18,49,50] else #[49,18,17]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[51,48,47] else #[52,53,54]) else (if i.val < 35 then #[21,20,55] else #[56,57,58])) else (if i.val < 38 then (if i.val < 37 then #[22,25,59] else #[29,60,61]) else (if i.val < 39 then #[24,62,63] else #[62,24,23]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[64,61,60] else #[65,66,67]) else (if i.val < 43 then #[55,68,69] else #[27,70,71])) else (if i.val < 46 then (if i.val < 45 then #[70,27,26] else #[72,69,68]) else (if i.val < 47 then #[73,74,75] else #[60,29,7])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[76,32,31] else #[31,30,73]) else (if i.val < 51 then #[77,78,79] else #[32,76,80])) else (if i.val < 54 then (if i.val < 53 then #[33,81,82] else #[81,33,28]) else (if i.val < 55 then #[67,75,74] else #[42,83,84]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[35,85,86] else #[85,35,34]) else (if i.val < 59 then #[87,84,83] else #[88,89,90])) else (if i.val < 62 then (if i.val < 61 then #[47,37,11] else #[91,40,39]) else (if i.val < 63 then #[39,38,88] else #[92,93,94])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then #[40,91,95] else #[41,96,97]) else (if i.val < 67 then #[96,41,36] else #[54,90,89])) else (if i.val < 70 then (if i.val < 69 then #[83,42,14] else #[98,45,44]) else (if i.val < 71 then #[44,43,52] else #[99,100,101]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then #[45,98,102] else #[46,103,104]) else (if i.val < 75 then #[103,46,19] else #[90,54,53])) else (if i.val < 78 then (if i.val < 77 then #[48,51,105] else #[50,106,107]) else (if i.val < 79 then #[106,50,49] else #[94,104,103])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then #[95,102,98] else #[53,52,43]) else (if i.val < 83 then #[97,101,100] else #[68,55,20])) else (if i.val < 86 then (if i.val < 85 then #[108,58,57] else #[57,56,65]) else (if i.val < 87 then #[109,110,111] else #[58,108,112]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then #[59,113,114] else #[113,59,25]) else (if i.val < 91 then #[75,67,66] else #[61,64,115])) else (if i.val < 94 then (if i.val < 93 then #[63,116,117] else #[116,63,62]) else (if i.val < 95 then #[79,114,113] else #[80,112,108]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then #[66,65,56] else #[82,111,110]) else (if i.val < 99 then #[69,72,118] else #[71,119,120])) else (if i.val < 102 then (if i.val < 101 then #[119,71,70] else #[111,82,81]) else (if i.val < 103 then #[112,80,76] else #[74,73,30]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then #[114,79,78] else #[121,118,72]) else (if i.val < 107 then #[78,77,121] else #[117,120,119])) else (if i.val < 110 then (if i.val < 109 then #[84,87,122] else #[86,123,124]) else (if i.val < 111 then #[123,86,85] else #[101,97,96])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then #[102,95,91] else #[89,88,38]) else (if i.val < 115 then #[104,94,93] else #[125,122,87])) else (if i.val < 118 then (if i.val < 117 then #[93,92,125] else #[107,124,123]) else (if i.val < 119 then #[126,105,51] else #[100,99,126]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then #[124,107,106] else #[105,126,99]) else (if i.val < 123 then #[127,115,64] else #[110,109,127])) else (if i.val < 126 then (if i.val < 125 then #[120,117,116] else #[115,127,109]) else (if i.val < 127 then #[118,121,77] else #[122,125,92]))))))) : Array (Fin 128))[j.val]!
private def quotientPrev (i : Fin 128) (j : Fin 3) : Fin 128 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,15] else #[0,4,21]) else (if i.val < 3 then #[4,0,8] else #[7,8,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,12] else #[11,12,1]) else (if i.val < 7 then #[14,15,2] else #[3,17,47]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[17,3,16] else #[19,16,3]) else (if i.val < 11 then #[20,21,4] else #[5,23,60])) else (if i.val < 14 then (if i.val < 13 then #[23,5,22] else #[25,22,5]) else (if i.val < 15 then #[6,26,68] else #[26,6,9])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[28,9,6] else #[8,7,31]) else (if i.val < 19 then #[30,31,7] else #[9,28,74])) else (if i.val < 22 then (if i.val < 21 then #[10,34,83] else #[34,10,13]) else (if i.val < 23 then #[36,13,10] else #[12,11,39]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[38,39,11] else #[13,36,89]) else (if i.val < 27 then #[15,14,44] else #[43,44,14])) else (if i.val < 30 then (if i.val < 29 then #[16,19,53] else #[37,47,17]) else (if i.val < 31 then #[18,49,103] else #[49,18,48]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[51,48,18] else #[52,53,19]) else (if i.val < 35 then #[21,20,57] else #[56,57,20])) else (if i.val < 38 then (if i.val < 37 then #[22,25,66] else #[29,60,23]) else (if i.val < 39 then #[24,62,113] else #[62,24,61]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[64,61,24] else #[65,66,25]) else (if i.val < 43 then #[55,68,26] else #[27,70,81])) else (if i.val < 46 then (if i.val < 45 then #[70,27,69] else #[72,69,27]) else (if i.val < 47 then #[73,74,28] else #[60,29,32])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[76,32,29] else #[31,30,78]) else (if i.val < 51 then #[77,78,30] else #[32,76,118])) else (if i.val < 54 then (if i.val < 53 then #[33,81,70] else #[81,33,75]) else (if i.val < 55 then #[67,75,33] else #[42,83,34]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[35,85,96] else #[85,35,84]) else (if i.val < 59 then #[87,84,35] else #[88,89,36])) else (if i.val < 62 then (if i.val < 61 then #[47,37,40] else #[91,40,37]) else (if i.val < 63 then #[39,38,93] else #[92,93,38])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then #[40,91,122] else #[41,96,85]) else (if i.val < 67 then #[96,41,90] else #[54,90,41])) else (if i.val < 70 then (if i.val < 69 then #[83,42,45] else #[98,45,42]) else (if i.val < 71 then #[44,43,100] else #[99,100,43]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then #[45,98,105] else #[46,103,49]) else (if i.val < 75 then #[103,46,54] else #[90,54,46])) else (if i.val < 78 then (if i.val < 77 then #[48,51,102] else #[50,106,126]) else (if i.val < 79 then #[106,50,104] else #[94,104,50])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then #[95,102,51] else #[53,52,101]) else (if i.val < 83 then #[97,101,52] else #[68,55,58])) else (if i.val < 86 then (if i.val < 85 then #[108,58,55] else #[57,56,110]) else (if i.val < 87 then #[109,110,56] else #[58,108,115]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then #[59,113,62] else #[113,59,67]) else (if i.val < 91 then #[75,67,59] else #[61,64,112])) else (if i.val < 94 then (if i.val < 93 then #[63,116,127] else #[116,63,114]) else (if i.val < 95 then #[79,114,63] else #[80,112,64]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then #[66,65,111] else #[82,111,65]) else (if i.val < 99 then #[69,72,80] else #[71,119,121])) else (if i.val < 102 then (if i.val < 101 then #[119,71,82] else #[111,82,71]) else (if i.val < 103 then #[112,80,72] else #[74,73,79]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then #[114,79,73] else #[121,118,76]) else (if i.val < 107 then #[78,77,120] else #[117,120,77])) else (if i.val < 110 then (if i.val < 109 then #[84,87,95] else #[86,123,125]) else (if i.val < 111 then #[123,86,97] else #[101,97,86])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then #[102,95,87] else #[89,88,94]) else (if i.val < 115 then #[104,94,88] else #[125,122,91])) else (if i.val < 118 then (if i.val < 117 then #[93,92,124] else #[107,124,92]) else (if i.val < 119 then #[126,105,98] else #[100,99,107]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then #[124,107,99] else #[105,126,106]) else (if i.val < 123 then #[127,115,108] else #[110,109,117])) else (if i.val < 126 then (if i.val < 125 then #[120,117,109] else #[115,127,116]) else (if i.val < 127 then #[118,121,119] else #[122,125,123]))))))) : Array (Fin 128))[j.val]!
private def quotientParents (i : Fin 128) : Fin 128 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 5 else 5) else (if i.val < 15 then 6 else 6)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 7) else (if i.val < 19 then 7 else 9)) else (if i.val < 22 then (if i.val < 21 then 10 else 10) else (if i.val < 23 then 10 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 11 else 13) else (if i.val < 27 then 14 else 14)) else (if i.val < 30 then (if i.val < 29 then 16 else 17) else (if i.val < 31 then 18 else 18))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 18 else 19) else (if i.val < 35 then 20 else 20)) else (if i.val < 38 then (if i.val < 37 then 22 else 23) else (if i.val < 39 then 24 else 24))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 24 else 25) else (if i.val < 43 then 26 else 27)) else (if i.val < 46 then (if i.val < 45 then 27 else 27) else (if i.val < 47 then 28 else 29)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 29 else 30) else (if i.val < 51 then 30 else 32)) else (if i.val < 54 then (if i.val < 53 then 33 else 33) else (if i.val < 55 then 33 else 34))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 35 else 35) else (if i.val < 59 then 35 else 36)) else (if i.val < 62 then (if i.val < 61 then 37 else 37) else (if i.val < 63 then 38 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 40 else 41) else (if i.val < 67 then 41 else 41)) else (if i.val < 70 then (if i.val < 69 then 42 else 42) else (if i.val < 71 then 43 else 43))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 45 else 46) else (if i.val < 75 then 46 else 46)) else (if i.val < 78 then (if i.val < 77 then 48 else 50) else (if i.val < 79 then 50 else 50)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 51 else 52) else (if i.val < 83 then 52 else 55)) else (if i.val < 86 then (if i.val < 85 then 55 else 56) else (if i.val < 87 then 56 else 58))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 59 else 59) else (if i.val < 91 then 59 else 61)) else (if i.val < 94 then (if i.val < 93 then 63 else 63) else (if i.val < 95 then 63 else 64))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 65 else 65) else (if i.val < 99 then 69 else 71)) else (if i.val < 102 then (if i.val < 101 then 71 else 71) else (if i.val < 103 then 72 else 73))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 73 else 76) else (if i.val < 107 then 77 else 77)) else (if i.val < 110 then (if i.val < 109 then 84 else 86) else (if i.val < 111 then 86 else 86)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 87 else 88) else (if i.val < 115 then 88 else 91)) else (if i.val < 118 then (if i.val < 117 then 92 else 92) else (if i.val < 119 then 98 else 99))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 99 else 105) else (if i.val < 123 then 108 else 109)) else (if i.val < 126 then (if i.val < 125 then 109 else 115) else (if i.val < 127 then 118 else 122))))))) : Fin 128)
private def quotientLetters (i : Fin 128) : Fin 3 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 0 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 1) else (if i.val < 19 then 2 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 1) else (if i.val < 23 then 2 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 0) else (if i.val < 27 then 1 else 2)) else (if i.val < 30 then (if i.val < 29 then 0 else 2) else (if i.val < 31 then 0 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 2 else 2) else (if i.val < 35 then 1 else 2)) else (if i.val < 38 then (if i.val < 37 then 0 else 2) else (if i.val < 39 then 0 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 2 else 2) else (if i.val < 43 then 2 else 0)) else (if i.val < 46 then (if i.val < 45 then 1 else 2) else (if i.val < 47 then 2 else 1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 2 else 1) else (if i.val < 51 then 2 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 1) else (if i.val < 55 then 2 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 1) else (if i.val < 59 then 2 else 2)) else (if i.val < 62 then (if i.val < 61 then 1 else 2) else (if i.val < 63 then 1 else 2)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 0 else 0) else (if i.val < 67 then 1 else 2)) else (if i.val < 70 then (if i.val < 69 then 1 else 2) else (if i.val < 71 then 1 else 2))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 0 else 0) else (if i.val < 75 then 1 else 2)) else (if i.val < 78 then (if i.val < 77 then 0 else 0) else (if i.val < 79 then 1 else 2)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 2 else 1) else (if i.val < 83 then 2 else 1)) else (if i.val < 86 then (if i.val < 85 then 2 else 1) else (if i.val < 87 then 2 else 0))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 0 else 1) else (if i.val < 91 then 2 else 0)) else (if i.val < 94 then (if i.val < 93 then 0 else 1) else (if i.val < 95 then 2 else 2))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 1 else 2) else (if i.val < 99 then 0 else 0)) else (if i.val < 102 then (if i.val < 101 then 1 else 2) else (if i.val < 103 then 2 else 1))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 2 else 2) else (if i.val < 107 then 1 else 2)) else (if i.val < 110 then (if i.val < 109 then 0 else 0) else (if i.val < 111 then 1 else 2)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 2 else 1) else (if i.val < 115 then 2 else 2)) else (if i.val < 118 then (if i.val < 117 then 1 else 2) else (if i.val < 119 then 2 else 1))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 2 else 0) else (if i.val < 123 then 2 else 1)) else (if i.val < 126 then (if i.val < 125 then 2 else 0) else (if i.val < 127 then 0 else 0))))))) : Fin 3)
private def stepWitness (i : Fin 128) (j : Fin 3) : Fin 1 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,0,0] else #[0,0,0]) else (if i.val < 3 then #[0,0,0] else #[0,0,0])) else (if i.val < 6 then (if i.val < 5 then #[0,0,0] else #[0,0,0]) else (if i.val < 7 then #[0,0,0] else #[0,0,0]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,0,0] else #[0,0,0]) else (if i.val < 11 then #[0,0,0] else #[0,0,0])) else (if i.val < 14 then (if i.val < 13 then #[0,0,0] else #[0,0,0]) else (if i.val < 15 then #[0,0,0] else #[0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[0,0,0] else #[0,0,0]) else (if i.val < 19 then #[0,0,0] else #[0,0,0])) else (if i.val < 22 then (if i.val < 21 then #[0,0,0] else #[0,0,0]) else (if i.val < 23 then #[0,0,0] else #[0,0,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[0,0,0] else #[0,0,0]) else (if i.val < 27 then #[0,0,0] else #[0,0,0])) else (if i.val < 30 then (if i.val < 29 then #[0,0,0] else #[0,0,0]) else (if i.val < 31 then #[0,0,0] else #[0,0,0]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,0,0] else #[0,0,0]) else (if i.val < 35 then #[0,0,0] else #[0,0,0])) else (if i.val < 38 then (if i.val < 37 then #[0,0,0] else #[0,0,0]) else (if i.val < 39 then #[0,0,0] else #[0,0,0]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[0,0,0] else #[0,0,0]) else (if i.val < 43 then #[0,0,0] else #[0,0,0])) else (if i.val < 46 then (if i.val < 45 then #[0,0,0] else #[0,0,0]) else (if i.val < 47 then #[0,0,0] else #[0,0,0])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[0,0,0] else #[0,0,0]) else (if i.val < 51 then #[0,0,0] else #[0,0,0])) else (if i.val < 54 then (if i.val < 53 then #[0,0,0] else #[0,0,0]) else (if i.val < 55 then #[0,0,0] else #[0,0,0]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[0,0,0] else #[0,0,0]) else (if i.val < 59 then #[0,0,0] else #[0,0,0])) else (if i.val < 62 then (if i.val < 61 then #[0,0,0] else #[0,0,0]) else (if i.val < 63 then #[0,0,0] else #[0,0,0])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then #[0,0,0] else #[0,0,0]) else (if i.val < 67 then #[0,0,0] else #[0,0,0])) else (if i.val < 70 then (if i.val < 69 then #[0,0,0] else #[0,0,0]) else (if i.val < 71 then #[0,0,0] else #[0,0,0]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then #[0,0,0] else #[0,0,0]) else (if i.val < 75 then #[0,0,0] else #[0,0,0])) else (if i.val < 78 then (if i.val < 77 then #[0,0,0] else #[0,0,0]) else (if i.val < 79 then #[0,0,0] else #[0,0,0])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then #[0,0,0] else #[0,0,0]) else (if i.val < 83 then #[0,0,0] else #[0,0,0])) else (if i.val < 86 then (if i.val < 85 then #[0,0,0] else #[0,0,0]) else (if i.val < 87 then #[0,0,0] else #[0,0,0]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then #[0,0,0] else #[0,0,0]) else (if i.val < 91 then #[0,0,0] else #[0,0,0])) else (if i.val < 94 then (if i.val < 93 then #[0,0,0] else #[0,0,0]) else (if i.val < 95 then #[0,0,0] else #[0,0,0]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then #[0,0,0] else #[0,0,0]) else (if i.val < 99 then #[0,0,0] else #[0,0,0])) else (if i.val < 102 then (if i.val < 101 then #[0,0,0] else #[0,0,0]) else (if i.val < 103 then #[0,0,0] else #[0,0,0]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then #[0,0,0] else #[0,0,0]) else (if i.val < 107 then #[0,0,0] else #[0,0,0])) else (if i.val < 110 then (if i.val < 109 then #[0,0,0] else #[0,0,0]) else (if i.val < 111 then #[0,0,0] else #[0,0,0])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then #[0,0,0] else #[0,0,0]) else (if i.val < 115 then #[0,0,0] else #[0,0,0])) else (if i.val < 118 then (if i.val < 117 then #[0,0,0] else #[0,0,0]) else (if i.val < 119 then #[0,0,0] else #[0,0,0]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then #[0,0,0] else #[0,0,0]) else (if i.val < 123 then #[0,0,0] else #[0,0,0])) else (if i.val < 126 then (if i.val < 125 then #[0,0,0] else #[0,0,0]) else (if i.val < 127 then #[0,0,0] else #[0,0,0]))))))) : Array (Fin 1))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

def cosets : BinaryNormalCosetCertificate generators kernel 128 where
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
  parent_lt := (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))
  parent_next := (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 0
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 128
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

def literalNormalGenerators (k : Fin 0) : Equiv.Perm (Fin 8) :=
  Fin.elim0 k

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 0) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  exact Fin.elim0 k

end N0

namespace N1
def normalGenerators (j : Fin 1) : Source := ⟨(52 : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 2) : Fin 128 := ((if i.val < 1 then 52 else 127) : Fin 128)
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

private def representatives (i : Fin 64) : Source := ⟨((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 71))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 25) else (if i.val < 11 then 47 else 79)) else (if i.val < 14 then (if i.val < 13 then 11 else 27) else (if i.val < 15 then 103 else 42)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 29 else 74) else (if i.val < 19 then 17 else 89)) else (if i.val < 22 then (if i.val < 21 then 111 else 43) else (if i.val < 23 then 31 else 75))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 19 else 91) else (if i.val < 27 then 106 else 21)) else (if i.val < 30 then (if i.val < 29 then 93 else 115) else (if i.val < 31 then 81 else 28))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 40 else 34) else (if i.val < 35 then 107 else 23)) else (if i.val < 38 then (if i.val < 37 then 95 else 51) else (if i.val < 39 then 83 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 41 else 35) else (if i.val < 43 then 119 else 8)) else (if i.val < 46 then (if i.val < 45 then 2 else 126) else (if i.val < 47 then 37 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 125 else 55) else (if i.val < 51 then 9 else 3)) else (if i.val < 54 then (if i.val < 53 then 62 else 45) else (if i.val < 55 then 46 else 61))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 122 else 5) else (if i.val < 59 then 6 else 121)) else (if i.val < 62 then (if i.val < 61 then 58 else 13) else (if i.val < 63 then 14 else 57)))))) : Fin 128)⟩
private def quotientNext (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,8,9])) else (if i.val < 6 then (if i.val < 5 then #[2,1,10] else #[11,12,13]) else (if i.val < 7 then #[14,15,16] else #[3,17,18]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[17,3,2] else #[19,16,15]) else (if i.val < 11 then #[20,21,22] else #[5,23,24])) else (if i.val < 14 then (if i.val < 13 then #[23,5,4] else #[25,22,21]) else (if i.val < 15 then #[6,26,27] else #[26,6,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[28,9,8] else #[8,7,29]) else (if i.val < 19 then #[30,31,32] else #[9,28,33])) else (if i.val < 22 then (if i.val < 21 then #[10,34,35] else #[34,10,1]) else (if i.val < 23 then #[36,13,12] else #[12,11,37]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[38,39,40] else #[13,36,41]) else (if i.val < 27 then #[15,14,42] else #[39,38,43])) else (if i.val < 30 then (if i.val < 29 then #[16,19,44] else #[37,45,46]) else (if i.val < 31 then #[18,35,34] else #[35,18,17]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[41,46,45] else #[40,47,48]) else (if i.val < 35 then #[21,20,49] else #[31,30,50])) else (if i.val < 38 then (if i.val < 37 then #[22,25,51] else #[29,52,53]) else (if i.val < 39 then #[24,27,26] else #[27,24,23]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[33,53,52] else #[32,54,55]) else (if i.val < 43 then #[49,56,57] else #[51,57,56])) else (if i.val < 46 then (if i.val < 45 then #[50,58,59] else #[52,29,7]) else (if i.val < 47 then #[54,32,31] else #[53,33,28])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[55,59,58] else #[42,60,61]) else (if i.val < 51 then #[44,61,60] else #[43,62,63])) else (if i.val < 54 then (if i.val < 53 then #[45,37,11] else #[47,40,39]) else (if i.val < 55 then #[46,41,36] else #[48,63,62]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[60,42,14] else #[62,43,38]) else (if i.val < 59 then #[61,44,19] else #[63,48,47])) else (if i.val < 62 then (if i.val < 61 then #[56,49,20] else #[58,50,30]) else (if i.val < 63 then #[57,51,25] else #[59,55,54])))))) : Array (Fin 64))[j.val]!
private def quotientPrev (i : Fin 64) (j : Fin 3) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,15] else #[0,4,21]) else (if i.val < 3 then #[4,0,8] else #[7,8,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,12] else #[11,12,1]) else (if i.val < 7 then #[14,15,2] else #[3,17,45]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[17,3,16] else #[19,16,3]) else (if i.val < 11 then #[20,21,4] else #[5,23,52])) else (if i.val < 14 then (if i.val < 13 then #[23,5,22] else #[25,22,5]) else (if i.val < 15 then #[6,26,56] else #[26,6,9])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[28,9,6] else #[8,7,31]) else (if i.val < 19 then #[30,31,7] else #[9,28,58])) else (if i.val < 22 then (if i.val < 21 then #[10,34,60] else #[34,10,13]) else (if i.val < 23 then #[36,13,10] else #[12,11,39]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[38,39,11] else #[13,36,62]) else (if i.val < 27 then #[15,14,38] else #[39,38,14])) else (if i.val < 30 then (if i.val < 29 then #[16,19,47] else #[37,45,17]) else (if i.val < 31 then #[18,35,61] else #[35,18,46]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[41,46,18] else #[40,47,19]) else (if i.val < 35 then #[21,20,30] else #[31,30,20])) else (if i.val < 38 then (if i.val < 37 then #[22,25,54] else #[29,52,23]) else (if i.val < 39 then #[24,27,57] else #[27,24,53]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[33,53,24] else #[32,54,25]) else (if i.val < 43 then #[49,56,26] else #[51,57,27])) else (if i.val < 46 then (if i.val < 45 then #[50,58,28] else #[52,29,32]) else (if i.val < 47 then #[54,32,29] else #[53,33,59])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[55,59,33] else #[42,60,34]) else (if i.val < 51 then #[44,61,35] else #[43,62,36])) else (if i.val < 54 then (if i.val < 53 then #[45,37,40] else #[47,40,37]) else (if i.val < 55 then #[46,41,63] else #[48,63,41]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[60,42,43] else #[62,43,42]) else (if i.val < 59 then #[61,44,48] else #[63,48,44])) else (if i.val < 62 then (if i.val < 61 then #[56,49,50] else #[58,50,49]) else (if i.val < 63 then #[57,51,55] else #[59,55,51])))))) : Array (Fin 64))[j.val]!
private def quotientParents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 5 else 5) else (if i.val < 15 then 6 else 6)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 7) else (if i.val < 19 then 7 else 9)) else (if i.val < 22 then (if i.val < 21 then 10 else 10) else (if i.val < 23 then 10 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 11 else 13) else (if i.val < 27 then 14 else 14)) else (if i.val < 30 then (if i.val < 29 then 16 else 17) else (if i.val < 31 then 18 else 18))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 18 else 19) else (if i.val < 35 then 20 else 20)) else (if i.val < 38 then (if i.val < 37 then 22 else 23) else (if i.val < 39 then 24 else 24))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 24 else 25) else (if i.val < 43 then 26 else 27)) else (if i.val < 46 then (if i.val < 45 then 28 else 29) else (if i.val < 47 then 29 else 33)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 33 else 34) else (if i.val < 51 then 35 else 36)) else (if i.val < 54 then (if i.val < 53 then 37 else 37) else (if i.val < 55 then 41 else 41))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 42 else 42) else (if i.val < 59 then 44 else 44)) else (if i.val < 62 then (if i.val < 61 then 49 else 49) else (if i.val < 63 then 51 else 51)))))) : Fin 64)
private def quotientLetters (i : Fin 64) : Fin 3 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 0 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 1) else (if i.val < 19 then 2 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 1) else (if i.val < 23 then 2 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 0) else (if i.val < 27 then 1 else 2)) else (if i.val < 30 then (if i.val < 29 then 0 else 2) else (if i.val < 31 then 0 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 2 else 2) else (if i.val < 35 then 1 else 2)) else (if i.val < 38 then (if i.val < 37 then 0 else 2) else (if i.val < 39 then 0 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 2 else 2) else (if i.val < 43 then 2 else 2)) else (if i.val < 46 then (if i.val < 45 then 2 else 1) else (if i.val < 47 then 2 else 1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 2 else 2) else (if i.val < 51 then 2 else 2)) else (if i.val < 54 then (if i.val < 53 then 1 else 2) else (if i.val < 55 then 1 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 1 else 2) else (if i.val < 59 then 1 else 2)) else (if i.val < 62 then (if i.val < 61 then 1 else 2) else (if i.val < 63 then 1 else 2)))))) : Fin 3)
private def stepWitness (i : Fin 64) (j : Fin 3) : Fin 2 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,1,1] else #[1,1,1]) else (if i.val < 3 then #[1,1,1] else #[1,1,1])) else (if i.val < 6 then (if i.val < 5 then #[1,1,1] else #[1,1,1]) else (if i.val < 7 then #[1,1,1] else #[1,1,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[1,1,1] else #[1,1,1]) else (if i.val < 11 then #[1,1,1] else #[1,1,1])) else (if i.val < 14 then (if i.val < 13 then #[1,1,1] else #[1,1,1]) else (if i.val < 15 then #[1,1,1] else #[1,1,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[1,1,1] else #[1,1,1]) else (if i.val < 19 then #[1,1,1] else #[1,1,1])) else (if i.val < 22 then (if i.val < 21 then #[1,1,1] else #[1,1,1]) else (if i.val < 23 then #[1,1,1] else #[1,1,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[1,1,1] else #[1,1,1]) else (if i.val < 27 then #[1,1,1] else #[0,0,1])) else (if i.val < 30 then (if i.val < 29 then #[1,1,1] else #[1,1,1]) else (if i.val < 31 then #[1,0,0] else #[0,1,1]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,1,1] else #[0,1,1]) else (if i.val < 35 then #[1,1,1] else #[0,0,1])) else (if i.val < 38 then (if i.val < 37 then #[1,1,1] else #[1,1,1]) else (if i.val < 39 then #[1,0,0] else #[0,1,1]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[0,1,1] else #[0,1,1]) else (if i.val < 43 then #[1,1,1] else #[0,1,1])) else (if i.val < 46 then (if i.val < 45 then #[0,1,1] else #[1,1,1]) else (if i.val < 47 then #[0,1,1] else #[0,1,1])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[1,1,1] else #[1,1,1]) else (if i.val < 51 then #[0,1,1] else #[0,1,1])) else (if i.val < 54 then (if i.val < 53 then #[1,1,1] else #[0,1,1]) else (if i.val < 55 then #[0,1,1] else #[1,1,1]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[1,1,1] else #[0,1,0]) else (if i.val < 59 then #[0,1,1] else #[1,1,1])) else (if i.val < 62 then (if i.val < 61 then #[1,1,1] else #[0,1,0]) else (if i.val < 63 then #[0,1,1] else #[1,1,1])))))) : Array (Fin 2))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

def cosets : BinaryNormalCosetCertificate generators kernel 64 where
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
  parent_lt := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
  parent_next := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 1
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 64
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 1) : Equiv.Perm (Fin 8) :=
  literalGenerator0

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 1) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N1

namespace N2
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 61 else 118) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 4) : Fin 128 := ((if i.val < 2 then (if i.val < 1 then 52 else 61) else (if i.val < 3 then 118 else 127)) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[1,2] else (if i.val < 2 then #[1,2] else #[2,1])) : Array (Fin 4))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 4 := ((if i.val < 1 then #[1,2] else (if i.val < 2 then #[1,2] else #[2,1])) : Array (Fin 4))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 32) : Source := ⟨((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 71))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 25) else (if i.val < 11 then 47 else 79)) else (if i.val < 14 then (if i.val < 13 then 11 else 27) else (if i.val < 15 then 103 else 42)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 29 else 74) else (if i.val < 19 then 17 else 111)) else (if i.val < 22 then (if i.val < 21 then 43 else 31) else (if i.val < 23 then 75 else 19))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 106 else 21) else (if i.val < 27 then 115 else 107)) else (if i.val < 30 then (if i.val < 29 then 23 else 51) else (if i.val < 31 then 119 else 55))))) : Fin 128)⟩
private def quotientNext (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,8,9])) else (if i.val < 6 then (if i.val < 5 then #[2,1,10] else #[11,12,13]) else (if i.val < 7 then #[14,15,16] else #[3,17,18]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[17,3,2] else #[13,16,15]) else (if i.val < 11 then #[19,20,21] else #[5,22,23])) else (if i.val < 14 then (if i.val < 13 then #[22,5,4] else #[9,21,20]) else (if i.val < 15 then #[6,24,25] else #[24,6,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,9,8] else #[8,7,26]) else (if i.val < 19 then #[23,25,24] else #[10,27,28])) else (if i.val < 22 then (if i.val < 21 then #[27,10,1] else #[16,13,12]) else (if i.val < 23 then #[12,11,29] else #[18,28,27]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,14,30] else #[28,18,17]) else (if i.val < 27 then #[29,30,14] else #[20,19,31])) else (if i.val < 30 then (if i.val < 29 then #[25,23,22] else #[26,31,19]) else (if i.val < 31 then #[31,26,7] else #[30,29,11]))))) : Array (Fin 32))[j.val]!
private def quotientPrev (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,15] else #[0,4,20]) else (if i.val < 3 then #[4,0,8] else #[7,8,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,12] else #[11,12,1]) else (if i.val < 7 then #[14,15,2] else #[3,17,30]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[17,3,16] else #[13,16,3]) else (if i.val < 11 then #[19,20,4] else #[5,22,31])) else (if i.val < 14 then (if i.val < 13 then #[22,5,21] else #[9,21,5]) else (if i.val < 15 then #[6,24,26] else #[24,6,9])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,9,6] else #[8,7,25]) else (if i.val < 19 then #[23,25,7] else #[10,27,29])) else (if i.val < 22 then (if i.val < 21 then #[27,10,13] else #[16,13,10]) else (if i.val < 23 then #[12,11,28] else #[18,28,11]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,14,18] else #[28,18,14]) else (if i.val < 27 then #[29,30,17] else #[20,19,23])) else (if i.val < 30 then (if i.val < 29 then #[25,23,19] else #[26,31,22]) else (if i.val < 31 then #[31,26,24] else #[30,29,27]))))) : Array (Fin 32))[j.val]!
private def quotientParents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 5 else 5) else (if i.val < 15 then 6 else 6)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 7) else (if i.val < 19 then 7 else 10)) else (if i.val < 22 then (if i.val < 21 then 10 else 10) else (if i.val < 23 then 11 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 14 else 14) else (if i.val < 27 then 17 else 19)) else (if i.val < 30 then (if i.val < 29 then 19 else 22) else (if i.val < 31 then 24 else 27))))) : Fin 32)
private def quotientLetters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 0 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 1) else (if i.val < 19 then 2 else 0)) else (if i.val < 22 then (if i.val < 21 then 1 else 2) else (if i.val < 23 then 1 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 2) else (if i.val < 27 then 2 else 1)) else (if i.val < 30 then (if i.val < 29 then 2 else 2) else (if i.val < 31 then 2 else 2))))) : Fin 3)
private def stepWitness (i : Fin 32) (j : Fin 3) : Fin 4 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,3,3] else #[3,3,3]) else (if i.val < 3 then #[3,3,3] else #[3,3,3])) else (if i.val < 6 then (if i.val < 5 then #[3,3,3] else #[3,3,3]) else (if i.val < 7 then #[3,3,3] else #[3,3,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,3,3] else #[1,3,3]) else (if i.val < 11 then #[3,3,3] else #[3,3,3])) else (if i.val < 14 then (if i.val < 13 then #[3,3,3] else #[1,3,3]) else (if i.val < 15 then #[3,3,3] else #[3,3,3])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[1,3,3] else #[3,3,3]) else (if i.val < 19 then #[1,2,2] else #[3,3,3])) else (if i.val < 22 then (if i.val < 21 then #[3,3,3] else #[1,3,3]) else (if i.val < 23 then #[3,3,3] else #[1,2,2]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[3,3,3] else #[1,2,2]) else (if i.val < 27 then #[3,2,2] else #[3,3,3])) else (if i.val < 30 then (if i.val < 29 then #[1,2,2] else #[3,2,2]) else (if i.val < 31 then #[3,2,2] else #[3,2,2]))))) : Array (Fin 4))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

def cosets : BinaryNormalCosetCertificate generators kernel 32 where
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
  parent_lt := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  parent_next := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

@[reducible] def state : BinaryNormalState generators where
  kernel := kernel
  normal := normal
  generatorCount := 2
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 32
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N2

namespace N3
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 81 else (if j.val < 2 then 61 else 118)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 128 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 19 else 26) else (if i.val < 3 then 52 else 61)) else (if i.val < 6 then (if i.val < 5 then 81 else 88) else (if i.val < 7 then 118 else 127))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[0,3,6] else (if i.val < 2 then #[5,3,6] else #[5,6,3])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[0,3,6] else (if i.val < 2 then #[5,3,6] else #[0,6,3])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 71))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 25) else (if i.val < 11 then 47 else 79)) else (if i.val < 14 then (if i.val < 13 then 11 else 27) else (if i.val < 15 then 29 else 31)))) : Fin 128)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,8,9])) else (if i.val < 6 then (if i.val < 5 then #[2,1,10] else #[11,12,13]) else (if i.val < 7 then #[12,11,14] else #[3,10,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,3,2] else #[13,14,11]) else (if i.val < 11 then #[8,7,15] else #[5,6,0])) else (if i.val < 14 then (if i.val < 13 then #[6,5,4] else #[9,15,7]) else (if i.val < 15 then #[15,9,8] else #[14,13,12])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,11] else #[0,4,7]) else (if i.val < 3 then #[4,0,8] else #[7,8,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,12] else #[11,12,1]) else (if i.val < 7 then #[12,11,2] else #[3,10,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,3,14] else #[13,14,3]) else (if i.val < 11 then #[8,7,4] else #[5,6,9])) else (if i.val < 14 then (if i.val < 13 then #[6,5,15] else #[9,15,5]) else (if i.val < 15 then #[15,9,6] else #[14,13,10])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 4 else 5)) else (if i.val < 14 then (if i.val < 13 then 5 else 5) else (if i.val < 15 then 6 else 10)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 2 else 2)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 8 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[7,7,7] else #[7,7,7])) else (if i.val < 6 then (if i.val < 5 then #[7,7,7] else #[7,7,7]) else (if i.val < 7 then #[0,0,7] else #[7,1,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[1,7,7] else #[3,7,0]) else (if i.val < 11 then #[4,4,7] else #[7,5,5])) else (if i.val < 14 then (if i.val < 13 then #[5,7,7] else #[3,7,4]) else (if i.val < 15 then #[3,7,7] else #[3,7,7])))) : Array (Fin 8))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 16 where
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N3

namespace N4
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 55 else (if j.val < 2 then 61 else 118)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 128 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 52 else 55) else (if i.val < 3 then 61 else 62)) else (if i.val < 6 then (if i.val < 5 then 117 else 118) else (if i.val < 7 then 124 else 127))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[1,2,5] else (if i.val < 2 then #[3,2,5] else #[3,5,2])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[1,2,5] else (if i.val < 2 then #[3,2,5] else #[4,5,2])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 25 else 47) else (if i.val < 11 then 11 else 27)) else (if i.val < 14 then (if i.val < 13 then 42 else 29) else (if i.val < 15 then 43 else 31)))) : Fin 128)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,7,8])) else (if i.val < 6 then (if i.val < 5 then #[2,1,9] else #[3,10,11]) else (if i.val < 7 then #[9,12,13] else #[10,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,13,12] else #[6,14,15]) else (if i.val < 11 then #[7,5,4] else #[8,15,14])) else (if i.val < 14 then (if i.val < 13 then #[14,6,0] else #[15,8,7]) else (if i.val < 15 then #[12,9,1] else #[13,11,10])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,12] else #[0,4,14]) else (if i.val < 3 then #[4,0,7] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,10] else #[3,10,1]) else (if i.val < 7 then #[9,12,2] else #[10,3,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,13,3] else #[6,14,4]) else (if i.val < 11 then #[7,5,15] else #[8,15,5])) else (if i.val < 14 then (if i.val < 13 then #[14,6,8] else #[15,8,6]) else (if i.val < 15 then #[12,9,11] else #[13,11,9])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 4) else (if i.val < 11 then 5 else 5)) else (if i.val < 14 then (if i.val < 13 then 6 else 6) else (if i.val < 15 then 9 else 9)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 1 else 2)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 8 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[7,7,7] else #[3,7,7])) else (if i.val < 6 then (if i.val < 5 then #[7,7,7] else #[3,7,7]) else (if i.val < 7 then #[1,7,7] else #[3,7,7]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,7,7] else #[1,7,7]) else (if i.val < 11 then #[3,7,7] else #[2,7,7])) else (if i.val < 14 then (if i.val < 13 then #[1,7,7] else #[2,7,7]) else (if i.val < 15 then #[1,7,7] else #[2,7,7])))) : Array (Fin 8))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 16 where
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
  quotientCount := 16
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N4

namespace N5
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 81 else 61) else (if j.val < 3 then 121 else 118)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 128 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 19 else 21) else (if i.val < 3 then 26 else 28)) else (if i.val < 6 then (if i.val < 5 then 50 else 52) else (if i.val < 7 then 59 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 81 else 87) else (if i.val < 11 then 88 else 94)) else (if i.val < 14 then (if i.val < 13 then 112 else 118) else (if i.val < 15 then 121 else 127)))) : Fin 128)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[13,8,3,2] else #[4,9,2,3]) else (if i.val < 3 then #[15,10,1,0] else #[6,11,0,1])) else (if i.val < 6 then (if i.val < 5 then #[11,12,5,6] else #[2,13,4,7]) else (if i.val < 7 then #[9,14,7,4] else #[0,15,6,5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[5,0,11,10] else #[12,1,10,11]) else (if i.val < 11 then #[7,2,9,8] else #[14,3,8,9])) else (if i.val < 14 then (if i.val < 13 then #[3,4,13,14] else #[10,5,12,15]) else (if i.val < 15 then #[1,6,15,12] else #[8,7,14,13])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 6 else 10) else (if i.val < 3 then 12 else 14)) else (if i.val < 6 then (if i.val < 5 then 13 else 5) else (if i.val < 7 then 9 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 15) else (if i.val < 11 then 8 else 7)) else (if i.val < 14 then (if i.val < 13 then 11 else 4) else (if i.val < 15 then 3 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 14) else (if i.val < 3 then 5 else 0)) else (if i.val < 6 then (if i.val < 5 then 5 else 8) else (if i.val < 7 then 7 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 11) else (if i.val < 11 then 8 else 8)) else (if i.val < 14 then (if i.val < 13 then 14 else 15) else (if i.val < 15 then 15 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 0 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 2 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 3) else (if i.val < 11 then 3 else 2)) else (if i.val < 14 then (if i.val < 13 then 3 else 3) else (if i.val < 15 then 2 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[0,7,14,13] else (if i.val < 2 then #[10,7,14,13] else #[10,13,1,7])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[0,7,14,13] else (if i.val < 2 then #[10,7,14,13] else #[0,13,3,7])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 7 else 15)) else (if i.val < 6 then (if i.val < 5 then 71 else 25) else (if i.val < 7 then 79 else 27))) : Fin 128)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,1,2] else #[0,0,3]) else (if i.val < 3 then #[4,4,5] else #[6,6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,2,1] else #[7,7,6]) else (if i.val < 7 then #[3,3,0] else #[5,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,1,6] else #[0,0,4]) else (if i.val < 3 then #[4,4,0] else #[6,6,1])) else (if i.val < 6 then (if i.val < 5 then #[2,2,7] else #[7,7,2]) else (if i.val < 7 then #[3,3,5] else #[5,5,3]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 3 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 0 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 16 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[15,6,15] else #[15,6,15]) else (if i.val < 3 then #[15,3,15] else #[15,11,15])) else (if i.val < 6 then (if i.val < 5 then #[15,3,2] else #[7,6,0]) else (if i.val < 7 then #[15,11,10] else #[7,6,8]))) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
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
  toFun x := (#[2,5,0,3,6,1,4,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,5,0,3,6,1,4,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N5

namespace N6
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 31 else (if j.val < 2 then 81 else 118)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 128 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 19 else 22) else (if i.val < 3 then 26 else 31)) else (if i.val < 6 then (if i.val < 5 then 49 else 52) else (if i.val < 7 then 56 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 81 else 84) else (if i.val < 11 then 88 else 93)) else (if i.val < 14 then (if i.val < 13 then 115 else 118) else (if i.val < 15 then 122 else 127)))) : Fin 128)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,13,2] else #[5,14,3]) else (if i.val < 3 then #[6,15,0] else #[7,12,1])) else (if i.val < 6 then (if i.val < 5 then #[8,1,6] else #[9,2,7]) else (if i.val < 7 then #[10,3,4] else #[11,0,5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,5,10] else #[13,6,11]) else (if i.val < 11 then #[14,7,8] else #[15,4,9])) else (if i.val < 14 then (if i.val < 13 then #[0,9,14] else #[1,10,15]) else (if i.val < 15 then #[2,11,12] else #[3,8,13])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 6) else (if i.val < 3 then 13 else 1)) else (if i.val < 6 then (if i.val < 5 then 14 else 7) else (if i.val < 7 then 15 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 11) else (if i.val < 11 then 8 else 9)) else (if i.val < 14 then (if i.val < 13 then 5 else 3) else (if i.val < 15 then 12 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 3) else (if i.val < 3 then 5 else 15)) else (if i.val < 6 then (if i.val < 5 then 11 else 8) else (if i.val < 7 then 9 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 12) else (if i.val < 11 then 8 else 7)) else (if i.val < 14 then (if i.val < 13 then 3 else 15) else (if i.val < 15 then 12 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 2 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[11,0,13] else (if i.val < 2 then #[3,10,13] else #[12,10,7])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[11,0,13] else (if i.val < 2 then #[3,10,13] else #[14,0,7])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 47))) : Fin 128)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[6,5,4])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[7,3,2]) else (if i.val < 7 then #[3,7,1] else #[5,6,0]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,7] else #[0,4,6]) else (if i.val < 3 then #[4,0,5] else #[6,5,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,3] else #[7,3,1]) else (if i.val < 7 then #[3,7,2] else #[5,6,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 4))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 16 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[15,15,15] else #[15,15,15]) else (if i.val < 3 then #[15,15,15] else #[14,3,3])) else (if i.val < 6 then (if i.val < 5 then #[15,15,15] else #[14,11,11]) else (if i.val < 7 then #[12,3,3] else #[12,11,11]))) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
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
  quotientCount := 8
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,2,5,4,7,6,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,2,1,4,3,6,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N6

namespace N7
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 89 else (if j.val < 2 then 55 else 118)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 128 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 17 else 18) else (if i.val < 3 then 24 else 27)) else (if i.val < 6 then (if i.val < 5 then 52 else 55) else (if i.val < 7 then 61 else 62))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 80 else 83) else (if i.val < 11 then 89 else 90)) else (if i.val < 14 then (if i.val < 13 then 117 else 118) else (if i.val < 15 then 124 else 127)))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[3,5,13] else (if i.val < 2 then #[10,7,13] else #[2,7,6])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[3,5,13] else (if i.val < 2 then #[10,7,13] else #[0,12,6])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 10))) : Fin 128)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,7,1])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,6,0]) else (if i.val < 7 then #[7,5,4] else #[6,3,2]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,5] else #[0,4,3]) else (if i.val < 3 then #[4,0,7] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,6] else #[3,6,1]) else (if i.val < 7 then #[7,5,2] else #[6,3,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 1))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 16 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[15,15,15] else #[15,15,15]) else (if i.val < 3 then #[15,15,15] else #[7,15,3])) else (if i.val < 6 then (if i.val < 5 then #[15,15,10] else #[7,10,10]) else (if i.val < 7 then #[0,3,3] else #[2,15,15]))) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
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
  quotientCount := 8
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N7

namespace N8
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 63 else 55) else (if j.val < 3 then 61 else 118)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 128 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 52 else 53) else (if i.val < 3 then 54 else 55)) else (if i.val < 6 then (if i.val < 5 then 60 else 61) else (if i.val < 7 then 62 else 63))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 116 else 117) else (if i.val < 11 then 118 else 119)) else (if i.val < 14 then (if i.val < 13 then 124 else 125) else (if i.val < 15 then 126 else 127)))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[7,3,5,10] else (if i.val < 2 then #[7,6,5,10] else #[14,6,10,5])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[7,3,5,10] else (if i.val < 2 then #[7,6,5,10] else #[11,9,10,5])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 123) else (if i.val < 3 then 7 else 39)) else (if i.val < 6 then (if i.val < 5 then 10 else 25) else (if i.val < 7 then 42 else 29))) : Fin 128)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,4,5] else #[3,6,7])) else (if i.val < 6 then (if i.val < 5 then #[4,2,1] else #[5,7,6]) else (if i.val < 7 then #[6,3,0] else #[7,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[0,1,6] else #[1,0,4]) else (if i.val < 3 then #[2,4,0] else #[3,6,1])) else (if i.val < 6 then (if i.val < 5 then #[4,2,7] else #[5,7,2]) else (if i.val < 7 then #[6,3,5] else #[7,5,3]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 3 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 1 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 16 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,15,15] else #[7,15,15]) else (if i.val < 3 then #[14,15,15] else #[11,15,15])) else (if i.val < 6 then (if i.val < 5 then #[14,15,15] else #[13,15,15]) else (if i.val < 7 then #[11,15,15] else #[13,15,15]))) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
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
  quotientCount := 8
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N8

namespace N9
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 61 else (if j.val < 2 then 25 else 52)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 8) : Fin 128 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 25) else (if i.val < 3 then 52 else 61)) else (if i.val < 6 then (if i.val < 5 then 82 else 91) else (if i.val < 7 then 118 else 127))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[3,5,2] else (if i.val < 2 then #[3,1,2] else #[6,1,2])) : Array (Fin 8))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 8 := ((if i.val < 1 then #[3,5,2] else (if i.val < 2 then #[3,1,2] else #[6,1,2])) : Array (Fin 8))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 16) : Source := ⟨((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 71))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 47 else 79) else (if i.val < 11 then 103 else 17)) else (if i.val < 14 then (if i.val < 13 then 111 else 19) else (if i.val < 15 then 21 else 23)))) : Fin 128)⟩
private def quotientNext (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,8] else #[9,8,1]) else (if i.val < 7 then #[10,3,2] else #[3,10,11]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,5,4] else #[5,12,13]) else (if i.val < 11 then #[6,7,14] else #[13,14,7])) else (if i.val < 14 then (if i.val < 13 then #[8,9,15] else #[11,15,9]) else (if i.val < 15 then #[15,11,10] else #[14,13,12])))) : Array (Fin 16))[j.val]!
private def quotientPrev (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,8] else #[9,8,1]) else (if i.val < 7 then #[10,3,2] else #[3,10,11]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,5,4] else #[5,12,13]) else (if i.val < 11 then #[6,7,14] else #[13,14,7])) else (if i.val < 14 then (if i.val < 13 then #[8,9,15] else #[11,15,9]) else (if i.val < 15 then #[15,11,10] else #[14,13,12])))) : Array (Fin 16))[j.val]!
private def quotientParents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 5) else (if i.val < 11 then 6 else 7)) else (if i.val < 14 then (if i.val < 13 then 8 else 9) else (if i.val < 15 then 10 else 12)))) : Fin 16)
private def quotientLetters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 0) else (if i.val < 11 then 0 else 2)) else (if i.val < 14 then (if i.val < 13 then 0 else 2) else (if i.val < 15 then 2 else 2)))) : Fin 3)
private def stepWitness (i : Fin 16) (j : Fin 3) : Fin 8 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[7,7,7] else #[7,7,7]) else (if i.val < 3 then #[7,7,7] else #[7,1,1])) else (if i.val < 6 then (if i.val < 5 then #[7,7,7] else #[7,5,5]) else (if i.val < 7 then #[7,1,1] else #[7,1,7]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[7,5,5] else #[7,5,7]) else (if i.val < 11 then #[7,1,7] else #[3,6,0])) else (if i.val < 14 then (if i.val < 13 then #[7,5,7] else #[3,6,4]) else (if i.val < 15 then #[3,6,0] else #[3,6,4])))) : Array (Fin 8))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 16 where
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N9

namespace N10
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 23 else (if j.val < 2 then 25 else 52)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 128 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 23) else (if i.val < 3 then 25 else 30)) else (if i.val < 6 then (if i.val < 5 then 51 else 52) else (if i.val < 7 then 58 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 82 else 85) else (if i.val < 11 then 91 else 92)) else (if i.val < 14 then (if i.val < 13 then 113 else 118) else (if i.val < 15 then 120 else 127)))) : Fin 128)
private def next (i : Fin 16) (j : Fin 3) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[14,13,10] else #[7,6,11]) else (if i.val < 3 then #[12,15,8] else #[5,4,9])) else (if i.val < 6 then (if i.val < 5 then #[2,3,14] else #[11,8,15]) else (if i.val < 7 then #[0,1,12] else #[9,10,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[6,5,2] else #[15,14,3]) else (if i.val < 11 then #[4,7,0] else #[13,12,1])) else (if i.val < 14 then (if i.val < 13 then #[10,11,6] else #[3,0,7]) else (if i.val < 15 then #[8,9,4] else #[1,2,5])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 12 else 1) else (if i.val < 3 then 2 else 14)) else (if i.val < 6 then (if i.val < 5 then 15 else 3) else (if i.val < 7 then 5 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 6)) else (if i.val < 14 then (if i.val < 13 then 7 else 11) else (if i.val < 15 then 13 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 6 else 15) else (if i.val < 3 then 15 else 9)) else (if i.val < 6 then (if i.val < 5 then 10 else 15) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 7) else (if i.val < 11 then 7 else 1)) else (if i.val < 14 then (if i.val < 13 then 2 else 7) else (if i.val < 15 then 9 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 3 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 1 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 0) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 0 else 2) else (if i.val < 15 then 1 else 0)))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[9,10,5] else (if i.val < 2 then #[3,2,5] else #[4,2,5])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[9,10,5] else (if i.val < 2 then #[3,2,5] else #[14,2,5])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 71))) : Fin 128)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[6,7,1]) else (if i.val < 7 then #[5,3,2] else #[3,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[7,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[6,7,1]) else (if i.val < 7 then #[5,3,2] else #[3,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 3))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 0))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 16 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[15,15,15] else #[15,15,15]) else (if i.val < 3 then #[15,15,15] else #[15,2,2])) else (if i.val < 6 then (if i.val < 5 then #[15,15,4] else #[6,11,10]) else (if i.val < 7 then #[4,2,2] else #[15,3,3]))) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
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
  quotientCount := 8
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,6,5,4,7,2,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,6,1,4,3,2,5] : Array (Fin 8))[x.val]!
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N10

namespace N11
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 61 else 29) else (if j.val < 3 then 25 else 52)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 128 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 20) else (if i.val < 3 then 25 else 29)) else (if i.val < 6 then (if i.val < 5 then 48 else 52) else (if i.val < 7 then 57 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 82 else 86) else (if i.val < 11 then 91 else 95)) else (if i.val < 14 then (if i.val < 13 then 114 else 118) else (if i.val < 15 then 123 else 127)))) : Fin 128)
private def next (i : Fin 16) (j : Fin 4) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[8,12,13,10] else #[9,13,12,11]) else (if i.val < 3 then #[10,14,15,8] else #[11,15,14,9])) else (if i.val < 6 then (if i.val < 5 then #[12,8,9,14] else #[13,9,8,15]) else (if i.val < 7 then #[14,10,11,12] else #[15,11,10,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,4,5,2] else #[1,5,4,3]) else (if i.val < 11 then #[2,6,7,0] else #[3,7,6,1])) else (if i.val < 14 then (if i.val < 13 then #[4,0,1,6] else #[5,1,0,7]) else (if i.val < 15 then #[6,2,3,4] else #[7,3,2,5])))) : Array (Fin 16))[j.val]!
private def rank (i : Fin 16) : ℕ := (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 12) else (if i.val < 3 then 3 else 2)) else (if i.val < 6 then (if i.val < 5 then 14 else 4) else (if i.val < 7 then 11 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 9) else (if i.val < 11 then 6 else 5)) else (if i.val < 14 then (if i.val < 13 then 15 else 7) else (if i.val < 15 then 8 else 0))))
private def parents (i : Fin 16) : Fin 16 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 11) else (if i.val < 3 then 15 else 15)) else (if i.val < 6 then (if i.val < 5 then 14 else 15) else (if i.val < 7 then 11 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 3) else (if i.val < 11 then 7 else 7)) else (if i.val < 14 then (if i.val < 13 then 6 else 7) else (if i.val < 15 then 3 else 15)))) : Fin 16)
private def letters (i : Fin 16) : Fin 4 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 2 else 1)) else (if i.val < 6 then (if i.val < 5 then 3 else 3) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 2 else 1)) else (if i.val < 14 then (if i.val < 13 then 3 else 3) else (if i.val < 15 then 2 else 0)))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[7,11,10,5] else (if i.val < 2 then #[7,3,2,5] else #[13,14,2,5])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 16 := ((if i.val < 1 then #[7,11,10,5] else (if i.val < 2 then #[7,3,2,5] else #[13,14,2,5])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 7 else 15)) else (if i.val < 6 then (if i.val < 5 then 71 else 79) else (if i.val < 7 then 17 else 19))) : Fin 128)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[4,2,0] else #[5,3,1])) else (if i.val < 6 then (if i.val < 5 then #[2,4,6] else #[3,5,7]) else (if i.val < 7 then #[7,6,4] else #[6,7,5]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[4,2,0] else #[5,3,1])) else (if i.val < 6 then (if i.val < 5 then #[2,4,6] else #[3,5,7]) else (if i.val < 7 then #[7,6,4] else #[6,7,5]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 3) else (if i.val < 7 then 4 else 5))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 2 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 16 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[15,14,15] else #[15,14,15]) else (if i.val < 3 then #[15,3,2] else #[15,11,10])) else (if i.val < 6 then (if i.val < 5 then #[15,3,15] else #[15,11,15]) else (if i.val < 7 then #[7,12,0] else #[7,12,8]))) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
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
  toFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N11

namespace N12
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 81 else (if j.val < 2 then 61 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 16) : Fin 128 := ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 19) else (if i.val < 3 then 25 else 26)) else (if i.val < 6 then (if i.val < 5 then 52 else 55) else (if i.val < 7 then 61 else 62))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 81 else 82) else (if i.val < 11 then 88 else 91)) else (if i.val < 14 then (if i.val < 13 then 117 else 118) else (if i.val < 15 then 124 else 127)))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[1,6,11] else (if i.val < 2 then #[10,6,2] else #[10,13,2])) : Array (Fin 16))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 16 := ((if i.val < 1 then #[1,6,11] else (if i.val < 2 then #[10,6,2] else #[1,13,2])) : Array (Fin 16))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 8) : Source := ⟨((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) else (if i.val < 6 then (if i.val < 5 then 59 else 15) else (if i.val < 7 then 39 else 47))) : Fin 128)⟩
private def quotientNext (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientPrev (i : Fin 8) (j : Fin 3) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,4,5]) else (if i.val < 3 then #[4,0,6] else #[5,6,0])) else (if i.val < 6 then (if i.val < 5 then #[2,1,7] else #[3,7,1]) else (if i.val < 7 then #[7,3,2] else #[6,5,4]))) : Array (Fin 8))[j.val]!
private def quotientParents (i : Fin 8) : Fin 8 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 4))) : Fin 8)
private def quotientLetters (i : Fin 8) : Fin 3 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 2 else 2))) : Fin 3)
private def stepWitness (i : Fin 8) (j : Fin 3) : Fin 16 := ((if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[15,15,15] else #[15,15,15]) else (if i.val < 3 then #[15,15,15] else #[7,2,2])) else (if i.val < 6 then (if i.val < 5 then #[15,15,15] else #[7,11,11]) else (if i.val < 7 then #[5,2,2] else #[5,11,11]))) : Array (Fin 16))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 8 where
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
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N12

namespace N13
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 37 else 81) else (if j.val < 3 then 61 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 128 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 8 else 11)) else (if i.val < 6 then (if i.val < 5 then 16 else 19) else (if i.val < 7 then 25 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 37 else 38) else (if i.val < 11 then 44 else 47)) else (if i.val < 14 then (if i.val < 13 then 52 else 55) else (if i.val < 15 then 61 else 62)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 64 else 67) else (if i.val < 19 then 73 else 74)) else (if i.val < 22 then (if i.val < 21 then 81 else 82) else (if i.val < 23 then 88 else 91))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 100 else 103) else (if i.val < 27 then 109 else 110)) else (if i.val < 30 then (if i.val < 29 then 117 else 118) else (if i.val < 31 then 124 else 127))))) : Fin 128)
private def next (i : Fin 32) (j : Fin 4) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[22,9,17,27] else #[23,27,16,9]) else (if i.val < 3 then #[7,11,19,25] else #[6,25,18,11])) else (if i.val < 6 then (if i.val < 5 then #[19,15,21,29] else #[18,29,20,15]) else (if i.val < 7 then #[2,13,23,31] else #[3,31,22,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[30,1,25,19] else #[31,19,24,1]) else (if i.val < 11 then #[15,3,27,17] else #[14,17,26,3])) else (if i.val < 14 then (if i.val < 13 then #[27,7,29,21] else #[26,21,28,7]) else (if i.val < 15 then #[10,5,31,23] else #[11,23,30,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,10,1,24] else #[20,24,0,10]) else (if i.val < 19 then #[4,8,3,26] else #[5,26,2,8])) else (if i.val < 22 then (if i.val < 21 then #[16,12,5,30] else #[17,30,4,12]) else (if i.val < 23 then #[1,14,7,28] else #[0,28,6,14]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,2,9,16] else #[28,16,8,2]) else (if i.val < 27 then #[12,0,11,18] else #[13,18,10,0])) else (if i.val < 30 then (if i.val < 29 then #[24,4,13,22] else #[25,22,12,4]) else (if i.val < 31 then #[9,6,15,20] else #[8,20,14,6]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 28 else 6) else (if i.val < 3 then 14 else 26)) else (if i.val < 6 then (if i.val < 5 then 30 else 11) else (if i.val < 7 then 4 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 16) else (if i.val < 11 then 12 else 29)) else (if i.val < 14 then (if i.val < 13 then 10 else 15) else (if i.val < 15 then 3 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 27) else (if i.val < 19 then 25 else 8)) else (if i.val < 22 then (if i.val < 21 then 2 else 21) else (if i.val < 23 then 31 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 7) else (if i.val < 27 then 20 else 18)) else (if i.val < 30 then (if i.val < 29 then 19 else 24) else (if i.val < 31 then 5 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 23 else 8) else (if i.val < 3 then 6 else 10)) else (if i.val < 6 then (if i.val < 5 then 28 else 20) else (if i.val < 7 then 31 else 12))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 31 else 30) else (if i.val < 11 then 14 else 2)) else (if i.val < 14 then (if i.val < 13 then 20 else 6) else (if i.val < 15 then 31 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 20 else 10) else (if i.val < 19 then 5 else 8)) else (if i.val < 22 then (if i.val < 21 then 31 else 16) else (if i.val < 23 then 28 else 14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 16 else 8) else (if i.val < 27 then 19 else 1)) else (if i.val < 30 then (if i.val < 29 then 25 else 12) else (if i.val < 31 then 8 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 4 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 2) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 2 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 3) else (if i.val < 19 then 0 else 3)) else (if i.val < 22 then (if i.val < 21 then 1 else 0) else (if i.val < 23 then 3 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 2) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 0 else 2) else (if i.val < 31 then 0 else 0))))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[26,5,14,23] else (if i.val < 2 then #[2,22,14,6] else #[1,22,29,6])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[26,5,14,23] else (if i.val < 2 then #[2,22,14,6] else #[3,5,29,6])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 7)) : Fin 128)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,3,2]) else (if i.val < 3 then #[3,0,1] else #[2,1,0])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[0,3,2]) else (if i.val < 3 then #[3,0,1] else #[2,1,0])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[31,31,31] else #[31,19,19]) else (if i.val < 3 then #[19,31,11] else #[3,3,6])) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
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
  quotientCount := 4
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,4,7,6,5,0,3,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,0,7,6,1,4,3,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N13

namespace N14
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 31 else (if j.val < 2 then 81 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 128 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 19) else (if i.val < 3 then 21 else 22)) else (if i.val < 6 then (if i.val < 5 then 25 else 26) else (if i.val < 7 then 28 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 50) else (if i.val < 11 then 52 else 55)) else (if i.val < 14 then (if i.val < 13 then 56 else 59) else (if i.val < 15 then 61 else 62)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 81 else 82) else (if i.val < 19 then 84 else 87)) else (if i.val < 22 then (if i.val < 21 then 88 else 91) else (if i.val < 23 then 93 else 94))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 112 else 115) else (if i.val < 27 then 117 else 118)) else (if i.val < 30 then (if i.val < 29 then 121 else 122) else (if i.val < 31 then 124 else 127))))) : Fin 128)
private def next (i : Fin 32) (j : Fin 3) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[24,15,27] else #[8,27,15]) else (if i.val < 3 then #[26,9,29] else #[10,29,9])) else (if i.val < 6 then (if i.val < 5 then #[28,11,31] else #[12,31,11]) else (if i.val < 7 then #[30,13,25] else #[14,25,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[16,3,23] else #[0,23,3]) else (if i.val < 11 then #[18,5,17] else #[2,17,5])) else (if i.val < 14 then (if i.val < 13 then #[20,7,19] else #[4,19,7]) else (if i.val < 15 then #[22,1,21] else #[6,21,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[25,10,30] else #[9,30,10]) else (if i.val < 19 then #[27,12,24] else #[11,24,12])) else (if i.val < 22 then (if i.val < 21 then #[29,14,26] else #[13,26,14]) else (if i.val < 23 then #[31,8,28] else #[15,28,8]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[17,6,18] else #[1,18,6]) else (if i.val < 27 then #[19,0,20] else #[3,20,0])) else (if i.val < 30 then (if i.val < 29 then #[21,2,22] else #[5,22,2]) else (if i.val < 31 then #[23,4,16] else #[7,16,4]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 12) else (if i.val < 3 then 20 else 29)) else (if i.val < 6 then (if i.val < 5 then 3 else 17) else (if i.val < 7 then 15 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 27) else (if i.val < 11 then 7 else 10)) else (if i.val < 14 then (if i.val < 13 then 25 else 6) else (if i.val < 15 then 4 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 18) else (if i.val < 19 then 14 else 16)) else (if i.val < 22 then (if i.val < 21 then 30 else 13) else (if i.val < 23 then 11 else 19))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 26 else 5) else (if i.val < 27 then 24 else 22)) else (if i.val < 30 then (if i.val < 29 then 9 else 28) else (if i.val < 31 then 8 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 27 else 14) else (if i.val < 3 then 28 else 8)) else (if i.val < 6 then (if i.val < 5 then 31 else 10) else (if i.val < 7 then 25 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 17) else (if i.val < 11 then 16 else 4)) else (if i.val < 14 then (if i.val < 13 then 18 else 7) else (if i.val < 15 then 7 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 31 else 10) else (if i.val < 19 then 25 else 13)) else (if i.val < 22 then (if i.val < 21 then 27 else 14) else (if i.val < 23 then 14 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 18 else 7) else (if i.val < 27 then 21 else 1)) else (if i.val < 30 then (if i.val < 29 then 4 else 2) else (if i.val < 31 then 16 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 3 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 1) else (if i.val < 7 then 2 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 0 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 2) else (if i.val < 19 then 1 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 2) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 1) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 0 else 2) else (if i.val < 31 then 2 else 0))))) : Fin 3)

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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[22,1,21] else (if i.val < 2 then #[7,20,4] else #[25,20,4])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[22,1,21] else (if i.val < 2 then #[7,20,4] else #[29,1,4])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 7 else 15)) : Fin 128)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,1,2] else #[0,0,3]) else (if i.val < 3 then #[3,3,0] else #[2,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,1,2] else #[0,0,3]) else (if i.val < 3 then #[3,3,0] else #[2,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[31,13,31] else #[31,13,31]) else (if i.val < 3 then #[15,7,4] else #[15,22,21])) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
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
  quotientCount := 4
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,2,5,4,7,6,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,2,1,4,3,6,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N14

namespace N15
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 81 else 61) else (if j.val < 3 then 39 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 128 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 9 else 10)) else (if i.val < 6 then (if i.val < 5 then 16 else 19) else (if i.val < 7 then 25 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 36 else 39) else (if i.val < 11 then 45 else 46)) else (if i.val < 14 then (if i.val < 13 then 52 else 55) else (if i.val < 15 then 61 else 62)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 65 else 66) else (if i.val < 19 then 72 else 75)) else (if i.val < 22 then (if i.val < 21 then 81 else 82) else (if i.val < 23 then 88 else 91))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 101 else 102) else (if i.val < 27 then 108 else 111)) else (if i.val < 30 then (if i.val < 29 then 117 else 118) else (if i.val < 31 then 124 else 127))))) : Fin 128)
private def next (i : Fin 32) (j : Fin 4) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[11,17,22,25] else #[25,16,23,11]) else (if i.val < 3 then #[9,19,7,27] else #[27,18,6,9])) else (if i.val < 6 then (if i.val < 5 then #[15,21,18,29] else #[29,20,19,15]) else (if i.val < 7 then #[13,23,3,31] else #[31,22,2,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[3,25,30,17] else #[17,24,31,3]) else (if i.val < 11 then #[1,27,15,19] else #[19,26,14,1])) else (if i.val < 14 then (if i.val < 13 then #[7,29,26,21] else #[21,28,27,7]) else (if i.val < 15 then #[5,31,11,23] else #[23,30,10,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[8,1,21,26] else #[26,0,20,8]) else (if i.val < 19 then #[10,3,4,24] else #[24,2,5,10])) else (if i.val < 22 then (if i.val < 21 then #[12,5,17,30] else #[30,4,16,12]) else (if i.val < 23 then #[14,7,0,28] else #[28,6,1,14]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[0,9,29,18] else #[18,8,28,0]) else (if i.val < 27 then #[2,11,12,16] else #[16,10,13,2])) else (if i.val < 30 then (if i.val < 29 then #[4,13,25,22] else #[22,12,24,4]) else (if i.val < 31 then #[6,15,8,20] else #[20,14,9,6]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 20 else 22) else (if i.val < 3 then 27 else 12)) else (if i.val < 6 then (if i.val < 5 then 28 else 6) else (if i.val < 7 then 4 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 3) else (if i.val < 11 then 30 else 9)) else (if i.val < 14 then (if i.val < 13 then 5 else 13) else (if i.val < 15 then 2 else 19)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 29 else 7) else (if i.val < 19 then 24 else 18)) else (if i.val < 22 then (if i.val < 21 then 1 else 17) else (if i.val < 23 then 26 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 11 else 31) else (if i.val < 27 then 16 else 25)) else (if i.val < 30 then (if i.val < 29 then 23 else 15) else (if i.val < 31 then 8 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 17 else 11) else (if i.val < 3 then 7 else 9)) else (if i.val < 6 then (if i.val < 5 then 29 else 20) else (if i.val < 7 then 31 else 12))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 31) else (if i.val < 11 then 19 else 14)) else (if i.val < 14 then (if i.val < 13 then 20 else 6) else (if i.val < 15 then 31 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 20) else (if i.val < 19 then 24 else 5)) else (if i.val < 22 then (if i.val < 21 then 31 else 12) else (if i.val < 23 then 7 else 14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 9 else 0) else (if i.val < 27 then 12 else 3)) else (if i.val < 30 then (if i.val < 29 then 23 else 12) else (if i.val < 31 then 20 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 4 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 1) else (if i.val < 7 then 3 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 2) else (if i.val < 11 then 3 else 2)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 1 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 2) else (if i.val < 19 then 3 else 2)) else (if i.val < 22 then (if i.val < 21 then 0 else 3) else (if i.val < 23 then 1 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 3) else (if i.val < 27 then 2 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 1) else (if i.val < 31 then 3 else 0))))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[5,14,27,23] else (if i.val < 2 then #[22,14,3,6] else #[22,29,3,6])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[5,14,27,23] else (if i.val < 2 then #[22,14,3,6] else #[5,29,3,6])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 59)) : Fin 128)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,2] else #[0,3,3]) else (if i.val < 3 then #[3,0,0] else #[2,1,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,2] else #[0,3,3]) else (if i.val < 3 then #[3,0,0] else #[2,1,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[31,31,3] else #[31,31,19]) else (if i.val < 3 then #[31,31,9] else #[31,31,27])) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
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
  toFun x := (#[1,0,7,6,5,4,3,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,0,7,6,5,4,3,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N15

namespace N16
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 81 else 61) else (if j.val < 3 then 29 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 128 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 19) else (if i.val < 3 then 20 else 23)) else (if i.val < 6 then (if i.val < 5 then 25 else 26) else (if i.val < 7 then 29 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 48 else 51) else (if i.val < 11 then 52 else 55)) else (if i.val < 14 then (if i.val < 13 then 57 else 58) else (if i.val < 15 then 61 else 62)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 81 else 82) else (if i.val < 19 then 85 else 86)) else (if i.val < 22 then (if i.val < 21 then 88 else 91) else (if i.val < 23 then 92 else 95))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 113 else 114) else (if i.val < 27 then 117 else 118)) else (if i.val < 30 then (if i.val < 29 then 120 else 123) else (if i.val < 31 then 124 else 127))))) : Fin 128)
private def next (i : Fin 32) (j : Fin 4) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[15,17,25,27] else #[27,16,9,15]) else (if i.val < 3 then #[13,19,27,25] else #[25,18,11,13])) else (if i.val < 6 then (if i.val < 5 then #[11,21,29,31] else #[31,20,13,11]) else (if i.val < 7 then #[9,23,31,29] else #[29,22,15,9]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[7,25,17,19] else #[19,24,1,7]) else (if i.val < 11 then #[5,27,19,17] else #[17,26,3,5])) else (if i.val < 14 then (if i.val < 13 then #[3,29,21,23] else #[23,28,5,3]) else (if i.val < 15 then #[1,31,23,21] else #[21,30,7,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[10,1,24,30] else #[30,0,8,10]) else (if i.val < 19 then #[8,3,26,28] else #[28,2,10,8])) else (if i.val < 22 then (if i.val < 21 then #[14,5,28,26] else #[26,4,12,14]) else (if i.val < 23 then #[12,7,30,24] else #[24,6,14,12]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[2,9,16,22] else #[22,8,0,2]) else (if i.val < 27 then #[0,11,18,20] else #[20,10,2,0])) else (if i.val < 30 then (if i.val < 29 then #[6,13,20,18] else #[18,12,4,6]) else (if i.val < 31 then #[4,15,22,16] else #[16,14,6,4]))))) : Array (Fin 32))[j.val]!
private def rank (i : Fin 32) : ℕ := (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 28 else 6) else (if i.val < 3 then 19 else 25)) else (if i.val < 6 then (if i.val < 5 then 4 else 14) else (if i.val < 7 then 3 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 30 else 11) else (if i.val < 11 then 5 else 13)) else (if i.val < 14 then (if i.val < 13 then 21 else 27) else (if i.val < 15 then 2 else 18)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 17) else (if i.val < 19 then 24 else 16)) else (if i.val < 22 then (if i.val < 21 then 26 else 10) else (if i.val < 23 then 20 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 7 else 31) else (if i.val < 27 then 22 else 15)) else (if i.val < 30 then (if i.val < 29 then 29 else 12) else (if i.val < 31 then 8 else 0)))))
private def parents (i : Fin 32) : Fin 32 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 27 else 16) else (if i.val < 3 then 24 else 11)) else (if i.val < 6 then (if i.val < 5 then 31 else 10) else (if i.val < 7 then 31 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 19 else 6) else (if i.val < 11 then 16 else 4)) else (if i.val < 14 then (if i.val < 13 then 23 else 5) else (if i.val < 15 then 31 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 31 else 10) else (if i.val < 19 then 29 else 10)) else (if i.val < 22 then (if i.val < 21 then 5 else 14) else (if i.val < 23 then 24 else 14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 16 else 2) else (if i.val < 27 then 21 else 10)) else (if i.val < 30 then (if i.val < 29 then 19 else 6) else (if i.val < 31 then 16 else 31))))) : Fin 32)
private def letters (i : Fin 32) : Fin 4 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 1) else (if i.val < 3 then 0 else 2)) else (if i.val < 6 then (if i.val < 5 then 3 else 0) else (if i.val < 7 then 2 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 3 else 2) else (if i.val < 15 then 1 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 3) else (if i.val < 19 then 0 else 2)) else (if i.val < 22 then (if i.val < 21 then 1 else 3) else (if i.val < 23 then 3 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 3) else (if i.val < 27 then 0 else 1)) else (if i.val < 30 then (if i.val < 29 then 0 else 3) else (if i.val < 31 then 3 else 0))))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[1,14,23,21] else (if i.val < 2 then #[20,14,6,4] else #[20,27,29,4])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[1,14,23,21] else (if i.val < 2 then #[20,14,6,4] else #[1,27,29,4])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 7 else 15)) : Fin 128)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[3,2,0] else #[2,3,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,0,2] else #[0,1,3]) else (if i.val < 3 then #[3,2,0] else #[2,3,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[31,29,31] else #[31,29,31]) else (if i.val < 3 then #[15,6,4] else #[15,23,21])) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
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
  toFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N16

namespace N17
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 71 else (if j.val < 2 then 61 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 128 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 6) else (if i.val < 3 then 12 else 15)) else (if i.val < 6 then (if i.val < 5 then 16 else 19) else (if i.val < 7 then 25 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 33 else 34) else (if i.val < 11 then 40 else 43)) else (if i.val < 14 then (if i.val < 13 then 52 else 55) else (if i.val < 15 then 61 else 62)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 68 else 71) else (if i.val < 19 then 77 else 78)) else (if i.val < 22 then (if i.val < 21 then 81 else 82) else (if i.val < 23 then 88 else 91))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 96 else 99) else (if i.val < 27 then 105 else 106)) else (if i.val < 30 then (if i.val < 29 then 117 else 118) else (if i.val < 31 then 124 else 127))))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[3,14,23] else (if i.val < 2 then #[27,14,6] else #[1,29,6])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 32 := ((if i.val < 1 then #[3,14,23] else (if i.val < 2 then #[27,14,6] else #[3,29,6])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 59)) : Fin 128)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,1] else #[0,3,0]) else (if i.val < 3 then #[3,0,3] else #[2,1,2])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,1] else #[0,3,0]) else (if i.val < 3 then #[3,0,3] else #[2,1,2])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[31,31,11] else #[31,31,27]) else (if i.val < 3 then #[31,31,3] else #[31,31,17])) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N17

namespace N18
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 81 else 63) else (if j.val < 3 then 61 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 128 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 17) else (if i.val < 3 then 18 else 19)) else (if i.val < 6 then (if i.val < 5 then 24 else 25) else (if i.val < 7 then 26 else 27))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 52 else 53) else (if i.val < 11 then 54 else 55)) else (if i.val < 14 then (if i.val < 13 then 60 else 61) else (if i.val < 15 then 62 else 63)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 80 else 81) else (if i.val < 19 then 82 else 83)) else (if i.val < 22 then (if i.val < 21 then 88 else 89) else (if i.val < 23 then 90 else 91))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 116 else 117) else (if i.val < 27 then 118 else 119)) else (if i.val < 30 then (if i.val < 29 then 124 else 125) else (if i.val < 31 then 126 else 127))))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[3,15,13,23] else (if i.val < 2 then #[20,15,13,5] else #[20,30,26,5])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[3,15,13,23] else (if i.val < 2 then #[20,15,13,5] else #[3,27,26,5])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 127 else 123) else (if i.val < 3 then 7 else 39)) : Fin 128)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,3,0] else #[3,2,1])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[0,1,2] else #[1,0,3]) else (if i.val < 3 then #[2,3,0] else #[3,2,1])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 2)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[15,31,31] else #[15,31,31]) else (if i.val < 3 then #[30,5,5] else #[27,5,5])) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N18

namespace N19
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 71 else 61) else (if j.val < 3 then 39 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 128 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 12 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 25 else 26) else (if i.val < 15 then 28 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 34) else (if i.val < 19 then 36 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 43) else (if i.val < 23 then 45 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 50) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 56 else 59) else (if i.val < 31 then 61 else 62))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 65 else 66) else (if i.val < 35 then 68 else 71)) else (if i.val < 38 then (if i.val < 37 then 72 else 75) else (if i.val < 39 then 77 else 78))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 81 else 82) else (if i.val < 43 then 84 else 87)) else (if i.val < 46 then (if i.val < 45 then 88 else 91) else (if i.val < 47 then 93 else 94)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 96 else 99) else (if i.val < 51 then 101 else 102)) else (if i.val < 54 then (if i.val < 53 then 105 else 106) else (if i.val < 55 then 108 else 111))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 112 else 115) else (if i.val < 59 then 117 else 118)) else (if i.val < 62 then (if i.val < 61 then 121 else 122) else (if i.val < 63 then 124 else 127)))))) : Fin 128)
private def next (i : Fin 64) (j : Fin 4) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[28,33,44,51] else #[60,32,45,23]) else (if i.val < 3 then #[44,35,61,53] else #[12,34,60,17])) else (if i.val < 6 then (if i.val < 5 then #[61,37,13,55] else #[29,36,12,19]) else (if i.val < 7 then #[13,39,28,49] else #[45,38,29,21]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[20,41,36,59] else #[52,40,37,31]) else (if i.val < 11 then #[36,43,53,61] else #[4,42,52,25])) else (if i.val < 14 then (if i.val < 13 then #[53,45,5,63] else #[21,44,4,27]) else (if i.val < 15 then #[5,47,20,57] else #[37,46,21,29])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[62,49,47,39] else #[30,48,46,3]) else (if i.val < 19 then #[14,51,62,33] else #[46,50,63,5])) else (if i.val < 22 then (if i.val < 21 then #[31,53,14,35] else #[63,52,15,7]) else (if i.val < 23 then #[47,55,31,37] else #[15,54,30,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[54,57,39,47] else #[22,56,38,11]) else (if i.val < 27 then #[6,59,54,41] else #[38,58,55,13])) else (if i.val < 30 then (if i.val < 29 then #[23,61,6,43] else #[55,60,7,15]) else (if i.val < 31 then #[39,63,23,45] else #[7,62,22,9]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[56,1,41,54] else #[24,0,40,18]) else (if i.val < 35 then #[8,3,56,48] else #[40,2,57,20])) else (if i.val < 38 then (if i.val < 37 then #[25,5,8,50] else #[57,4,9,22]) else (if i.val < 39 then #[41,7,25,52] else #[9,6,24,16]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[48,9,33,62] else #[16,8,32,26]) else (if i.val < 43 then #[0,11,48,56] else #[32,10,49,28])) else (if i.val < 46 then (if i.val < 45 then #[17,13,0,58] else #[49,12,1,30]) else (if i.val < 47 then #[33,15,17,60] else #[1,14,16,24])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[26,17,42,34] else #[58,16,43,6]) else (if i.val < 51 then #[42,19,59,36] else #[10,18,58,0])) else (if i.val < 54 then (if i.val < 53 then #[59,21,11,38] else #[27,20,10,2]) else (if i.val < 55 then #[11,23,26,32] else #[43,22,27,4]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[18,25,34,42] else #[50,24,35,14]) else (if i.val < 59 then #[34,27,51,44] else #[2,26,50,8])) else (if i.val < 62 then (if i.val < 61 then #[51,29,3,46] else #[19,28,2,10]) else (if i.val < 63 then #[3,31,18,40] else #[35,30,19,12])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 43 else 29) else (if i.val < 3 then 6 else 45)) else (if i.val < 6 then (if i.val < 5 then 63 else 14) else (if i.val < 7 then 25 else 50))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 58 else 17) else (if i.val < 11 then 38 else 53)) else (if i.val < 14 then (if i.val < 13 then 4 else 46) else (if i.val < 15 then 23 else 27)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 31) else (if i.val < 19 then 44 else 3)) else (if i.val < 22 then (if i.val < 21 then 8 else 52) else (if i.val < 23 then 51 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 59) else (if i.val < 27 then 39 else 37)) else (if i.val < 30 then (if i.val < 29 then 48 else 36) else (if i.val < 31 then 2 else 24))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 54 else 18) else (if i.val < 35 then 40 else 1)) else (if i.val < 38 then (if i.val < 37 then 35 else 42) else (if i.val < 39 then 61 else 9))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 5 else 62) else (if i.val < 43 then 33 else 55)) else (if i.val < 46 then (if i.val < 45 then 20 else 11) else (if i.val < 47 then 12 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 30) else (if i.val < 51 then 13 else 56)) else (if i.val < 54 then (if i.val < 53 then 41 else 15) else (if i.val < 55 then 28 else 60))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 7) else (if i.val < 59 then 47 else 34)) else (if i.val < 62 then (if i.val < 61 then 32 else 21) else (if i.val < 63 then 19 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 33 else 23) else (if i.val < 3 then 35 else 62)) else (if i.val < 6 then (if i.val < 5 then 37 else 19) else (if i.val < 7 then 39 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 59 else 40) else (if i.val < 11 then 53 else 54)) else (if i.val < 14 then (if i.val < 13 then 63 else 44) else (if i.val < 15 then 57 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 39 else 46) else (if i.val < 19 then 33 else 63)) else (if i.val < 22 then (if i.val < 21 then 35 else 15) else (if i.val < 23 then 31 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 36) else (if i.val < 27 then 48 else 53)) else (if i.val < 30 then (if i.val < 29 then 61 else 5) else (if i.val < 31 then 63 else 20))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 54 else 40) else (if i.val < 35 then 48 else 63)) else (if i.val < 38 then (if i.val < 37 then 50 else 9) else (if i.val < 39 then 27 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 35 else 26) else (if i.val < 43 then 50 else 49)) else (if i.val < 46 then (if i.val < 45 then 2 else 30) else (if i.val < 47 then 19 else 24)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 40 else 45) else (if i.val < 51 then 19 else 60)) else (if i.val < 54 then (if i.val < 53 then 9 else 12) else (if i.val < 55 then 23 else 29))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 42 else 35) else (if i.val < 59 then 44 else 50)) else (if i.val < 62 then (if i.val < 61 then 46 else 2) else (if i.val < 63 then 40 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 4 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 3) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 3) else (if i.val < 7 then 1 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 1) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 3 else 1) else (if i.val < 15 then 3 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 2) else (if i.val < 19 then 3 else 2)) else (if i.val < 22 then (if i.val < 21 then 3 else 2) else (if i.val < 23 then 2 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 1 else 0) else (if i.val < 31 then 1 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 3 else 2) else (if i.val < 35 then 3 else 0)) else (if i.val < 38 then (if i.val < 37 then 3 else 2) else (if i.val < 39 then 0 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 3) else (if i.val < 43 then 0 else 2)) else (if i.val < 46 then (if i.val < 45 then 0 else 3) else (if i.val < 47 then 0 else 3)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 1 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 1 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 3 else 2) else (if i.val < 59 then 3 else 2)) else (if i.val < 62 then (if i.val < 61 then 3 else 2) else (if i.val < 63 then 3 else 0)))))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 64 := ((if i.val < 1 then #[7,30,55,45] else (if i.val < 2 then #[53,30,5,12] else #[3,59,5,12])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 64 := ((if i.val < 1 then #[7,30,55,45] else (if i.val < 2 then #[53,30,5,12] else #[7,59,5,12])) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 127 else 63) : Fin 128)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,1] else #[0,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,1] else #[0,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[63,29,21] else #[63,29,53]) : Array (Fin 64))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
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
  generatorCount := 4
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
  toFun x := (#[1,0,7,6,5,4,3,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,0,7,6,5,4,3,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N19

namespace N20
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 81 else 63) else (if j.val < 3 then 61 else (if j.val < 4 then 39 else 25))) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 128 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 8 else 9) else (if i.val < 7 then 10 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 17) else (if i.val < 11 then 18 else 19)) else (if i.val < 14 then (if i.val < 13 then 24 else 25) else (if i.val < 15 then 26 else 27)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 36 else 37) else (if i.val < 19 then 38 else 39)) else (if i.val < 22 then (if i.val < 21 then 44 else 45) else (if i.val < 23 then 46 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 52 else 53) else (if i.val < 27 then 54 else 55)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 64 else 65) else (if i.val < 35 then 66 else 67)) else (if i.val < 38 then (if i.val < 37 then 72 else 73) else (if i.val < 39 then 74 else 75))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 80 else 81) else (if i.val < 43 then 82 else 83)) else (if i.val < 46 then (if i.val < 45 then 88 else 89) else (if i.val < 47 then 90 else 91)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 100 else 101) else (if i.val < 51 then 102 else 103)) else (if i.val < 54 then (if i.val < 53 then 108 else 109) else (if i.val < 55 then 110 else 111))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 116 else 117) else (if i.val < 59 then 118 else 119)) else (if i.val < 62 then (if i.val < 61 then 124 else 125) else (if i.val < 63 then 126 else 127)))))) : Fin 128)
private def next (i : Fin 64) (j : Fin 5) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[22,32,34,44,50] else #[18,33,35,46,54]) else (if i.val < 3 then #[54,34,32,45,18] else #[50,35,33,47,22])) else (if i.val < 6 then (if i.val < 5 then #[23,36,38,12,51] else #[19,37,39,14,55]) else (if i.val < 7 then #[55,38,36,13,19] else #[51,39,37,15,23]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[30,40,42,36,58] else #[26,41,43,38,62]) else (if i.val < 11 then #[62,42,40,37,26] else #[58,43,41,39,30])) else (if i.val < 14 then (if i.val < 13 then #[31,44,46,4,59] else #[27,45,47,6,63]) else (if i.val < 15 then #[63,46,44,5,27] else #[59,47,45,7,31])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[6,48,50,60,34] else #[2,49,51,62,38]) else (if i.val < 19 then #[38,50,48,61,2] else #[34,51,49,63,6])) else (if i.val < 22 then (if i.val < 21 then #[7,52,54,28,35] else #[3,53,55,30,39]) else (if i.val < 23 then #[39,54,52,29,3] else #[35,55,53,31,7]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[14,56,58,52,42] else #[10,57,59,54,46]) else (if i.val < 27 then #[46,58,56,53,10] else #[42,59,57,55,14])) else (if i.val < 30 then (if i.val < 29 then #[15,60,62,20,43] else #[11,61,63,22,47]) else (if i.val < 31 then #[47,62,60,21,11] else #[43,63,61,23,15]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[20,0,2,40,48] else #[16,1,3,42,52]) else (if i.val < 35 then #[52,2,0,41,16] else #[48,3,1,43,20])) else (if i.val < 38 then (if i.val < 37 then #[21,4,6,8,49] else #[17,5,7,10,53]) else (if i.val < 39 then #[53,6,4,9,17] else #[49,7,5,11,21]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[28,8,10,32,56] else #[24,9,11,34,60]) else (if i.val < 43 then #[60,10,8,33,24] else #[56,11,9,35,28])) else (if i.val < 46 then (if i.val < 45 then #[29,12,14,0,57] else #[25,13,15,2,61]) else (if i.val < 47 then #[61,14,12,1,25] else #[57,15,13,3,29])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[4,16,18,56,32] else #[0,17,19,58,36]) else (if i.val < 51 then #[36,18,16,57,0] else #[32,19,17,59,4])) else (if i.val < 54 then (if i.val < 53 then #[5,20,22,24,33] else #[1,21,23,26,37]) else (if i.val < 55 then #[37,22,20,25,1] else #[33,23,21,27,5]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[12,24,26,48,40] else #[8,25,27,50,44]) else (if i.val < 59 then #[44,26,24,49,8] else #[40,27,25,51,12])) else (if i.val < 62 then (if i.val < 61 then #[13,28,30,16,41] else #[9,29,31,18,45]) else (if i.val < 63 then #[45,30,28,17,9] else #[41,31,29,19,13])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 33 else 62) else (if i.val < 3 then 32 else 43)) else (if i.val < 6 then (if i.val < 5 then 47 else 52) else (if i.val < 7 then 19 else 40))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 56 else 7) else (if i.val < 11 then 59 else 8)) else (if i.val < 14 then (if i.val < 13 then 53 else 5) else (if i.val < 15 then 22 else 14)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 46) else (if i.val < 19 then 37 else 4)) else (if i.val < 22 then (if i.val < 21 then 57 else 60) else (if i.val < 23 then 15 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6 else 49) else (if i.val < 27 then 27 else 20)) else (if i.val < 30 then (if i.val < 29 then 35 else 3) else (if i.val < 31 then 31 else 2))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 45 else 58) else (if i.val < 35 then 9 else 36)) else (if i.val < 38 then (if i.val < 37 then 48 else 63) else (if i.val < 39 then 28 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 55 else 1) else (if i.val < 43 then 26 else 11)) else (if i.val < 46 then (if i.val < 45 then 51 else 21) else (if i.val < 47 then 50 else 16)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 54 else 18) else (if i.val < 51 then 61 else 17)) else (if i.val < 54 then (if i.val < 53 then 25 else 39) else (if i.val < 55 then 42 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 23 else 44) else (if i.val < 59 then 24 else 41)) else (if i.val < 62 then (if i.val < 61 then 10 else 12) else (if i.val < 63 then 29 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 34 else 35) else (if i.val < 3 then 34 else 22)) else (if i.val < 6 then (if i.val < 5 then 51 else 14) else (if i.val < 7 then 19 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 58 else 41) else (if i.val < 11 then 42 else 41)) else (if i.val < 14 then (if i.val < 13 then 56 else 63) else (if i.val < 15 then 24 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 51) else (if i.val < 19 then 61 else 63)) else (if i.val < 22 then (if i.val < 21 then 52 else 39) else (if i.val < 23 then 29 else 31))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 41 else 45) else (if i.val < 27 then 9 else 13)) else (if i.val < 30 then (if i.val < 29 then 60 else 63) else (if i.val < 31 then 11 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 51 else 52) else (if i.val < 35 then 41 else 43)) else (if i.val < 38 then (if i.val < 37 then 49 else 53) else (if i.val < 39 then 9 else 11))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 56 else 63) else (if i.val < 43 then 24 else 31)) else (if i.val < 46 then (if i.val < 45 then 14 else 13) else (if i.val < 47 then 14 else 29)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 56 else 19) else (if i.val < 51 then 0 else 19)) else (if i.val < 54 then (if i.val < 53 then 24 else 23) else (if i.val < 55 then 22 else 23))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 24 else 47) else (if i.val < 59 then 24 else 15)) else (if i.val < 62 then (if i.val < 61 then 41 else 31) else (if i.val < 63 then 9 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 5 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 2) else (if i.val < 3 then 1 else 4)) else (if i.val < 6 then (if i.val < 5 then 4 else 3) else (if i.val < 7 then 4 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 1) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 0 else 4) else (if i.val < 15 then 0 else 4)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 2) else (if i.val < 19 then 3 else 3)) else (if i.val < 22 then (if i.val < 21 then 1 else 4) else (if i.val < 23 then 3 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 1 else 2) else (if i.val < 31 then 4 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 4) else (if i.val < 35 then 3 else 3)) else (if i.val < 38 then (if i.val < 37 then 4 else 4) else (if i.val < 39 then 3 else 3))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 4 else 0) else (if i.val < 43 then 4 else 0)) else (if i.val < 46 then (if i.val < 45 then 2 else 1) else (if i.val < 47 then 1 else 4)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 3 else 2) else (if i.val < 51 then 4 else 1)) else (if i.val < 54 then (if i.val < 53 then 3 else 2) else (if i.val < 55 then 1 else 1))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 1 else 0) else (if i.val < 59 then 2 else 0)) else (if i.val < 62 then (if i.val < 61 then 4 else 2) else (if i.val < 63 then 4 else 0)))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 64 := ((if i.val < 1 then #[11,31,29,55,47] else (if i.val < 2 then #[44,31,29,6,13] else #[44,62,58,6,13])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 64 := ((if i.val < 1 then #[11,31,29,55,47] else (if i.val < 2 then #[44,31,29,6,13] else #[11,59,58,6,13])) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 127 else 123) : Fin 128)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,1] else #[1,0,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,1] else #[1,0,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 1) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[31,63,6] else #[31,63,19]) : Array (Fin 64))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
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
  generatorCount := 5
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
  toFun x := (#[1,0,7,6,5,4,3,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,0,7,6,5,4,3,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator4 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 5) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else (if k.val < 4 then literalGenerator3 else literalGenerator4)))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 5) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N20

namespace N21
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 71 else 61) else (if j.val < 3 then 29 else 25)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 128 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 5 else 6)) else (if i.val < 6 then (if i.val < 5 then 8 else 11) else (if i.val < 7 then 12 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 20 else 23)) else (if i.val < 14 then (if i.val < 13 then 25 else 26) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 34) else (if i.val < 19 then 37 else 38)) else (if i.val < 22 then (if i.val < 21 then 40 else 43) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 51) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 61 else 62))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 64 else 67) else (if i.val < 35 then 68 else 71)) else (if i.val < 38 then (if i.val < 37 then 73 else 74) else (if i.val < 39 then 77 else 78))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 81 else 82) else (if i.val < 43 then 85 else 86)) else (if i.val < 46 then (if i.val < 45 then 88 else 91) else (if i.val < 47 then 92 else 95)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 96 else 99) else (if i.val < 51 then 100 else 103)) else (if i.val < 54 then (if i.val < 53 then 105 else 106) else (if i.val < 55 then 109 else 110))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 113 else 114) else (if i.val < 59 then 117 else 118)) else (if i.val < 62 then (if i.val < 61 then 120 else 123) else (if i.val < 63 then 124 else 127)))))) : Fin 128)
private def next (i : Fin 64) (j : Fin 4) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[60,33,49,55] else #[28,32,17,19]) else (if i.val < 3 then #[44,35,51,53] else #[12,34,19,17])) else (if i.val < 6 then (if i.val < 5 then #[29,37,53,51] else #[61,36,21,23]) else (if i.val < 7 then #[13,39,55,49] else #[45,38,23,21]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[20,41,57,59] else #[52,40,25,31]) else (if i.val < 11 then #[4,43,59,57] else #[36,42,27,29])) else (if i.val < 14 then (if i.val < 13 then #[53,45,61,63] else #[21,44,29,27]) else (if i.val < 15 then #[37,47,63,61] else #[5,46,31,25])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[62,49,33,39] else #[30,48,1,3]) else (if i.val < 19 then #[46,51,35,37] else #[14,50,3,1])) else (if i.val < 22 then (if i.val < 21 then #[31,53,37,35] else #[63,52,5,7]) else (if i.val < 23 then #[15,55,39,33] else #[47,54,7,5]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[22,57,41,43] else #[54,56,9,15]) else (if i.val < 27 then #[6,59,43,41] else #[38,58,11,13])) else (if i.val < 30 then (if i.val < 29 then #[55,61,45,47] else #[23,60,13,11]) else (if i.val < 31 then #[39,63,47,45] else #[7,62,15,9]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[24,1,48,50] else #[56,0,16,22]) else (if i.val < 35 then #[8,3,50,48] else #[40,2,18,20])) else (if i.val < 38 then (if i.val < 37 then #[57,5,52,54] else #[25,4,20,18]) else (if i.val < 39 then #[41,7,54,52] else #[9,6,22,16]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[48,9,56,62] else #[16,8,24,26]) else (if i.val < 43 then #[32,11,58,60] else #[0,10,26,24])) else (if i.val < 46 then (if i.val < 45 then #[17,13,60,58] else #[49,12,28,30]) else (if i.val < 47 then #[1,15,62,56] else #[33,14,30,28])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[26,17,32,34] else #[58,16,0,6]) else (if i.val < 51 then #[10,19,34,32] else #[42,18,2,4])) else (if i.val < 54 then (if i.val < 53 then #[59,21,36,38] else #[27,20,4,2]) else (if i.val < 55 then #[43,23,38,36] else #[11,22,6,0]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[50,25,40,46] else #[18,24,8,10]) else (if i.val < 59 then #[34,27,42,44] else #[2,26,10,8])) else (if i.val < 62 then (if i.val < 61 then #[19,29,44,42] else #[51,28,12,14]) else (if i.val < 63 then #[3,31,46,40] else #[35,30,14,12])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 47 else 43) else (if i.val < 3 then 6 else 38)) else (if i.val < 6 then (if i.val < 5 then 30 else 61) else (if i.val < 7 then 23 else 45))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 56 else 16) else (if i.val < 11 then 59 else 51)) else (if i.val < 14 then (if i.val < 13 then 4 else 39) else (if i.val < 15 then 3 else 44)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 25 else 33) else (if i.val < 19 then 7 else 60)) else (if i.val < 22 then (if i.val < 21 then 8 else 57) else (if i.val < 23 then 24 else 62))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 55 else 29) else (if i.val < 27 then 32 else 31)) else (if i.val < 30 then (if i.val < 29 then 27 else 49) else (if i.val < 31 then 2 else 22))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 34 else 26) else (if i.val < 35 then 35 else 1)) else (if i.val < 38 then (if i.val < 37 then 58 else 12) else (if i.val < 39 then 50 else 9))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 5 else 54) else (if i.val < 43 then 42 else 53)) else (if i.val < 46 then (if i.val < 45 then 19 else 11) else (if i.val < 47 then 21 else 10)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 15 else 28) else (if i.val < 51 then 37 else 20)) else (if i.val < 54 then (if i.val < 53 then 36 else 14) else (if i.val < 55 then 48 else 46))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 17 else 63) else (if i.val < 59 then 41 else 52)) else (if i.val < 62 then (if i.val < 61 then 40 else 13) else (if i.val < 63 then 18 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 33 else 46) else (if i.val < 3 then 35 else 62)) else (if i.val < 6 then (if i.val < 5 then 37 else 15) else (if i.val < 7 then 39 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 34 else 40) else (if i.val < 11 then 50 else 27)) else (if i.val < 14 then (if i.val < 13 then 63 else 44) else (if i.val < 15 then 63 else 46)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 39 else 48) else (if i.val < 19 then 35 else 50)) else (if i.val < 22 then (if i.val < 21 then 35 else 52) else (if i.val < 23 then 39 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 32 else 37) else (if i.val < 27 then 48 else 53)) else (if i.val < 30 then (if i.val < 29 then 47 else 4) else (if i.val < 31 then 63 else 20))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 48 else 47) else (if i.val < 35 then 48 else 63)) else (if i.val < 38 then (if i.val < 37 then 52 else 14) else (if i.val < 39 then 27 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 35 else 26) else (if i.val < 43 then 51 else 26)) else (if i.val < 46 then (if i.val < 45 then 2 else 30) else (if i.val < 47 then 18 else 30)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 40 else 45) else (if i.val < 51 then 56 else 2)) else (if i.val < 54 then (if i.val < 53 then 9 else 12) else (if i.val < 55 then 25 else 6))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 40 else 24) else (if i.val < 59 then 44 else 26)) else (if i.val < 62 then (if i.val < 61 then 44 else 14) else (if i.val < 63 then 40 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 4 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 0) else (if i.val < 7 then 1 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 0 else 2)) else (if i.val < 14 then (if i.val < 13 then 3 else 1) else (if i.val < 15 then 2 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 1) else (if i.val < 19 then 2 else 1)) else (if i.val < 22 then (if i.val < 21 then 3 else 1) else (if i.val < 23 then 2 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 3 else 0) else (if i.val < 31 then 1 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 2 else 0) else (if i.val < 35 then 3 else 0)) else (if i.val < 38 then (if i.val < 37 then 2 else 0) else (if i.val < 39 then 0 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 3) else (if i.val < 43 then 0 else 2)) else (if i.val < 46 then (if i.val < 45 then 0 else 3) else (if i.val < 47 then 0 else 2)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 0 else 2)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 0 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 2 else 1) else (if i.val < 59 then 3 else 1)) else (if i.val < 62 then (if i.val < 61 then 2 else 3) else (if i.val < 63 then 3 else 0)))))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 64 := ((if i.val < 1 then #[7,30,47,45] else (if i.val < 2 then #[53,30,14,12] else #[3,59,61,12])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 64 := ((if i.val < 1 then #[7,30,47,45] else (if i.val < 2 then #[53,30,14,12] else #[7,59,61,12])) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 127 else 63) : Fin 128)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,1] else #[0,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,1] else #[0,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[63,61,21] else #[63,61,53]) : Array (Fin 64))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
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
  generatorCount := 4
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
  toFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N21

namespace N22
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 81 else 63) else (if j.val < 3 then 61 else (if j.val < 4 then 29 else 25))) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 128 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 17) else (if i.val < 3 then 18 else 19)) else (if i.val < 6 then (if i.val < 5 then 20 else 21) else (if i.val < 7 then 22 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 25) else (if i.val < 11 then 26 else 27)) else (if i.val < 14 then (if i.val < 13 then 28 else 29) else (if i.val < 15 then 30 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 48 else 49) else (if i.val < 19 then 50 else 51)) else (if i.val < 22 then (if i.val < 21 then 52 else 53) else (if i.val < 23 then 54 else 55))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 56 else 57) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 80 else 81) else (if i.val < 35 then 82 else 83)) else (if i.val < 38 then (if i.val < 37 then 84 else 85) else (if i.val < 39 then 86 else 87))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 88 else 89) else (if i.val < 43 then 90 else 91)) else (if i.val < 46 then (if i.val < 45 then 92 else 93) else (if i.val < 47 then 94 else 95)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 112 else 113) else (if i.val < 51 then 114 else 115)) else (if i.val < 54 then (if i.val < 53 then 116 else 117) else (if i.val < 55 then 118 else 119))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 120 else 121) else (if i.val < 59 then 122 else 123)) else (if i.val < 62 then (if i.val < 61 then 124 else 125) else (if i.val < 63 then 126 else 127)))))) : Fin 128)
private def next (i : Fin 64) (j : Fin 5) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[30,32,34,50,54] else #[22,33,35,51,62]) else (if i.val < 3 then #[62,34,32,18,22] else #[54,35,33,19,30])) else (if i.val < 6 then (if i.val < 5 then #[26,36,38,54,50] else #[18,37,39,55,58]) else (if i.val < 7 then #[58,38,36,22,18] else #[50,39,37,23,26]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[31,40,42,58,55] else #[23,41,43,59,63]) else (if i.val < 11 then #[63,42,40,26,23] else #[55,43,41,27,31])) else (if i.val < 14 then (if i.val < 13 then #[27,44,46,62,51] else #[19,45,47,63,59]) else (if i.val < 15 then #[59,46,44,30,19] else #[51,47,45,31,27])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[14,48,50,34,38] else #[6,49,51,35,46]) else (if i.val < 19 then #[46,50,48,2,6] else #[38,51,49,3,14])) else (if i.val < 22 then (if i.val < 21 then #[10,52,54,38,34] else #[2,53,55,39,42]) else (if i.val < 23 then #[42,54,52,6,2] else #[34,55,53,7,10]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,56,58,42,39] else #[7,57,59,43,47]) else (if i.val < 27 then #[47,58,56,10,7] else #[39,59,57,11,15])) else (if i.val < 30 then (if i.val < 29 then #[11,60,62,46,35] else #[3,61,63,47,43]) else (if i.val < 31 then #[43,62,60,14,3] else #[35,63,61,15,11]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[28,0,2,48,52] else #[20,1,3,49,60]) else (if i.val < 35 then #[60,2,0,16,20] else #[52,3,1,17,28])) else (if i.val < 38 then (if i.val < 37 then #[24,4,6,52,48] else #[16,5,7,53,56]) else (if i.val < 39 then #[56,6,4,20,16] else #[48,7,5,21,24]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[29,8,10,56,53] else #[21,9,11,57,61]) else (if i.val < 43 then #[61,10,8,24,21] else #[53,11,9,25,29])) else (if i.val < 46 then (if i.val < 45 then #[25,12,14,60,49] else #[17,13,15,61,57]) else (if i.val < 47 then #[57,14,12,28,17] else #[49,15,13,29,25])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[12,16,18,32,36] else #[4,17,19,33,44]) else (if i.val < 51 then #[44,18,16,0,4] else #[36,19,17,1,12])) else (if i.val < 54 then (if i.val < 53 then #[8,20,22,36,32] else #[0,21,23,37,40]) else (if i.val < 55 then #[40,22,20,4,0] else #[32,23,21,5,8]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[13,24,26,40,37] else #[5,25,27,41,45]) else (if i.val < 59 then #[45,26,24,8,5] else #[37,27,25,9,13])) else (if i.val < 62 then (if i.val < 61 then #[9,28,30,44,33] else #[1,29,31,45,41]) else (if i.val < 63 then #[41,30,28,12,1] else #[33,31,29,13,9])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 50 else 7) else (if i.val < 3 then 54 else 8)) else (if i.val < 6 then (if i.val < 5 then 31 else 59) else (if i.val < 7 then 52 else 42))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 47 else 5) else (if i.val < 11 then 22 else 14)) else (if i.val < 14 then (if i.val < 13 then 55 else 4) else (if i.val < 15 then 39 else 13)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 53 else 32) else (if i.val < 19 then 63 else 17)) else (if i.val < 22 then (if i.val < 21 then 6 else 43) else (if i.val < 23 then 27 else 20))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 60 else 37) else (if i.val < 27 then 46 else 35)) else (if i.val < 30 then (if i.val < 29 then 34 else 3) else (if i.val < 31 then 30 else 2))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 49 else 1) else (if i.val < 35 then 26 else 11)) else (if i.val < 38 then (if i.val < 37 then 48 else 41) else (if i.val < 39 then 25 else 58))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 45 else 21) else (if i.val < 43 then 44 else 16)) else (if i.val < 46 then (if i.val < 45 then 33 else 18) else (if i.val < 47 then 57 else 15)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 62 else 9) else (if i.val < 51 then 56 else 28)) else (if i.val < 54 then (if i.val < 53 then 23 else 38) else (if i.val < 55 then 24 else 36))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 51 else 40) else (if i.val < 59 then 61 else 19)) else (if i.val < 62 then (if i.val < 61 then 10 else 12) else (if i.val < 63 then 29 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 54 else 33) else (if i.val < 3 then 34 else 33)) else (if i.val < 6 then (if i.val < 5 then 49 else 55) else (if i.val < 7 then 38 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 52 else 63) else (if i.val < 11 then 20 else 31)) else (if i.val < 14 then (if i.val < 13 then 51 else 63) else (if i.val < 15 then 19 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 38 else 49) else (if i.val < 19 then 6 else 13)) else (if i.val < 22 then (if i.val < 21 then 33 else 41) else (if i.val < 23 then 1 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 42 else 47) else (if i.val < 27 then 10 else 15)) else (if i.val < 30 then (if i.val < 29 then 60 else 63) else (if i.val < 31 then 3 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 52 else 63) else (if i.val < 35 then 20 else 31)) else (if i.val < 38 then (if i.val < 37 then 52 else 59) else (if i.val < 39 then 20 else 27))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10 else 9) else (if i.val < 43 then 10 else 29)) else (if i.val < 46 then (if i.val < 45 then 49 else 13) else (if i.val < 47 then 17 else 29)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 36 else 33) else (if i.val < 51 then 4 else 1)) else (if i.val < 54 then (if i.val < 53 then 20 else 43) else (if i.val < 55 then 20 else 11))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 45) else (if i.val < 59 then 26 else 13)) else (if i.val < 62 then (if i.val < 61 then 33 else 31) else (if i.val < 63 then 1 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 5 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 1) else (if i.val < 3 then 1 else 2)) else (if i.val < 6 then (if i.val < 5 then 0 else 3) else (if i.val < 7 then 1 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 4) else (if i.val < 11 then 0 else 4)) else (if i.val < 14 then (if i.val < 13 then 4 else 3) else (if i.val < 15 then 4 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 1) else (if i.val < 19 then 4 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 4) else (if i.val < 27 then 3 else 4)) else (if i.val < 30 then (if i.val < 29 then 1 else 2) else (if i.val < 31 then 4 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 4 else 0) else (if i.val < 35 then 4 else 0)) else (if i.val < 38 then (if i.val < 37 then 3 else 0) else (if i.val < 39 then 3 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 2 else 1) else (if i.val < 43 then 1 else 4)) else (if i.val < 46 then (if i.val < 45 then 4 else 1) else (if i.val < 47 then 4 else 3)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 4 else 3) else (if i.val < 51 then 4 else 3)) else (if i.val < 54 then (if i.val < 53 then 1 else 0) else (if i.val < 55 then 2 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 4) else (if i.val < 59 then 1 else 4)) else (if i.val < 62 then (if i.val < 61 then 4 else 2) else (if i.val < 63 then 4 else 0)))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 64 := ((if i.val < 1 then #[3,31,29,47,43] else (if i.val < 2 then #[40,31,29,13,9] else #[40,62,54,59,9])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 64 := ((if i.val < 1 then #[3,31,29,47,43] else (if i.val < 2 then #[40,31,29,13,9] else #[3,55,54,59,9])) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 127 else 7) : Fin 128)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,0,1] else #[1,1,0]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,0,1] else #[1,1,0]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 2) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[31,59,63] else #[62,13,9]) : Array (Fin 64))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
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
  generatorCount := 5
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
  toFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator4 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 5) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else (if k.val < 4 then literalGenerator3 else literalGenerator4)))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 5) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N22

namespace N23
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 7 else 55) else (if j.val < 3 then 61 else 16)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 32) : Fin 128 := ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 7) else (if i.val < 3 then 13 else 14)) else (if i.val < 6 then (if i.val < 5 then 16 else 19) else (if i.val < 7 then 25 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 32 else 35) else (if i.val < 11 then 41 else 42)) else (if i.val < 14 then (if i.val < 13 then 52 else 55) else (if i.val < 15 then 61 else 62)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 69 else 70) else (if i.val < 19 then 76 else 79)) else (if i.val < 22 then (if i.val < 21 then 81 else 82) else (if i.val < 23 then 88 else 91))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 97 else 98) else (if i.val < 27 then 104 else 107)) else (if i.val < 30 then (if i.val < 29 then 117 else 118) else (if i.val < 31 then 124 else 127))))) : Fin 128)
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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[19,13,14,21] else (if i.val < 2 then #[11,15,14,4] else #[1,15,29,23])) : Array (Fin 32))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 32 := ((if i.val < 1 then #[19,13,14,21] else (if i.val < 2 then #[11,15,14,4] else #[1,28,29,23])) : Array (Fin 32))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 4) : Source := ⟨((if i.val < 2 then (if i.val < 1 then 127 else 63) else (if i.val < 3 then 123 else 59)) : Fin 128)⟩
private def quotientNext (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,0] else #[0,3,1]) else (if i.val < 3 then #[3,0,2] else #[2,1,3])) : Array (Fin 4))[j.val]!
private def quotientPrev (i : Fin 4) (j : Fin 3) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then #[1,2,0] else #[0,3,1]) else (if i.val < 3 then #[3,0,2] else #[2,1,3])) : Array (Fin 4))[j.val]!
private def quotientParents (i : Fin 4) : Fin 4 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 1)) : Fin 4)
private def quotientLetters (i : Fin 4) : Fin 3 := ((if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) : Fin 3)
private def stepWitness (i : Fin 4) (j : Fin 3) : Fin 32 := ((if i.val < 2 then (if i.val < 1 then #[31,31,11] else #[31,31,27]) else (if i.val < 3 then #[31,31,1] else #[31,31,19])) : Array (Fin 32))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 4 where
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
  quotientCount := 4
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

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N23

namespace N24
def normalGenerators (j : Fin 4) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 31 else 7) else (if j.val < 3 then 55 else 16)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 128 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 8 else 11) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 25 else 26) else (if i.val < 15 then 28 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 35) else (if i.val < 19 then 37 else 38)) else (if i.val < 22 then (if i.val < 21 then 41 else 42) else (if i.val < 23 then 44 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 50) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 56 else 59) else (if i.val < 31 then 61 else 62))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 64 else 67) else (if i.val < 35 then 69 else 70)) else (if i.val < 38 then (if i.val < 37 then 73 else 74) else (if i.val < 39 then 76 else 79))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 81 else 82) else (if i.val < 43 then 84 else 87)) else (if i.val < 46 then (if i.val < 45 then 88 else 91) else (if i.val < 47 then 93 else 94)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 97 else 98) else (if i.val < 51 then 100 else 103)) else (if i.val < 54 then (if i.val < 53 then 104 else 107) else (if i.val < 55 then 109 else 110))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 112 else 115) else (if i.val < 59 then 117 else 118)) else (if i.val < 62 then (if i.val < 61 then 121 else 122) else (if i.val < 63 then 124 else 127)))))) : Fin 128)
private def next (i : Fin 64) (j : Fin 4) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[48,28,36,51] else #[16,60,37,23]) else (if i.val < 3 then #[50,44,38,53] else #[18,12,39,17])) else (if i.val < 6 then (if i.val < 5 then #[52,61,32,55] else #[20,29,33,19]) else (if i.val < 7 then #[54,13,34,49] else #[22,45,35,21]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[56,52,44,63] else #[24,20,45,27]) else (if i.val < 11 then #[58,4,46,57] else #[26,36,47,29])) else (if i.val < 14 then (if i.val < 13 then #[60,21,40,59] else #[28,53,41,31]) else (if i.val < 15 then #[62,37,42,61] else #[30,5,43,25])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[32,62,52,39] else #[0,30,53,3]) else (if i.val < 19 then #[34,14,54,33] else #[2,46,55,5])) else (if i.val < 22 then (if i.val < 21 then #[36,31,48,35] else #[4,63,49,7]) else (if i.val < 23 then #[38,47,50,37] else #[6,15,51,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[40,22,60,43] else #[8,54,61,15]) else (if i.val < 27 then #[42,38,62,45] else #[10,6,63,9])) else (if i.val < 30 then (if i.val < 29 then #[44,55,56,47] else #[12,23,57,11]) else (if i.val < 31 then #[46,7,58,41] else #[14,39,59,13]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[49,56,4,54] else #[17,24,5,18]) else (if i.val < 35 then #[51,8,6,48] else #[19,40,7,20])) else (if i.val < 38 then (if i.val < 37 then #[53,25,0,50] else #[21,57,1,22]) else (if i.val < 39 then #[55,41,2,52] else #[23,9,3,16]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[57,16,12,58] else #[25,48,13,30]) else (if i.val < 43 then #[59,32,14,60] else #[27,0,15,24])) else (if i.val < 46 then (if i.val < 45 then #[61,49,8,62] else #[29,17,9,26]) else (if i.val < 47 then #[63,1,10,56] else #[31,33,11,28])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[33,26,20,34] else #[1,58,21,6]) else (if i.val < 51 then #[35,42,22,36] else #[3,10,23,0])) else (if i.val < 54 then (if i.val < 53 then #[37,59,16,38] else #[5,27,17,2]) else (if i.val < 55 then #[39,11,18,32] else #[7,43,19,4]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[41,50,28,46] else #[9,18,29,10]) else (if i.val < 59 then #[43,2,30,40] else #[11,34,31,12])) else (if i.val < 62 then (if i.val < 61 then #[45,19,24,42] else #[13,51,25,14]) else (if i.val < 63 then #[47,35,26,44] else #[15,3,27,8])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 27 else 50) else (if i.val < 3 then 53 else 2)) else (if i.val < 6 then (if i.val < 5 then 40 else 6) else (if i.val < 7 then 14 else 20))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 15) else (if i.val < 11 then 13 else 57)) else (if i.val < 14 then (if i.val < 13 then 10 else 42) else (if i.val < 15 then 32 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 38 else 12) else (if i.val < 19 then 9 else 26)) else (if i.val < 22 then (if i.val < 21 then 23 else 34) else (if i.val < 23 then 51 else 37))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 28 else 8) else (if i.val < 27 then 62 else 3)) else (if i.val < 30 then (if i.val < 29 then 46 else 24) else (if i.val < 31 then 5 else 56))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 60 else 25) else (if i.val < 35 then 31 else 52)) else (if i.val < 38 then (if i.val < 37 then 55 else 47) else (if i.val < 39 then 48 else 11))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 35 else 22) else (if i.val < 43 then 61 else 7)) else (if i.val < 46 then (if i.val < 45 then 18 else 44) else (if i.val < 47 then 19 else 63)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 54 else 43) else (if i.val < 51 then 45 else 59)) else (if i.val < 54 then (if i.val < 53 then 17 else 39) else (if i.val < 55 then 29 else 58))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 16 else 41) else (if i.val < 59 then 21 else 36)) else (if i.val < 62 then (if i.val < 61 then 33 else 30) else (if i.val < 63 then 49 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 43 else 46) else (if i.val < 3 then 58 else 63)) else (if i.val < 6 then (if i.val < 5 then 10 else 15) else (if i.val < 7 then 27 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 63 else 27) else (if i.val < 11 then 27 else 29)) else (if i.val < 14 then (if i.val < 13 then 3 else 6) else (if i.val < 15 then 18 else 63)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 39 else 3) else (if i.val < 19 then 3 else 5)) else (if i.val < 22 then (if i.val < 21 then 5 else 12) else (if i.val < 23 then 7 else 39))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 43 else 15) else (if i.val < 27 then 45 else 63)) else (if i.val < 30 then (if i.val < 29 then 56 else 5) else (if i.val < 31 then 15 else 20))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 54 else 5) else (if i.val < 35 then 18 else 7)) else (if i.val < 38 then (if i.val < 37 then 20 else 52) else (if i.val < 39 then 52 else 3))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 12 else 30) else (if i.val < 43 then 14 else 15)) else (if i.val < 46 then (if i.val < 45 then 8 else 9) else (if i.val < 47 then 30 else 28)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 41 else 6) else (if i.val < 51 then 56 else 0)) else (if i.val < 54 then (if i.val < 53 then 8 else 17) else (if i.val < 55 then 25 else 19))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 8 else 10) else (if i.val < 59 then 30 else 12)) else (if i.val < 62 then (if i.val < 61 then 12 else 25) else (if i.val < 63 then 44 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 4 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 3) else (if i.val < 11 then 0 else 3)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 3) else (if i.val < 19 then 0 else 3)) else (if i.val < 22 then (if i.val < 21 then 0 else 1) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 3) else (if i.val < 27 then 3 else 2)) else (if i.val < 30 then (if i.val < 29 then 2 else 1) else (if i.val < 31 then 0 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 3 else 2) else (if i.val < 35 then 0 else 2)) else (if i.val < 38 then (if i.val < 37 then 0 else 0) else (if i.val < 39 then 3 else 2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 2 else 3) else (if i.val < 43 then 2 else 2)) else (if i.val < 46 then (if i.val < 45 then 2 else 2) else (if i.val < 47 then 0 else 3)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 1 else 3) else (if i.val < 51 then 1 else 3)) else (if i.val < 54 then (if i.val < 53 then 1 else 2) else (if i.val < 55 then 1 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 3) else (if i.val < 59 then 2 else 3)) else (if i.val < 62 then (if i.val < 61 then 0 else 2) else (if i.val < 63 then 3 else 0)))))) : Fin 4)

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

private def posWitness (i : Fin 3) (j : Fin 4) : Fin 64 := ((if i.val < 1 then #[46,39,27,41] else (if i.val < 2 then #[15,21,31,8] else #[57,3,31,45])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 4) : Fin 64 := ((if i.val < 1 then #[46,39,27,41] else (if i.val < 2 then #[15,21,31,8] else #[61,3,58,45])) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 127 else 63) : Fin 128)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,0] else #[0,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,1,0] else #[0,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[63,29,21] else #[63,29,53]) : Array (Fin 64))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
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
  generatorCount := 4
  normalGenerators := normalGenerators
  generated := rfl
  quotientCount := 2
  cardinal := by rw [kernel_card,source_card]
  cosets := cosets
  prev := quotientPrev
  prev_next := (by decide +kernel)

private def literalGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,3,2,5,4,7,6,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,2,1,4,3,6,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 4) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else literalGenerator3))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 4) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N24

namespace N25
def normalGenerators (j : Fin 5) : Source := ⟨((if j.val < 2 then (if j.val < 1 then 7 else 55) else (if j.val < 3 then 61 else (if j.val < 4 then 29 else 16))) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 128 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 4 else 7)) else (if i.val < 6 then (if i.val < 5 then 9 else 10) else (if i.val < 7 then 13 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 19) else (if i.val < 11 then 20 else 23)) else (if i.val < 14 then (if i.val < 13 then 25 else 26) else (if i.val < 15 then 29 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 35) else (if i.val < 19 then 36 else 39)) else (if i.val < 22 then (if i.val < 21 then 41 else 42) else (if i.val < 23 then 45 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 51) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 61 else 62))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 65 else 66) else (if i.val < 35 then 69 else 70)) else (if i.val < 38 then (if i.val < 37 then 72 else 75) else (if i.val < 39 then 76 else 79))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 81 else 82) else (if i.val < 43 then 85 else 86)) else (if i.val < 46 then (if i.val < 45 then 88 else 91) else (if i.val < 47 then 92 else 95)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 97 else 98) else (if i.val < 51 then 101 else 102)) else (if i.val < 54 then (if i.val < 53 then 104 else 107) else (if i.val < 55 then 108 else 111))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 113 else 114) else (if i.val < 59 then 117 else 118)) else (if i.val < 62 then (if i.val < 61 then 120 else 123) else (if i.val < 63 then 124 else 127)))))) : Fin 128)
private def next (i : Fin 64) (j : Fin 5) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[60,36,33,49,55] else #[28,37,32,17,19]) else (if i.val < 3 then #[44,38,35,51,53] else #[12,39,34,19,17])) else (if i.val < 6 then (if i.val < 5 then #[29,32,37,53,51] else #[61,33,36,21,23]) else (if i.val < 7 then #[13,34,39,55,49] else #[45,35,38,23,21]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[52,44,41,57,63] else #[20,45,40,25,27]) else (if i.val < 11 then #[36,46,43,59,61] else #[4,47,42,27,25])) else (if i.val < 14 then (if i.val < 13 then #[21,40,45,61,59] else #[53,41,44,29,31]) else (if i.val < 15 then #[5,42,47,63,57] else #[37,43,46,31,29])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[62,52,49,33,39] else #[30,53,48,1,3]) else (if i.val < 19 then #[46,54,51,35,37] else #[14,55,50,3,1])) else (if i.val < 22 then (if i.val < 21 then #[31,48,53,37,35] else #[63,49,52,5,7]) else (if i.val < 23 then #[15,50,55,39,33] else #[47,51,54,7,5]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[54,60,57,41,47] else #[22,61,56,9,11]) else (if i.val < 27 then #[38,62,59,43,45] else #[6,63,58,11,9])) else (if i.val < 30 then (if i.val < 29 then #[23,56,61,45,43] else #[55,57,60,13,15]) else (if i.val < 31 then #[7,58,63,47,41] else #[39,59,62,15,13]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[24,4,1,48,50] else #[56,5,0,16,22]) else (if i.val < 35 then #[8,6,3,50,48] else #[40,7,2,18,20])) else (if i.val < 38 then (if i.val < 37 then #[57,0,5,52,54] else #[25,1,4,20,18]) else (if i.val < 39 then #[41,2,7,54,52] else #[9,3,6,22,16]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[16,12,9,56,58] else #[48,13,8,24,30]) else (if i.val < 43 then #[0,14,11,58,56] else #[32,15,10,26,28])) else (if i.val < 46 then (if i.val < 45 then #[49,8,13,60,62] else #[17,9,12,28,26]) else (if i.val < 47 then #[33,10,15,62,60] else #[1,11,14,30,24])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[26,20,17,32,34] else #[58,21,16,0,6]) else (if i.val < 51 then #[10,22,19,34,32] else #[42,23,18,2,4])) else (if i.val < 54 then (if i.val < 53 then #[59,16,21,36,38] else #[27,17,20,4,2]) else (if i.val < 55 then #[43,18,23,38,36] else #[11,19,22,6,0]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[18,28,25,40,42] else #[50,29,24,8,14]) else (if i.val < 59 then #[2,30,27,42,40] else #[34,31,26,10,12])) else (if i.val < 62 then (if i.val < 61 then #[51,24,29,44,46] else #[19,25,28,12,10]) else (if i.val < 63 then #[35,26,31,46,44] else #[3,27,30,14,8])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 47 else 33) else (if i.val < 3 then 37 else 1)) else (if i.val < 6 then (if i.val < 5 then 38 else 18) else (if i.val < 7 then 11 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 14) else (if i.val < 11 then 54 else 13)) else (if i.val < 14 then (if i.val < 13 then 6 else 35) else (if i.val < 15 then 4 else 56)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 29 else 10) else (if i.val < 19 then 60 else 9)) else (if i.val < 22 then (if i.val < 21 then 40 else 23) else (if i.val < 23 then 28 else 43))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 44 else 39) else (if i.val < 27 then 53 else 2)) else (if i.val < 30 then (if i.val < 29 then 52 else 49) else (if i.val < 31 then 3 else 55))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 45) else (if i.val < 35 then 8 else 41)) else (if i.val < 38 then (if i.val < 37 then 46 else 58) else (if i.val < 39 then 42 else 7))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 24 else 17) else (if i.val < 43 then 19 else 63)) else (if i.val < 46 then (if i.val < 45 then 22 else 25) else (if i.val < 47 then 62 else 16)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 31 else 36) else (if i.val < 51 then 30 else 59)) else (if i.val < 54 then (if i.val < 53 then 21 else 34) else (if i.val < 55 then 61 else 32))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 48 else 20) else (if i.val < 59 then 12 else 27)) else (if i.val < 62 then (if i.val < 61 then 50 else 26) else (if i.val < 63 then 51 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 42 else 19) else (if i.val < 3 then 58 else 63)) else (if i.val < 6 then (if i.val < 5 then 11 else 14) else (if i.val < 7 then 27 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 63 else 27) else (if i.val < 11 then 61 else 27)) else (if i.val < 14 then (if i.val < 13 then 3 else 6) else (if i.val < 15 then 63 else 22)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 39 else 3) else (if i.val < 19 then 35 else 3)) else (if i.val < 22 then (if i.val < 21 then 9 else 12) else (if i.val < 23 then 39 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 47 else 11) else (if i.val < 27 then 45 else 63)) else (if i.val < 30 then (if i.val < 29 then 45 else 57) else (if i.val < 31 then 63 else 59))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 50 else 5) else (if i.val < 35 then 3 else 7)) else (if i.val < 38 then (if i.val < 37 then 5 else 1) else (if i.val < 39 then 7 else 3))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 12 else 30) else (if i.val < 43 then 14 else 28)) else (if i.val < 46 then (if i.val < 45 then 8 else 12) else (if i.val < 47 then 60 else 30)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 34 else 6) else (if i.val < 51 then 34 else 2)) else (if i.val < 54 then (if i.val < 53 then 8 else 17) else (if i.val < 55 then 38 else 19))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 42 else 14) else (if i.val < 59 then 27 else 12)) else (if i.val < 62 then (if i.val < 61 then 44 else 12) else (if i.val < 63 then 44 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 5 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 4) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 4) else (if i.val < 11 then 4 else 3)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 3 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4 else 4) else (if i.val < 19 then 3 else 3)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 3 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 4) else (if i.val < 27 then 4 else 1)) else (if i.val < 30 then (if i.val < 29 then 3 else 1) else (if i.val < 31 then 2 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 4 else 1) else (if i.val < 35 then 2 else 1)) else (if i.val < 38 then (if i.val < 37 then 2 else 1) else (if i.val < 39 then 2 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 1 else 4) else (if i.val < 43 then 1 else 4)) else (if i.val < 46 then (if i.val < 45 then 1 else 2) else (if i.val < 47 then 4 else 3)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 4 else 4) else (if i.val < 51 then 3 else 3)) else (if i.val < 54 then (if i.val < 53 then 0 else 1) else (if i.val < 55 then 3 else 1))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 4 else 4) else (if i.val < 59 then 2 else 4)) else (if i.val < 62 then (if i.val < 61 then 3 else 3) else (if i.val < 63 then 4 else 0)))))) : Fin 5)

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

private def posWitness (i : Fin 3) (j : Fin 5) : Fin 64 := ((if i.val < 1 then #[39,27,30,47,41] else (if i.val < 2 then #[21,31,30,14,8] else #[3,31,59,61,45])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 5) : Fin 64 := ((if i.val < 1 then #[39,27,30,47,41] else (if i.val < 2 then #[21,31,30,14,8] else #[3,58,59,61,45])) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 127 else 63) : Fin 128)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,0] else #[0,1,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[1,0,0] else #[0,1,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 0) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[63,61,21] else #[63,61,53]) : Array (Fin 64))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
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
  generatorCount := 5
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
  toFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  invFun x := (#[0,7,2,5,4,3,6,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator4 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 5) : Equiv.Perm (Fin 8) :=
  (if k.val < 2 then (if k.val < 1 then literalGenerator0 else literalGenerator1) else (if k.val < 3 then literalGenerator2 else (if k.val < 4 then literalGenerator3 else literalGenerator4)))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 5) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N25

namespace N26
def normalGenerators (j : Fin 2) : Source := ⟨((if j.val < 1 then 63 else 7) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 64) : Fin 128 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 5) else (if i.val < 3 then 6 else 7)) else (if i.val < 6 then (if i.val < 5 then 12 else 13) else (if i.val < 7 then 14 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 17) else (if i.val < 11 then 18 else 19)) else (if i.val < 14 then (if i.val < 13 then 24 else 25) else (if i.val < 15 then 26 else 27)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 32 else 33) else (if i.val < 19 then 34 else 35)) else (if i.val < 22 then (if i.val < 21 then 40 else 41) else (if i.val < 23 then 42 else 43))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 52 else 53) else (if i.val < 27 then 54 else 55)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 68 else 69) else (if i.val < 35 then 70 else 71)) else (if i.val < 38 then (if i.val < 37 then 76 else 77) else (if i.val < 39 then 78 else 79))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 80 else 81) else (if i.val < 43 then 82 else 83)) else (if i.val < 46 then (if i.val < 45 then 88 else 89) else (if i.val < 47 then 90 else 91)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 96 else 97) else (if i.val < 51 then 98 else 99)) else (if i.val < 54 then (if i.val < 53 then 104 else 105) else (if i.val < 55 then 106 else 107))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 116 else 117) else (if i.val < 59 then 118 else 119)) else (if i.val < 62 then (if i.val < 61 then 124 else 125) else (if i.val < 63 then 126 else 127)))))) : Fin 128)
private def next (i : Fin 64) (j : Fin 2) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[32,44] else #[33,12]) else (if i.val < 3 then #[34,45] else #[35,13])) else (if i.val < 6 then (if i.val < 5 then #[36,46] else #[37,14]) else (if i.val < 7 then #[38,47] else #[39,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[40,52] else #[41,20]) else (if i.val < 11 then #[42,53] else #[43,21])) else (if i.val < 14 then (if i.val < 13 then #[44,54] else #[45,22]) else (if i.val < 15 then #[46,55] else #[47,23])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[48,60] else #[49,28]) else (if i.val < 19 then #[50,61] else #[51,29])) else (if i.val < 22 then (if i.val < 21 then #[52,62] else #[53,30]) else (if i.val < 23 then #[54,63] else #[55,31]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[56,36] else #[57,4]) else (if i.val < 27 then #[58,37] else #[59,5])) else (if i.val < 30 then (if i.val < 29 then #[60,38] else #[61,6]) else (if i.val < 31 then #[62,39] else #[63,7]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,40] else #[1,8]) else (if i.val < 35 then #[2,41] else #[3,9])) else (if i.val < 38 then (if i.val < 37 then #[4,42] else #[5,10]) else (if i.val < 39 then #[6,43] else #[7,11]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[8,48] else #[9,16]) else (if i.val < 43 then #[10,49] else #[11,17])) else (if i.val < 46 then (if i.val < 45 then #[12,50] else #[13,18]) else (if i.val < 47 then #[14,51] else #[15,19])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[16,56] else #[17,24]) else (if i.val < 51 then #[18,57] else #[19,25])) else (if i.val < 54 then (if i.val < 53 then #[20,58] else #[21,26]) else (if i.val < 55 then #[22,59] else #[23,27]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[24,32] else #[25,0]) else (if i.val < 59 then #[26,33] else #[27,1])) else (if i.val < 62 then (if i.val < 61 then #[28,34] else #[29,2]) else (if i.val < 63 then #[30,35] else #[31,3])))))) : Array (Fin 64))[j.val]!
private def rank (i : Fin 64) : ℕ := (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 39) else (if i.val < 3 then 38 else 2)) else (if i.val < 6 then (if i.val < 5 then 54 else 45) else (if i.val < 7 then 44 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 8) else (if i.val < 11 then 60 else 11)) else (if i.val < 14 then (if i.val < 13 then 50 else 5) else (if i.val < 15 then 55 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 28) else (if i.val < 19 then 16 else 20)) else (if i.val < 22 then (if i.val < 21 then 15 else 19) else (if i.val < 23 then 10 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 51 else 43) else (if i.val < 27 then 42 else 33)) else (if i.val < 30 then (if i.val < 29 then 41 else 32) else (if i.val < 31 then 30 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 56 else 48) else (if i.val < 35 then 47 else 4)) else (if i.val < 38 then (if i.val < 37 then 59 else 53) else (if i.val < 39 then 52 else 6))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 62 else 14) else (if i.val < 43 then 63 else 18)) else (if i.val < 46 then (if i.val < 45 then 58 else 9) else (if i.val < 47 then 61 else 12)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 34 else 40) else (if i.val < 51 then 25 else 31)) else (if i.val < 54 then (if i.val < 53 then 23 else 29) else (if i.val < 55 then 17 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 37) else (if i.val < 59 then 36 else 27)) else (if i.val < 62 then (if i.val < 61 then 35 else 26) else (if i.val < 63 then 24 else 0))))))
private def parents (i : Fin 64) : Fin 64 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 59) else (if i.val < 3 then 61 else 63)) else (if i.val < 6 then (if i.val < 5 then 25 else 27) else (if i.val < 7 then 29 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 33 else 35) else (if i.val < 11 then 37 else 39)) else (if i.val < 14 then (if i.val < 13 then 1 else 3) else (if i.val < 15 then 5 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 41 else 43) else (if i.val < 19 then 45 else 47)) else (if i.val < 22 then (if i.val < 21 then 9 else 11) else (if i.val < 23 then 13 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 51) else (if i.val < 27 then 53 else 55)) else (if i.val < 30 then (if i.val < 29 then 17 else 19) else (if i.val < 31 then 21 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 56 else 58) else (if i.val < 35 then 60 else 3)) else (if i.val < 38 then (if i.val < 37 then 24 else 26) else (if i.val < 39 then 28 else 7))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 32 else 9) else (if i.val < 43 then 36 else 11)) else (if i.val < 46 then (if i.val < 45 then 0 else 13) else (if i.val < 47 then 4 else 15)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 17) else (if i.val < 51 then 18 else 19)) else (if i.val < 54 then (if i.val < 53 then 20 else 21) else (if i.val < 55 then 22 else 23))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 48 else 50) else (if i.val < 59 then 52 else 54)) else (if i.val < 62 then (if i.val < 61 then 16 else 18) else (if i.val < 63 then 20 else 63)))))) : Fin 64)
private def letters (i : Fin 64) : Fin 2 := ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 1) else (if i.val < 19 then 1 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 1) else (if i.val < 23 then 1 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 1) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 1 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 1 else 1) else (if i.val < 35 then 1 else 0)) else (if i.val < 38 then (if i.val < 37 then 1 else 1) else (if i.val < 39 then 1 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 1 else 0) else (if i.val < 43 then 1 else 0)) else (if i.val < 46 then (if i.val < 45 then 1 else 0) else (if i.val < 47 then 1 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 0 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 1 else 1) else (if i.val < 59 then 1 else 1)) else (if i.val < 62 then (if i.val < 61 then 1 else 1) else (if i.val < 63 then 1 else 0)))))) : Fin 2)

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

private def posWitness (i : Fin 3) (j : Fin 2) : Fin 64 := ((if i.val < 1 then #[31,39] else (if i.val < 2 then #[31,22] else #[62,3])) : Array (Fin 64))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 2) : Fin 64 := ((if i.val < 1 then #[31,39] else (if i.val < 2 then #[31,22] else #[59,3])) : Array (Fin 64))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 2) : Source := ⟨((if i.val < 1 then 127 else 123) : Fin 128)⟩
private def quotientNext (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,0] else #[1,0,1]) : Array (Fin 2))[j.val]!
private def quotientPrev (i : Fin 2) (j : Fin 3) : Fin 2 := ((if i.val < 1 then #[0,1,0] else #[1,0,1]) : Array (Fin 2))[j.val]!
private def quotientParents (i : Fin 2) : Fin 2 := ((if i.val < 1 then 0 else 0) : Fin 2)
private def quotientLetters (i : Fin 2) : Fin 3 := ((if i.val < 1 then 0 else 1) : Fin 3)
private def stepWitness (i : Fin 2) (j : Fin 3) : Fin 64 := ((if i.val < 1 then #[31,63,22] else #[31,63,3]) : Array (Fin 64))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 2 where
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
  quotientCount := 2
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
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 2) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else literalGenerator1)

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 2) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N26

namespace N27
def normalGenerators (j : Fin 3) : Source := ⟨((if j.val < 1 then 7 else (if j.val < 2 then 63 else 123)) : Fin 128)⟩
def kernel : Subgroup Source := Subgroup.closure (Set.range normalGenerators)
private def rows (i : Fin 128) : Fin 128 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 64 else 65) else (if i.val < 67 then 66 else 67)) else (if i.val < 70 then (if i.val < 69 then 68 else 69) else (if i.val < 71 then 70 else 71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 72 else 73) else (if i.val < 75 then 74 else 75)) else (if i.val < 78 then (if i.val < 77 then 76 else 77) else (if i.val < 79 then 78 else 79)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 80 else 81) else (if i.val < 83 then 82 else 83)) else (if i.val < 86 then (if i.val < 85 then 84 else 85) else (if i.val < 87 then 86 else 87))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 88 else 89) else (if i.val < 91 then 90 else 91)) else (if i.val < 94 then (if i.val < 93 then 92 else 93) else (if i.val < 95 then 94 else 95))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 96 else 97) else (if i.val < 99 then 98 else 99)) else (if i.val < 102 then (if i.val < 101 then 100 else 101) else (if i.val < 103 then 102 else 103))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 104 else 105) else (if i.val < 107 then 106 else 107)) else (if i.val < 110 then (if i.val < 109 then 108 else 109) else (if i.val < 111 then 110 else 111)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 112 else 113) else (if i.val < 115 then 114 else 115)) else (if i.val < 118 then (if i.val < 117 then 116 else 117) else (if i.val < 119 then 118 else 119))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 120 else 121) else (if i.val < 123 then 122 else 123)) else (if i.val < 126 then (if i.val < 125 then 124 else 125) else (if i.val < 127 then 126 else 127))))))) : Fin 128)
private def next (i : Fin 128) (j : Fin 3) : Fin 128 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[120,64,4] else #[56,65,12]) else (if i.val < 3 then #[121,66,6] else #[57,67,14])) else (if i.val < 6 then (if i.val < 5 then #[88,68,0] else #[24,69,8]) else (if i.val < 7 then #[89,70,2] else #[25,71,10]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[122,72,5] else #[58,73,13]) else (if i.val < 11 then #[123,74,7] else #[59,75,15])) else (if i.val < 14 then (if i.val < 13 then #[90,76,1] else #[26,77,9]) else (if i.val < 15 then #[91,78,3] else #[27,79,11])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[104,80,20] else #[40,81,28]) else (if i.val < 19 then #[105,82,22] else #[41,83,30])) else (if i.val < 22 then (if i.val < 21 then #[72,84,16] else #[8,85,24]) else (if i.val < 23 then #[73,86,18] else #[9,87,26]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[106,88,21] else #[42,89,29]) else (if i.val < 27 then #[107,90,23] else #[43,91,31])) else (if i.val < 30 then (if i.val < 29 then #[74,92,17] else #[10,93,25]) else (if i.val < 31 then #[75,94,19] else #[11,95,27]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[124,96,36] else #[60,97,44]) else (if i.val < 35 then #[125,98,38] else #[61,99,46])) else (if i.val < 38 then (if i.val < 37 then #[92,100,32] else #[28,101,40]) else (if i.val < 39 then #[93,102,34] else #[29,103,42]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[126,104,37] else #[62,105,45]) else (if i.val < 43 then #[127,106,39] else #[63,107,47])) else (if i.val < 46 then (if i.val < 45 then #[94,108,33] else #[30,109,41]) else (if i.val < 47 then #[95,110,35] else #[31,111,43])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[108,112,52] else #[44,113,60]) else (if i.val < 51 then #[109,114,54] else #[45,115,62])) else (if i.val < 54 then (if i.val < 53 then #[76,116,48] else #[12,117,56]) else (if i.val < 55 then #[77,118,50] else #[13,119,58]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[110,120,53] else #[46,121,61]) else (if i.val < 59 then #[111,122,55] else #[47,123,63])) else (if i.val < 62 then (if i.val < 61 then #[78,124,49] else #[14,125,57]) else (if i.val < 63 then #[79,126,51] else #[15,127,59])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then #[112,0,68] else #[48,1,76]) else (if i.val < 67 then #[113,2,70] else #[49,3,78])) else (if i.val < 70 then (if i.val < 69 then #[80,4,64] else #[16,5,72]) else (if i.val < 71 then #[81,6,66] else #[17,7,74]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then #[114,8,69] else #[50,9,77]) else (if i.val < 75 then #[115,10,71] else #[51,11,79])) else (if i.val < 78 then (if i.val < 77 then #[82,12,65] else #[18,13,73]) else (if i.val < 79 then #[83,14,67] else #[19,15,75])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then #[96,16,84] else #[32,17,92]) else (if i.val < 83 then #[97,18,86] else #[33,19,94])) else (if i.val < 86 then (if i.val < 85 then #[64,20,80] else #[0,21,88]) else (if i.val < 87 then #[65,22,82] else #[1,23,90]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then #[98,24,85] else #[34,25,93]) else (if i.val < 91 then #[99,26,87] else #[35,27,95])) else (if i.val < 94 then (if i.val < 93 then #[66,28,81] else #[2,29,89]) else (if i.val < 95 then #[67,30,83] else #[3,31,91]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then #[116,32,100] else #[52,33,108]) else (if i.val < 99 then #[117,34,102] else #[53,35,110])) else (if i.val < 102 then (if i.val < 101 then #[84,36,96] else #[20,37,104]) else (if i.val < 103 then #[85,38,98] else #[21,39,106]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then #[118,40,101] else #[54,41,109]) else (if i.val < 107 then #[119,42,103] else #[55,43,111])) else (if i.val < 110 then (if i.val < 109 then #[86,44,97] else #[22,45,105]) else (if i.val < 111 then #[87,46,99] else #[23,47,107])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then #[100,48,116] else #[36,49,124]) else (if i.val < 115 then #[101,50,118] else #[37,51,126])) else (if i.val < 118 then (if i.val < 117 then #[68,52,112] else #[4,53,120]) else (if i.val < 119 then #[69,54,114] else #[5,55,122]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then #[102,56,117] else #[38,57,125]) else (if i.val < 123 then #[103,58,119] else #[39,59,127])) else (if i.val < 126 then (if i.val < 125 then #[70,60,113] else #[6,61,121]) else (if i.val < 127 then #[71,62,115] else #[7,63,123]))))))) : Array (Fin 128))[j.val]!
private def rank (i : Fin 128) : ℕ := (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 81 else 105) else (if i.val < 3 then 38 else 73)) else (if i.val < 6 then (if i.val < 5 then 89 else 55) else (if i.val < 7 then 58 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 52 else 77) else (if i.val < 11 then 6 else 17)) else (if i.val < 14 then (if i.val < 13 then 112 else 84) else (if i.val < 15 then 87 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 108 else 13) else (if i.val < 19 then 123 else 30)) else (if i.val < 22 then (if i.val < 21 then 95 else 33) else (if i.val < 23 then 119 else 51))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 54 else 4) else (if i.val < 27 then 79 else 15)) else (if i.val < 30 then (if i.val < 29 then 25 else 12) else (if i.val < 31 then 50 else 29))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 42 else 75) else (if i.val < 35 then 21 else 46)) else (if i.val < 38 then (if i.val < 37 then 69 else 41) else (if i.val < 39 then 37 else 9))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 23 else 48) else (if i.val < 43 then 10 else 27)) else (if i.val < 46 then (if i.val < 45 then 103 else 70) else (if i.val < 47 then 72 else 18)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 125 else 114) else (if i.val < 51 then 115 else 44)) else (if i.val < 54 then (if i.val < 53 then 117 else 90) else (if i.val < 55 then 93 else 56))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 113 else 88) else (if i.val < 59 then 85 else 8)) else (if i.val < 62 then (if i.val < 61 then 96 else 59) else (if i.val < 63 then 64 else 2)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 107 else 121) else (if i.val < 67 then 63 else 101)) else (if i.val < 70 then (if i.val < 69 then 111 else 83) else (if i.val < 71 then 86 else 5))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 80 else 104) else (if i.val < 75 then 14 else 31)) else (if i.val < 78 then (if i.val < 77 then 124 else 109) else (if i.val < 79 then 110 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 122 else 24) else (if i.val < 83 then 127 else 49)) else (if i.val < 86 then (if i.val < 85 then 116 else 53) else (if i.val < 87 then 126 else 78))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 82 else 11) else (if i.val < 91 then 106 else 28)) else (if i.val < 94 then (if i.val < 93 then 43 else 22) else (if i.val < 95 then 76 else 47))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 68 else 102) else (if i.val < 99 then 36 else 71)) else (if i.val < 102 then (if i.val < 101 then 98 else 66) else (if i.val < 103 then 62 else 19))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 40 else 74) else (if i.val < 107 then 20 else 45)) else (if i.val < 110 then (if i.val < 109 then 120 else 99) else (if i.val < 111 then 100 else 32)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 118 else 92) else (if i.val < 115 then 94 else 26)) else (if i.val < 118 then (if i.val < 117 then 97 else 61) else (if i.val < 119 then 65 else 34))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 91 else 60) else (if i.val < 123 then 57 else 3)) else (if i.val < 126 then (if i.val < 125 then 67 else 35) else (if i.val < 127 then 39 else 0)))))))
private def parents (i : Fin 128) : Fin 128 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 85 else 87) else (if i.val < 3 then 93 else 95)) else (if i.val < 6 then (if i.val < 5 then 117 else 119) else (if i.val < 7 then 125 else 127))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 23) else (if i.val < 11 then 7 else 15)) else (if i.val < 14 then (if i.val < 13 then 53 else 55) else (if i.val < 15 then 61 else 63)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 69 else 71) else (if i.val < 19 then 77 else 79)) else (if i.val < 22 then (if i.val < 21 then 101 else 103) else (if i.val < 23 then 109 else 111))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 7) else (if i.val < 27 then 23 else 15)) else (if i.val < 30 then (if i.val < 29 then 17 else 25) else (if i.val < 31 then 19 else 27))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 81 else 83) else (if i.val < 35 then 89 else 91)) else (if i.val < 38 then (if i.val < 37 then 32 else 40) else (if i.val < 39 then 34 else 123))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 17 else 19) else (if i.val < 43 then 25 else 27)) else (if i.val < 46 then (if i.val < 45 then 33 else 51) else (if i.val < 47 then 35 else 59)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 52 else 113) else (if i.val < 51 then 54 else 115)) else (if i.val < 54 then (if i.val < 53 then 116 else 117) else (if i.val < 55 then 118 else 119))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 53 else 61) else (if i.val < 59 then 55 else 63)) else (if i.val < 62 then (if i.val < 61 then 124 else 125) else (if i.val < 63 then 126 else 127)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 0 else 1) else (if i.val < 67 then 2 else 3)) else (if i.val < 70 then (if i.val < 69 then 4 else 5) else (if i.val < 71 then 6 else 7))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 8 else 9) else (if i.val < 75 then 71 else 79)) else (if i.val < 78 then (if i.val < 77 then 12 else 13) else (if i.val < 79 then 14 else 15)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 16 else 17) else (if i.val < 83 then 18 else 19)) else (if i.val < 86 then (if i.val < 85 then 20 else 21) else (if i.val < 87 then 22 else 23))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 85 else 25) else (if i.val < 91 then 87 else 27)) else (if i.val < 94 then (if i.val < 93 then 81 else 89) else (if i.val < 95 then 83 else 91))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 32 else 33) else (if i.val < 99 then 34 else 35)) else (if i.val < 102 then (if i.val < 101 then 96 else 104) else (if i.val < 103 then 98 else 39))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 40 else 41) else (if i.val < 107 then 42 else 43)) else (if i.val < 110 then (if i.val < 109 then 97 else 45) else (if i.val < 111 then 99 else 47)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 116 else 66) else (if i.val < 115 then 118 else 74)) else (if i.val < 118 then (if i.val < 117 then 96 else 98) else (if i.val < 119 then 104 else 106))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 117 else 125) else (if i.val < 123 then 119 else 127)) else (if i.val < 126 then (if i.val < 125 then 32 else 34) else (if i.val < 127 then 40 else 127))))))) : Fin 128)
private def letters (i : Fin 128) : Fin 3 := ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 2 else 2)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 0) else (if i.val < 27 then 2 else 0)) else (if i.val < 30 then (if i.val < 29 then 2 else 2) else (if i.val < 31 then 2 else 2))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 0) else (if i.val < 35 then 0 else 0)) else (if i.val < 38 then (if i.val < 37 then 2 else 2) else (if i.val < 39 then 2 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 0) else (if i.val < 43 then 0 else 0)) else (if i.val < 46 then (if i.val < 45 then 2 else 0) else (if i.val < 47 then 2 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 2 else 1) else (if i.val < 51 then 2 else 1)) else (if i.val < 54 then (if i.val < 53 then 1 else 1) else (if i.val < 55 then 1 else 1))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 2 else 2) else (if i.val < 59 then 2 else 2)) else (if i.val < 62 then (if i.val < 61 then 1 else 1) else (if i.val < 63 then 1 else 1)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 1 else 1) else (if i.val < 67 then 1 else 1)) else (if i.val < 70 then (if i.val < 69 then 1 else 1) else (if i.val < 71 then 1 else 1))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 1 else 1) else (if i.val < 75 then 2 else 2)) else (if i.val < 78 then (if i.val < 77 then 1 else 1) else (if i.val < 79 then 1 else 1)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 1 else 1) else (if i.val < 83 then 1 else 1)) else (if i.val < 86 then (if i.val < 85 then 1 else 1) else (if i.val < 87 then 1 else 1))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 2 else 1) else (if i.val < 91 then 2 else 1)) else (if i.val < 94 then (if i.val < 93 then 2 else 2) else (if i.val < 95 then 2 else 2))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 1 else 1) else (if i.val < 99 then 1 else 1)) else (if i.val < 102 then (if i.val < 101 then 2 else 2) else (if i.val < 103 then 2 else 1))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 1 else 1) else (if i.val < 107 then 1 else 1)) else (if i.val < 110 then (if i.val < 109 then 2 else 1) else (if i.val < 111 then 2 else 1)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 2 else 0) else (if i.val < 115 then 2 else 0)) else (if i.val < 118 then (if i.val < 117 then 0 else 0) else (if i.val < 119 then 0 else 0))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 2 else 2) else (if i.val < 123 then 2 else 2)) else (if i.val < 126 then (if i.val < 125 then 0 else 0) else (if i.val < 127 then 0 else 0))))))) : Fin 3)

def normalCertificate : EncodedCayleyCertificate (binaryNormalRowEncoding normalGenerators) 128 where
  rows := rows
  identity := 127
  identity_eq := by decide +kernel
  next := next
  next_eq := (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))
  rank := rank
  parent i _ := parents i
  letter i hi := letters i
  parent_lt := (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))
  parent_next := (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

theorem normalRows_injective : Function.Injective normalCertificate.rows := by decide +kernel

theorem kernel_card : Nat.card kernel=128 := normalCertificate.card_closure normalRows_injective

theorem row_mem (i : Fin 128) : (⟨rows i⟩ : Source)∈kernel :=
  binaryNormalRow_mem normalCertificate i

private def posWitness (i : Fin 3) (j : Fin 3) : Fin 128 := ((if i.val < 1 then #[79,63,123] else (if i.val < 2 then #[42,63,123] else #[7,126,29])) : Array (Fin 128))[j.val]!
private def negWitness (i : Fin 3) (j : Fin 3) : Fin 128 := ((if i.val < 1 then #[79,63,123] else (if i.val < 2 then #[42,63,123] else #[7,119,29])) : Array (Fin 128))[j.val]!
private theorem pos_checked : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹=
    (⟨rows (posWitness i j)⟩ : Source) := by decide +kernel
private theorem neg_checked : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i=
    (⟨rows (negWitness i j)⟩ : Source) := by decide +kernel

instance normal : kernel.Normal := binaryNormal_of_generator_conjugates generators generators_full
  normalGenerators (fun i j => (pos_checked i j) ▸ row_mem (posWitness i j))
  (fun i j => (neg_checked i j) ▸ row_mem (negWitness i j))

private def representatives (i : Fin 1) : Source := ⟨(127 : Fin 128)⟩
private def quotientNext (i : Fin 1) (j : Fin 3) : Fin 1 := (#[0,0,0] : Array (Fin 1))[j.val]!
private def quotientPrev (i : Fin 1) (j : Fin 3) : Fin 1 := (#[0,0,0] : Array (Fin 1))[j.val]!
private def quotientParents (i : Fin 1) : Fin 1 := (0 : Fin 1)
private def quotientLetters (i : Fin 1) : Fin 3 := (0 : Fin 3)
private def stepWitness (i : Fin 1) (j : Fin 3) : Fin 128 := (#[63,123,42] : Array (Fin 128))[j.val]!
private theorem quotientStep_checked : ∀ i j,
    representatives (quotientNext i j)/(representatives i*generators j)=
      (⟨rows (stepWitness i j)⟩ : Source) := (by decide +kernel)

def cosets : BinaryNormalCosetCertificate generators kernel 1 where
  representatives := representatives
  identity := 0
  identity_mem := by
    have he : representatives 0=(⟨rows 127⟩ : Source) := by decide +kernel
    exact he ▸ row_mem 127
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
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def literalGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,1,0,3,6,5,4,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,1,0,3,6,5,4,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalNormalGenerators (k : Fin 3) : Equiv.Perm (Fin 8) :=
  (if k.val < 1 then literalGenerator0 else (if k.val < 2 then literalGenerator1 else literalGenerator2))

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin 3) :
    (BinaryMenuCayley8T35.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T35.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T35.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T35.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel

end N27

@[reducible] def states (i : Fin 28) : BinaryNormalState generators :=
  (if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then N0.state else (if i.val < 2 then N1.state else N2.state)) else (if i.val < 5 then (if i.val < 4 then N3.state else N4.state) else (if i.val < 6 then N5.state else N6.state))) else (if i.val < 10 then (if i.val < 8 then N7.state else (if i.val < 9 then N8.state else N9.state)) else (if i.val < 12 then (if i.val < 11 then N10.state else N11.state) else (if i.val < 13 then N12.state else N13.state)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then N14.state else (if i.val < 16 then N15.state else N16.state)) else (if i.val < 19 then (if i.val < 18 then N17.state else N18.state) else (if i.val < 20 then N19.state else N20.state))) else (if i.val < 24 then (if i.val < 22 then N21.state else (if i.val < 23 then N22.state else N23.state)) else (if i.val < 26 then (if i.val < 25 then N24.state else N25.state) else (if i.val < 27 then N26.state else N27.state)))))

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T35
