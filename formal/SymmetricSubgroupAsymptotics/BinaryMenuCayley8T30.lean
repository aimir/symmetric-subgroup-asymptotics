import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T30

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T30

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,1,0,7,6,5,4,3] : Array (Fin 8))[x.val]!
  invFun x := (#[2,1,0,7,6,5,4,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 64) : Fin (8^8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 358771 else 473431) else (if i.val < 3 then 858613 else 1006033)) else (if i.val < 6 then (if i.val < 5 then 1390711 else 1538131) else (if i.val < 7 then 1923313 else 2037973))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2206526 else 2353946) else (if i.val < 11 then 2739128 else 2853788)) else (if i.val < 14 then (if i.val < 13 then 3271226 else 3385886) else (if i.val < 15 then 3771068 else 3918488)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4472167 else 4619587) else (if i.val < 19 then 5004769 else 5119429)) else (if i.val < 22 then (if i.val < 21 then 5536867 else 5651527) else (if i.val < 23 then 6036709 else 6184129))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6352682 else 6467342) else (if i.val < 27 then 6852524 else 6999944)) else (if i.val < 30 then (if i.val < 29 then 7384622 else 7532042) else (if i.val < 31 then 7917224 else 8031884))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 8728951 else 8876371) else (if i.val < 35 then 9261553 else 9376213)) else (if i.val < 38 then (if i.val < 37 then 9793651 else 9908311) else (if i.val < 39 then 10293493 else 10440913))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10609466 else 10724126) else (if i.val < 43 then 11109308 else 11256728)) else (if i.val < 46 then (if i.val < 45 then 11641406 else 11788826) else (if i.val < 47 then 12174008 else 12288668)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 12875107 else 12989767) else (if i.val < 51 then 13374949 else 13522369)) else (if i.val < 54 then (if i.val < 53 then 13907047 else 14054467) else (if i.val < 55 then 14439649 else 14554309))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 14722862 else 14870282) else (if i.val < 59 then 15255464 else 15370124)) else (if i.val < 62 then (if i.val < 61 then 15787562 else 15902222) else (if i.val < 63 then 16287404 else 16434824))))))
private def ranks (i : Fin 64) : ℕ :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 50) else (if i.val < 3 then 5 else 3)) else (if i.val < 6 then (if i.val < 5 then 61 else 45) else (if i.val < 7 then 8 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 46 else 24) else (if i.val < 11 then 36 else 54)) else (if i.val < 14 then (if i.val < 13 then 10 else 22) else (if i.val < 15 then 43 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 51 else 30) else (if i.val < 19 then 18 else 39)) else (if i.val < 22 then (if i.val < 21 then 49 else 26) else (if i.val < 23 then 17 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6 else 11) else (if i.val < 27 then 60 else 44)) else (if i.val < 30 then (if i.val < 29 then 4 else 2) else (if i.val < 31 then 56 else 48))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 14 else 32) else (if i.val < 35 then 53 else 38)) else (if i.val < 38 then (if i.val < 37 then 21 else 9) else (if i.val < 39 then 62 else 63))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 58 else 35) else (if i.val < 43 then 55 else 31)) else (if i.val < 46 then (if i.val < 45 then 15 else 33) else (if i.val < 47 then 25 else 41)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 40 else 37) else (if i.val < 51 then 29 else 52)) else (if i.val < 54 then (if i.val < 53 then 42 else 19) else (if i.val < 55 then 28 else 12))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 34 else 23) else (if i.val < 59 then 1 else 27)) else (if i.val < 62 then (if i.val < 61 then 47 else 59) else (if i.val < 63 then 16 else 0))))))
private def parents (i : Fin 64) : Fin 64 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 43 else 46) else (if i.val < 3 then 58 else 63)) else (if i.val < 6 then (if i.val < 5 then 10 else 15) else (if i.val < 7 then 3 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 12) else (if i.val < 11 then 44 else 54)) else (if i.val < 14 then (if i.val < 13 then 3 else 6) else (if i.val < 15 then 18 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 55) else (if i.val < 19 then 23 else 22)) else (if i.val < 22 then (if i.val < 21 then 9 else 12) else (if i.val < 23 then 24 else 29))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 29 else 28) else (if i.val < 27 then 56 else 53)) else (if i.val < 30 then (if i.val < 29 then 58 else 63) else (if i.val < 31 then 17 else 57))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 2 else 7) else (if i.val < 35 then 59 else 62)) else (if i.val < 38 then (if i.val < 37 then 6 else 3) else (if i.val < 39 then 35 else 5))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 45 else 44) else (if i.val < 43 then 50 else 55)) else (if i.val < 46 then (if i.val < 45 then 2 else 7) else (if i.val < 47 then 12 else 22)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 22 else 44) else (if i.val < 51 then 55 else 21)) else (if i.val < 54 then (if i.val < 53 then 18 else 23) else (if i.val < 55 then 25 else 28))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 32 else 37) else (if i.val < 59 then 63 else 25)) else (if i.val < 62 then (if i.val < 61 then 57 else 56) else (if i.val < 63 then 24 else 63))))))
private def letters (i : Fin 64) : Fin 3 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 2) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 2 else 2) else (if i.val < 15 then 2 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 1) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 2 else 2) else (if i.val < 23 then 2 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 1 else 2)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 2 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 1 else 1) else (if i.val < 35 then 2 else 2)) else (if i.val < 38 then (if i.val < 37 then 1 else 1) else (if i.val < 39 then 0 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 0) else (if i.val < 43 then 2 else 2)) else (if i.val < 46 then (if i.val < 45 then 2 else 2) else (if i.val < 47 then 1 else 2)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 1 else 2) else (if i.val < 51 then 0 else 1)) else (if i.val < 54 then (if i.val < 53 then 1 else 1) else (if i.val < 55 then 2 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 2 else 2) else (if i.val < 59 then 0 else 1)) else (if i.val < 62 then (if i.val < 61 then 0 else 0) else (if i.val < 63 then 1 else 0))))))
private def nextRow (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,38,28] else #[4,35,60]) else (if i.val < 3 then #[7,32,44] else #[6,37,12])) else (if i.val < 6 then (if i.val < 5 then #[1,34,61] else #[0,39,29]) else (if i.val < 7 then #[3,36,13] else #[2,33,45]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,42,52] else #[12,47,20]) else (if i.val < 11 then #[15,44,4] else #[14,41,36])) else (if i.val < 14 then (if i.val < 13 then #[9,46,21] else #[8,43,53]) else (if i.val < 15 then #[11,40,37] else #[10,45,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,50,62] else #[20,55,30]) else (if i.val < 19 then #[23,52,14] else #[22,49,46])) else (if i.val < 22 then (if i.val < 21 then #[17,54,31] else #[16,51,63]) else (if i.val < 23 then #[19,48,47] else #[18,53,15]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,62,22] else #[28,59,54]) else (if i.val < 27 then #[31,56,38] else #[30,61,6])) else (if i.val < 30 then (if i.val < 29 then #[25,58,55] else #[24,63,23]) else (if i.val < 31 then #[27,60,7] else #[26,57,39]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[37,2,56] else #[36,7,24]) else (if i.val < 35 then #[39,4,8] else #[38,1,40])) else (if i.val < 38 then (if i.val < 37 then #[33,6,25] else #[32,3,57]) else (if i.val < 39 then #[35,0,41] else #[34,5,9]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[45,14,16] else #[44,11,48]) else (if i.val < 43 then #[47,8,32] else #[46,13,0])) else (if i.val < 46 then (if i.val < 45 then #[41,10,49] else #[40,15,17]) else (if i.val < 47 then #[43,12,1] else #[42,9,33])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[53,22,26] else #[52,19,58]) else (if i.val < 51 then #[55,16,42] else #[54,21,10])) else (if i.val < 54 then (if i.val < 53 then #[49,18,59] else #[48,23,27]) else (if i.val < 55 then #[51,20,11] else #[50,17,43]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[61,26,50] else #[60,31,18]) else (if i.val < 59 then #[63,28,2] else #[62,25,34])) else (if i.val < 62 then (if i.val < 61 then #[57,30,19] else #[56,27,51]) else (if i.val < 63 then #[59,24,35] else #[58,29,3])))))) : Array (Fin 64))[j.val]!
private def prevRow (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,38,43] else #[4,35,46]) else (if i.val < 3 then #[7,32,58] else #[6,37,63])) else (if i.val < 6 then (if i.val < 5 then #[1,34,10] else #[0,39,15]) else (if i.val < 7 then #[3,36,27] else #[2,33,30]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,42,34] else #[12,47,39]) else (if i.val < 11 then #[15,44,51] else #[14,41,54])) else (if i.val < 14 then (if i.val < 13 then #[9,46,3] else #[8,43,6]) else (if i.val < 15 then #[11,40,18] else #[10,45,23])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,50,40] else #[20,55,45]) else (if i.val < 19 then #[23,52,57] else #[22,49,60])) else (if i.val < 22 then (if i.val < 21 then #[17,54,9] else #[16,51,12]) else (if i.val < 23 then #[19,48,24] else #[18,53,29]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,62,33] else #[28,59,36]) else (if i.val < 27 then #[31,56,48] else #[30,61,53])) else (if i.val < 30 then (if i.val < 29 then #[25,58,0] else #[24,63,5]) else (if i.val < 31 then #[27,60,17] else #[26,57,20]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[37,2,42] else #[36,7,47]) else (if i.val < 35 then #[39,4,59] else #[38,1,62])) else (if i.val < 38 then (if i.val < 37 then #[33,6,11] else #[32,3,14]) else (if i.val < 39 then #[35,0,26] else #[34,5,31]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[45,14,35] else #[44,11,38]) else (if i.val < 43 then #[47,8,50] else #[46,13,55])) else (if i.val < 46 then (if i.val < 45 then #[41,10,2] else #[40,15,7]) else (if i.val < 47 then #[43,12,19] else #[42,9,22])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[53,22,41] else #[52,19,44]) else (if i.val < 51 then #[55,16,56] else #[54,21,61])) else (if i.val < 54 then (if i.val < 53 then #[49,18,8] else #[48,23,13]) else (if i.val < 55 then #[51,20,25] else #[50,17,28]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[61,26,32] else #[60,31,37]) else (if i.val < 59 then #[63,28,49] else #[62,25,52])) else (if i.val < 62 then (if i.val < 61 then #[57,30,1] else #[56,27,4]) else (if i.val < 63 then #[59,24,16] else #[58,29,21])))))) : Array (Fin 64))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 64,
    i ≠ 63 → ranks (parents i) < ranks i := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
private theorem parent_next_checked : ∀ i : Fin 64,
    i ≠ 63 → nextRow (parents i) (letters i) = i := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 64 where
  rows := codes
  identity := 63
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (Fin.addCases (m := 31) (n := 32) (Fin.addCases (m := 15) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 64 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 64) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 64 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T30
