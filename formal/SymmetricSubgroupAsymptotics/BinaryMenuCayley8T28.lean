import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T28

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T28

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,1,0,3,6,5,4,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,1,0,3,6,5,4,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 64) : Fin (8^8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 358771 else 473431) else (if i.val < 3 then 874993 else 989653)) else (if i.val < 6 then (if i.val < 5 then 1390711 else 1538131) else (if i.val < 7 then 1906933 else 2054353))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2206526 else 2353946) else (if i.val < 11 then 2722748 else 2870168)) else (if i.val < 14 then (if i.val < 13 then 3271226 else 3385886) else (if i.val < 15 then 3787448 else 3902108)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4488547 else 4603207) else (if i.val < 19 then 5004769 else 5119429)) else (if i.val < 22 then (if i.val < 21 then 5520487 else 5667907) else (if i.val < 23 then 6036709 else 6184129))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6336302 else 6483722) else (if i.val < 27 then 6852524 else 6999944)) else (if i.val < 30 then (if i.val < 29 then 7401002 else 7515662) else (if i.val < 31 then 7917224 else 8031884))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 8728951 else 8876371) else (if i.val < 35 then 9245173 else 9392593)) else (if i.val < 38 then (if i.val < 37 then 9793651 else 9908311) else (if i.val < 39 then 10309873 else 10424533))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10609466 else 10724126) else (if i.val < 43 then 11125688 else 11240348)) else (if i.val < 46 then (if i.val < 45 then 11641406 else 11788826) else (if i.val < 47 then 12157628 else 12305048)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 12858727 else 13006147) else (if i.val < 51 then 13374949 else 13522369)) else (if i.val < 54 then (if i.val < 53 then 13923427 else 14038087) else (if i.val < 55 then 14439649 else 14554309))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 14739242 else 14853902) else (if i.val < 59 then 15255464 else 15370124)) else (if i.val < 62 then (if i.val < 61 then 15771182 else 15918602) else (if i.val < 63 then 16287404 else 16434824))))))
private def ranks (i : Fin 64) : ℕ :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 14 else 32) else (if i.val < 3 then 8 else 13)) else (if i.val < 6 then (if i.val < 5 then 21 else 9) else (if i.val < 7 then 5 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 10) else (if i.val < 11 then 41 else 20)) else (if i.val < 14 then (if i.val < 13 then 24 else 44) else (if i.val < 15 then 43 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 48) else (if i.val < 19 then 18 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 19) else (if i.val < 23 then 17 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 34 else 23) else (if i.val < 27 then 50 else 42)) else (if i.val < 30 then (if i.val < 29 then 46 else 57) else (if i.val < 31 then 54 else 47))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 61 else 49) else (if i.val < 35 then 60 else 62)) else (if i.val < 38 then (if i.val < 37 then 59 else 63) else (if i.val < 39 then 51 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 33 else 15) else (if i.val < 43 then 55 else 36)) else (if i.val < 46 then (if i.val < 45 then 35 else 56) else (if i.val < 47 then 53 else 31)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 45 else 30) else (if i.val < 51 then 29 else 52)) else (if i.val < 54 then (if i.val < 53 then 37 else 58) else (if i.val < 55 then 28 else 12))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 6 else 11) else (if i.val < 59 then 1 else 27)) else (if i.val < 62 then (if i.val < 61 then 4 else 2) else (if i.val < 63 then 16 else 0))))))
private def parents (i : Fin 64) : Fin 64 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 6 else 3) else (if i.val < 3 then 7 else 6)) else (if i.val < 6 then (if i.val < 5 then 2 else 7) else (if i.val < 7 then 58 else 63))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 7) else (if i.val < 11 then 18 else 23)) else (if i.val < 14 then (if i.val < 13 then 9 else 11) else (if i.val < 15 then 11 else 9)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 12) else (if i.val < 19 then 23 else 22)) else (if i.val < 22 then (if i.val < 21 then 18 else 23) else (if i.val < 23 then 56 else 61))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 5) else (if i.val < 27 then 16 else 21)) else (if i.val < 30 then (if i.val < 29 then 25 else 24) else (if i.val < 31 then 49 else 25))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 10 else 15) else (if i.val < 35 then 39 else 31)) else (if i.val < 38 then (if i.val < 37 then 43 else 46) else (if i.val < 39 then 59 else 62))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 3 else 6) else (if i.val < 43 then 47 else 41)) else (if i.val < 46 then (if i.val < 45 then 41 else 47) else (if i.val < 47 then 50 else 55)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 8 else 55) else (if i.val < 51 then 55 else 54)) else (if i.val < 54 then (if i.val < 53 then 41 else 44) else (if i.val < 55 then 57 else 60))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 61 else 60) else (if i.val < 59 then 63 else 57)) else (if i.val < 62 then (if i.val < 61 then 58 else 63) else (if i.val < 63 then 56 else 63))))))
private def letters (i : Fin 64) : Fin 3 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 2 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 2) else (if i.val < 11 then 2 else 2)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 0 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 1 else 1) else (if i.val < 23 then 2 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 2) else (if i.val < 27 then 2 else 2)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 2 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 2 else 2) else (if i.val < 35 then 0 else 2)) else (if i.val < 38 then (if i.val < 37 then 2 else 2) else (if i.val < 39 then 2 else 2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 2 else 2) else (if i.val < 43 then 0 else 1)) else (if i.val < 46 then (if i.val < 45 then 0 else 1) else (if i.val < 47 then 2 else 2)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 2 else 1) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 2 else 2) else (if i.val < 55 then 2 else 2))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 0) else (if i.val < 59 then 0 else 1)) else (if i.val < 62 then (if i.val < 61 then 1 else 1) else (if i.val < 63 then 1 else 0))))))
private def nextRow (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,6,24] else #[4,3,56]) else (if i.val < 3 then #[7,4,8] else #[6,1,40])) else (if i.val < 6 then (if i.val < 5 then #[1,2,57] else #[0,7,25]) else (if i.val < 7 then #[3,0,41] else #[2,5,9]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,10,48] else #[12,15,16]) else (if i.val < 11 then #[15,8,32] else #[14,13,0])) else (if i.val < 14 then (if i.val < 13 then #[9,14,17] else #[8,11,49]) else (if i.val < 15 then #[11,12,1] else #[10,9,33])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,22,26] else #[20,19,58]) else (if i.val < 19 then #[23,20,10] else #[22,17,42])) else (if i.val < 22 then (if i.val < 21 then #[17,18,59] else #[16,23,27]) else (if i.val < 23 then #[19,16,43] else #[18,21,11]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,26,50] else #[28,31,18]) else (if i.val < 27 then #[31,24,34] else #[30,29,2])) else (if i.val < 30 then (if i.val < 29 then #[25,30,19] else #[24,27,51]) else (if i.val < 31 then #[27,28,3] else #[26,25,35]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[37,34,60] else #[36,39,28]) else (if i.val < 35 then #[39,32,44] else #[38,37,12])) else (if i.val < 38 then (if i.val < 37 then #[33,38,29] else #[32,35,61]) else (if i.val < 39 then #[35,36,13] else #[34,33,45]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[45,46,20] else #[44,43,52]) else (if i.val < 43 then #[47,44,4] else #[46,41,36])) else (if i.val < 46 then (if i.val < 45 then #[41,42,53] else #[40,47,21]) else (if i.val < 47 then #[43,40,37] else #[42,45,5])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[53,50,62] else #[52,55,30]) else (if i.val < 51 then #[55,48,46] else #[54,53,14])) else (if i.val < 54 then (if i.val < 53 then #[49,54,31] else #[48,51,63]) else (if i.val < 55 then #[51,52,15] else #[50,49,47]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[61,62,22] else #[60,59,54]) else (if i.val < 59 then #[63,60,6] else #[62,57,38])) else (if i.val < 62 then (if i.val < 61 then #[57,58,55] else #[56,63,23]) else (if i.val < 63 then #[59,56,39] else #[58,61,7])))))) : Array (Fin 64))[j.val]!
private def prevRow (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,6,11] else #[4,3,14]) else (if i.val < 3 then #[7,4,27] else #[6,1,30])) else (if i.val < 6 then (if i.val < 5 then #[1,2,42] else #[0,7,47]) else (if i.val < 7 then #[3,0,58] else #[2,5,63]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,10,2] else #[12,15,7]) else (if i.val < 11 then #[15,8,18] else #[14,13,23])) else (if i.val < 14 then (if i.val < 13 then #[9,14,35] else #[8,11,38]) else (if i.val < 15 then #[11,12,51] else #[10,9,54])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,22,9] else #[20,19,12]) else (if i.val < 19 then #[23,20,25] else #[22,17,28])) else (if i.val < 22 then (if i.val < 21 then #[17,18,40] else #[16,23,45]) else (if i.val < 23 then #[19,16,56] else #[18,21,61]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,26,0] else #[28,31,5]) else (if i.val < 27 then #[31,24,16] else #[30,29,21])) else (if i.val < 30 then (if i.val < 29 then #[25,30,33] else #[24,27,36]) else (if i.val < 31 then #[27,28,49] else #[26,25,52]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[37,34,10] else #[36,39,15]) else (if i.val < 35 then #[39,32,26] else #[38,37,31])) else (if i.val < 38 then (if i.val < 37 then #[33,38,43] else #[32,35,46]) else (if i.val < 39 then #[35,36,59] else #[34,33,62]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[45,46,3] else #[44,43,6]) else (if i.val < 43 then #[47,44,19] else #[46,41,22])) else (if i.val < 46 then (if i.val < 45 then #[41,42,34] else #[40,47,39]) else (if i.val < 47 then #[43,40,50] else #[42,45,55])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[53,50,8] else #[52,55,13]) else (if i.val < 51 then #[55,48,24] else #[54,53,29])) else (if i.val < 54 then (if i.val < 53 then #[49,54,41] else #[48,51,44]) else (if i.val < 55 then #[51,52,57] else #[50,49,60]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[61,62,1] else #[60,59,4]) else (if i.val < 59 then #[63,60,17] else #[62,57,20])) else (if i.val < 62 then (if i.val < 61 then #[57,58,32] else #[56,63,37]) else (if i.val < 63 then #[59,56,48] else #[58,61,53])))))) : Array (Fin 64))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T28
