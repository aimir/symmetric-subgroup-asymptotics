import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T31

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T31

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,2,1,4,3,6,5,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,2,1,4,3,6,5,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 64) : Fin (8^8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 342391 else 358771) else (if i.val < 3 then 473431 else 489811)) else (if i.val < 6 then (if i.val < 5 then 1390711 else 1407091) else (if i.val < 7 then 1521751 else 1538131))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2206526 else 2222906) else (if i.val < 11 then 2337566 else 2353946)) else (if i.val < 14 then (if i.val < 13 then 3254846 else 3271226) else (if i.val < 15 then 3385886 else 3402266)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4988389 else 5004769) else (if i.val < 19 then 5119429 else 5135809)) else (if i.val < 22 then (if i.val < 21 then 6036709 else 6053089) else (if i.val < 23 then 6167749 else 6184129))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6852524 else 6868904) else (if i.val < 27 then 6983564 else 6999944)) else (if i.val < 30 then (if i.val < 29 then 7900844 else 7917224) else (if i.val < 31 then 8031884 else 8048264))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 8728951 else 8745331) else (if i.val < 35 then 8859991 else 8876371)) else (if i.val < 38 then (if i.val < 37 then 9777271 else 9793651) else (if i.val < 39 then 9908311 else 9924691))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10593086 else 10609466) else (if i.val < 43 then 10724126 else 10740506)) else (if i.val < 46 then (if i.val < 45 then 11641406 else 11657786) else (if i.val < 47 then 11772446 else 11788826)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 13374949 else 13391329) else (if i.val < 51 then 13505989 else 13522369)) else (if i.val < 54 then (if i.val < 53 then 14423269 else 14439649) else (if i.val < 55 then 14554309 else 14570689))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 15239084 else 15255464) else (if i.val < 59 then 15370124 else 15386504)) else (if i.val < 62 then (if i.val < 61 then 16287404 else 16303784) else (if i.val < 63 then 16418444 else 16434824))))))
private def ranks (i : Fin 64) : ℕ :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 39 else 46) else (if i.val < 3 then 27 else 33)) else (if i.val < 6 then (if i.val < 5 then 25 else 31) else (if i.val < 7 then 2 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 35 else 22) else (if i.val < 11 then 42 else 28)) else (if i.val < 14 then (if i.val < 13 then 24 else 3) else (if i.val < 15 then 30 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 48 else 13) else (if i.val < 19 then 15 else 7)) else (if i.val < 22 then (if i.val < 21 then 54 else 18) else (if i.val < 23 then 20 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 63 else 58) else (if i.val < 27 then 57 else 45)) else (if i.val < 30 then (if i.val < 29 then 55 else 21) else (if i.val < 31 then 17 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 53 else 59) else (if i.val < 35 then 40 else 47)) else (if i.val < 38 then (if i.val < 37 then 36 else 43) else (if i.val < 39 then 6 else 9))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 50 else 34) else (if i.val < 43 then 56 else 41)) else (if i.val < 46 then (if i.val < 45 then 37 else 8) else (if i.val < 47 then 44 else 11)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 60 else 23) else (if i.val < 51 then 26 else 14)) else (if i.val < 54 then (if i.val < 53 then 62 else 29) else (if i.val < 55 then 32 else 19))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 61 else 52) else (if i.val < 59 then 51 else 38)) else (if i.val < 62 then (if i.val < 61 then 49 else 16) else (if i.val < 63 then 12 else 0))))))
private def parents (i : Fin 64) : Fin 64 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 50 else 54) else (if i.val < 3 then 18 else 22)) else (if i.val < 6 then (if i.val < 5 then 51 else 55) else (if i.val < 7 then 63 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 62) else (if i.val < 11 then 53 else 30)) else (if i.val < 14 then (if i.val < 13 then 51 else 63) else (if i.val < 15 then 55 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 41 else 38) else (if i.val < 19 then 45 else 6)) else (if i.val < 22 then (if i.val < 21 then 43 else 39) else (if i.val < 23 then 47 else 7))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 42 else 46) else (if i.val < 27 then 10 else 14)) else (if i.val < 30 then (if i.val < 29 then 43 else 47) else (if i.val < 31 then 39 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 1) else (if i.val < 35 then 2 else 3)) else (if i.val < 38 then (if i.val < 37 then 49 else 53) else (if i.val < 39 then 6 else 7))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 8 else 9) else (if i.val < 43 then 10 else 11)) else (if i.val < 46 then (if i.val < 45 then 12 else 13) else (if i.val < 47 then 14 else 15)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 17) else (if i.val < 51 then 18 else 19)) else (if i.val < 54 then (if i.val < 53 then 20 else 21) else (if i.val < 55 then 22 else 23))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 40 else 44) else (if i.val < 59 then 8 else 12)) else (if i.val < 62 then (if i.val < 61 then 41 else 45) else (if i.val < 63 then 38 else 63))))))
private def letters (i : Fin 64) : Fin 3 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 2) else (if i.val < 3 then 2 else 2)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 2) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 1 else 2) else (if i.val < 15 then 1 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 2) else (if i.val < 19 then 1 else 2)) else (if i.val < 22 then (if i.val < 21 then 1 else 2) else (if i.val < 23 then 1 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 2) else (if i.val < 27 then 2 else 2)) else (if i.val < 30 then (if i.val < 29 then 2 else 2) else (if i.val < 31 then 1 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 0) else (if i.val < 35 then 0 else 0)) else (if i.val < 38 then (if i.val < 37 then 2 else 2) else (if i.val < 39 then 0 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 0) else (if i.val < 43 then 0 else 0)) else (if i.val < 46 then (if i.val < 45 then 0 else 0) else (if i.val < 47 then 0 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 0 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 2 else 2) else (if i.val < 59 then 2 else 2)) else (if i.val < 62 then (if i.val < 61 then 2 else 2) else (if i.val < 63 then 1 else 0))))))
private def nextRow (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[32,57,50] else #[33,25,54]) else (if i.val < 3 then #[34,61,18] else #[35,29,22])) else (if i.val < 6 then (if i.val < 5 then #[36,59,51] else #[37,27,55]) else (if i.val < 7 then #[38,63,19] else #[39,31,23]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[40,49,58] else #[41,17,62]) else (if i.val < 11 then #[42,53,26] else #[43,21,30])) else (if i.val < 14 then (if i.val < 13 then #[44,51,59] else #[45,19,63]) else (if i.val < 15 then #[46,55,27] else #[47,23,31])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[48,41,34] else #[49,9,38]) else (if i.val < 19 then #[50,45,2] else #[51,13,6])) else (if i.val < 22 then (if i.val < 21 then #[52,43,35] else #[53,11,39]) else (if i.val < 23 then #[54,47,3] else #[55,15,7]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[56,33,42] else #[57,1,46]) else (if i.val < 27 then #[58,37,10] else #[59,5,14])) else (if i.val < 30 then (if i.val < 29 then #[60,35,43] else #[61,3,47]) else (if i.val < 31 then #[62,39,11] else #[63,7,15]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,56,48] else #[1,24,52]) else (if i.val < 35 then #[2,60,16] else #[3,28,20])) else (if i.val < 38 then (if i.val < 37 then #[4,58,49] else #[5,26,53]) else (if i.val < 39 then #[6,62,17] else #[7,30,21]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[8,48,56] else #[9,16,60]) else (if i.val < 43 then #[10,52,24] else #[11,20,28])) else (if i.val < 46 then (if i.val < 45 then #[12,50,57] else #[13,18,61]) else (if i.val < 47 then #[14,54,25] else #[15,22,29])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[16,40,32] else #[17,8,36]) else (if i.val < 51 then #[18,44,0] else #[19,12,4])) else (if i.val < 54 then (if i.val < 53 then #[20,42,33] else #[21,10,37]) else (if i.val < 55 then #[22,46,1] else #[23,14,5]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[24,32,40] else #[25,0,44]) else (if i.val < 59 then #[26,36,8] else #[27,4,12])) else (if i.val < 62 then (if i.val < 61 then #[28,34,41] else #[29,2,45]) else (if i.val < 63 then #[30,38,9] else #[31,6,13])))))) : Array (Fin 64))[j.val]!
private def prevRow (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[32,57,50] else #[33,25,54]) else (if i.val < 3 then #[34,61,18] else #[35,29,22])) else (if i.val < 6 then (if i.val < 5 then #[36,59,51] else #[37,27,55]) else (if i.val < 7 then #[38,63,19] else #[39,31,23]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[40,49,58] else #[41,17,62]) else (if i.val < 11 then #[42,53,26] else #[43,21,30])) else (if i.val < 14 then (if i.val < 13 then #[44,51,59] else #[45,19,63]) else (if i.val < 15 then #[46,55,27] else #[47,23,31])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[48,41,34] else #[49,9,38]) else (if i.val < 19 then #[50,45,2] else #[51,13,6])) else (if i.val < 22 then (if i.val < 21 then #[52,43,35] else #[53,11,39]) else (if i.val < 23 then #[54,47,3] else #[55,15,7]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[56,33,42] else #[57,1,46]) else (if i.val < 27 then #[58,37,10] else #[59,5,14])) else (if i.val < 30 then (if i.val < 29 then #[60,35,43] else #[61,3,47]) else (if i.val < 31 then #[62,39,11] else #[63,7,15]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,56,48] else #[1,24,52]) else (if i.val < 35 then #[2,60,16] else #[3,28,20])) else (if i.val < 38 then (if i.val < 37 then #[4,58,49] else #[5,26,53]) else (if i.val < 39 then #[6,62,17] else #[7,30,21]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[8,48,56] else #[9,16,60]) else (if i.val < 43 then #[10,52,24] else #[11,20,28])) else (if i.val < 46 then (if i.val < 45 then #[12,50,57] else #[13,18,61]) else (if i.val < 47 then #[14,54,25] else #[15,22,29])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[16,40,32] else #[17,8,36]) else (if i.val < 51 then #[18,44,0] else #[19,12,4])) else (if i.val < 54 then (if i.val < 53 then #[20,42,33] else #[21,10,37]) else (if i.val < 55 then #[22,46,1] else #[23,14,5]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[24,32,40] else #[25,0,44]) else (if i.val < 59 then #[26,36,8] else #[27,4,12])) else (if i.val < 62 then (if i.val < 61 then #[28,34,41] else #[29,2,45]) else (if i.val < 63 then #[30,38,9] else #[31,6,13])))))) : Array (Fin 64))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T31
