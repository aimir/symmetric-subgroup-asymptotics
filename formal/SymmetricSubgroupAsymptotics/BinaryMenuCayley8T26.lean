import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T26

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T26

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,1,4,7,2,5,0,3] : Array (Fin 8))[x.val]!
  invFun x := (#[6,1,4,7,2,5,0,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 64) : Fin (8^8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 342391 else 489811) else (if i.val < 3 then 874993 else 989653)) else (if i.val < 6 then (if i.val < 5 then 1407091 else 1521751) else (if i.val < 7 then 1906933 else 2054353))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2206526 else 2353946) else (if i.val < 11 then 2739128 else 2853788)) else (if i.val < 14 then (if i.val < 13 then 3271226 else 3385886) else (if i.val < 15 then 3771068 else 3918488)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4488547 else 4603207) else (if i.val < 19 then 4988389 else 5135809)) else (if i.val < 22 then (if i.val < 21 then 5520487 else 5667907) else (if i.val < 23 then 6053089 else 6167749))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6352682 else 6467342) else (if i.val < 27 then 6852524 else 6999944)) else (if i.val < 30 then (if i.val < 29 then 7384622 else 7532042) else (if i.val < 31 then 7917224 else 8031884))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 8745331 else 8859991) else (if i.val < 35 then 9245173 else 9392593)) else (if i.val < 38 then (if i.val < 37 then 9777271 else 9924691) else (if i.val < 39 then 10309873 else 10424533))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10609466 else 10724126) else (if i.val < 43 then 11109308 else 11256728)) else (if i.val < 46 then (if i.val < 45 then 11641406 else 11788826) else (if i.val < 47 then 12174008 else 12288668)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 12858727 else 13006147) else (if i.val < 51 then 13391329 else 13505989)) else (if i.val < 54 then (if i.val < 53 then 13923427 else 14038087) else (if i.val < 55 then 14423269 else 14570689))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 14722862 else 14870282) else (if i.val < 59 then 15255464 else 15370124)) else (if i.val < 62 then (if i.val < 61 then 15787562 else 15902222) else (if i.val < 63 then 16287404 else 16434824))))))
private def ranks (i : Fin 64) : ℕ :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 17) else (if i.val < 3 then 46 else 19)) else (if i.val < 6 then (if i.val < 5 then 30 else 15) else (if i.val < 7 then 61 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 59 else 4) else (if i.val < 11 then 58 else 31)) else (if i.val < 14 then (if i.val < 13 then 18 else 33) else (if i.val < 15 then 22 else 29)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 11 else 38) else (if i.val < 19 then 23 else 42)) else (if i.val < 22 then (if i.val < 21 then 50 else 32) else (if i.val < 23 then 24 else 35))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 37 else 3) else (if i.val < 27 then 26 else 25)) else (if i.val < 30 then (if i.val < 29 then 36 else 21) else (if i.val < 31 then 62 else 2))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 53 else 6) else (if i.val < 35 then 47 else 7)) else (if i.val < 38 then (if i.val < 37 then 52 else 34) else (if i.val < 39 then 60 else 5))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 41 else 12) else (if i.val < 43 then 40 else 13)) else (if i.val < 46 then (if i.val < 45 then 39 else 14) else (if i.val < 47 then 44 else 51)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 27 else 56) else (if i.val < 51 then 9 else 55)) else (if i.val < 54 then (if i.val < 53 then 28 else 54) else (if i.val < 55 then 45 else 20))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 10) else (if i.val < 59 then 48 else 43)) else (if i.val < 62 then (if i.val < 61 then 16 else 8) else (if i.val < 63 then 49 else 0))))))
private def parents (i : Fin 64) : Fin 64 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 32 else 33) else (if i.val < 3 then 27 else 35)) else (if i.val < 6 then (if i.val < 5 then 43 else 39) else (if i.val < 7 then 58 else 63))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 40 else 7) else (if i.val < 11 then 42 else 43)) else (if i.val < 14 then (if i.val < 13 then 35 else 45) else (if i.val < 15 then 50 else 41)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 12) else (if i.val < 19 then 50 else 29)) else (if i.val < 22 then (if i.val < 21 then 52 else 45) else (if i.val < 23 then 57 else 60))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 63) else (if i.val < 27 then 16 else 57)) else (if i.val < 30 then (if i.val < 29 then 60 else 61) else (if i.val < 31 then 62 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 11 else 7) else (if i.val < 35 then 26 else 31)) else (if i.val < 38 then (if i.val < 37 then 4 else 5) else (if i.val < 39 then 59 else 7))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 3 else 9) else (if i.val < 43 then 12 else 9)) else (if i.val < 46 then (if i.val < 45 then 12 else 39) else (if i.val < 47 then 14 else 15)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 13) else (if i.val < 51 then 25 else 21)) else (if i.val < 54 then (if i.val < 53 then 41 else 21) else (if i.val < 55 then 22 else 61))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 24 else 25) else (if i.val < 59 then 26 else 29)) else (if i.val < 62 then (if i.val < 61 then 33 else 31) else (if i.val < 63 then 48 else 63))))))
private def letters (i : Fin 64) : Fin 3 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 0) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 0 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 1 else 0)) else (if i.val < 22 then (if i.val < 21 then 1 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 2) else (if i.val < 27 then 0 else 2)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 1 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 2) else (if i.val < 35 then 0 else 0)) else (if i.val < 38 then (if i.val < 37 then 1 else 1) else (if i.val < 39 then 0 else 1))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 1) else (if i.val < 43 then 2 else 2)) else (if i.val < 46 then (if i.val < 45 then 1 else 0) else (if i.val < 47 then 1 else 1)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 1 else 0) else (if i.val < 51 then 0 else 2)) else (if i.val < 54 then (if i.val < 53 then 0 else 1) else (if i.val < 55 then 1 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 1 else 1) else (if i.val < 59 then 1 else 2)) else (if i.val < 62 then (if i.val < 61 then 0 else 2) else (if i.val < 63 then 0 else 0))))))
private def nextRow (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[56,32,38] else #[24,33,35]) else (if i.val < 3 then #[8,34,32] else #[40,35,37])) else (if i.val < 6 then (if i.val < 5 then #[25,36,34] else #[57,37,39]) else (if i.val < 7 then #[41,38,36] else #[9,39,33]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[48,40,46] else #[16,41,43]) else (if i.val < 11 then #[0,42,40] else #[32,43,45])) else (if i.val < 14 then (if i.val < 13 then #[17,44,42] else #[49,45,47]) else (if i.val < 15 then #[33,46,44] else #[1,47,41])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[26,48,50] else #[58,49,55]) else (if i.val < 19 then #[42,50,52] else #[10,51,49])) else (if i.val < 22 then (if i.val < 21 then #[59,52,54] else #[27,53,51]) else (if i.val < 23 then #[11,54,48] else #[43,55,53]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[18,56,58] else #[50,57,63]) else (if i.val < 27 then #[34,58,60] else #[2,59,57])) else (if i.val < 30 then (if i.val < 29 then #[51,60,62] else #[19,61,59]) else (if i.val < 31 then #[3,62,56] else #[35,63,61]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[28,0,2] else #[60,1,7]) else (if i.val < 35 then #[44,2,4] else #[12,3,1])) else (if i.val < 38 then (if i.val < 37 then #[61,4,6] else #[29,5,3]) else (if i.val < 39 then #[13,6,0] else #[45,7,5]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[20,8,10] else #[52,9,15]) else (if i.val < 43 then #[36,10,12] else #[4,11,9])) else (if i.val < 46 then (if i.val < 45 then #[53,12,14] else #[21,13,11]) else (if i.val < 47 then #[5,14,8] else #[37,15,13])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[62,16,22] else #[30,17,19]) else (if i.val < 51 then #[14,18,16] else #[46,19,21])) else (if i.val < 54 then (if i.val < 53 then #[31,20,18] else #[63,21,23]) else (if i.val < 55 then #[47,22,20] else #[15,23,17]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[54,24,30] else #[22,25,27]) else (if i.val < 59 then #[6,26,24] else #[38,27,29])) else (if i.val < 62 then (if i.val < 61 then #[23,28,26] else #[55,29,31]) else (if i.val < 63 then #[39,30,28] else #[7,31,25])))))) : Array (Fin 64))[j.val]!
private def prevRow (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[10,32,38] else #[15,33,35]) else (if i.val < 3 then #[27,34,32] else #[30,35,37])) else (if i.val < 6 then (if i.val < 5 then #[43,36,34] else #[46,37,39]) else (if i.val < 7 then #[58,38,36] else #[63,39,33]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[2,40,46] else #[7,41,43]) else (if i.val < 11 then #[19,42,40] else #[22,43,45])) else (if i.val < 14 then (if i.val < 13 then #[35,44,42] else #[38,45,47]) else (if i.val < 15 then #[50,46,44] else #[55,47,41])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[9,48,50] else #[12,49,55]) else (if i.val < 19 then #[24,50,52] else #[29,51,49])) else (if i.val < 22 then (if i.val < 21 then #[40,52,54] else #[45,53,51]) else (if i.val < 23 then #[57,54,48] else #[60,55,53]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[1,56,58] else #[4,57,63]) else (if i.val < 27 then #[16,58,60] else #[21,59,57])) else (if i.val < 30 then (if i.val < 29 then #[32,60,62] else #[37,61,59]) else (if i.val < 31 then #[49,62,56] else #[52,63,61]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[11,0,2] else #[14,1,7]) else (if i.val < 35 then #[26,2,4] else #[31,3,1])) else (if i.val < 38 then (if i.val < 37 then #[42,4,6] else #[47,5,3]) else (if i.val < 39 then #[59,6,0] else #[62,7,5]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[3,8,10] else #[6,9,15]) else (if i.val < 43 then #[18,10,12] else #[23,11,9])) else (if i.val < 46 then (if i.val < 45 then #[34,12,14] else #[39,13,11]) else (if i.val < 47 then #[51,14,8] else #[54,15,13])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[8,16,22] else #[13,17,19]) else (if i.val < 51 then #[25,18,16] else #[28,19,21])) else (if i.val < 54 then (if i.val < 53 then #[41,20,18] else #[44,21,23]) else (if i.val < 55 then #[56,22,20] else #[61,23,17]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[0,24,30] else #[5,25,27]) else (if i.val < 59 then #[17,26,24] else #[20,27,29])) else (if i.val < 62 then (if i.val < 61 then #[33,28,26] else #[36,29,31]) else (if i.val < 63 then #[48,30,28] else #[53,31,25])))))) : Array (Fin 64))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T26
