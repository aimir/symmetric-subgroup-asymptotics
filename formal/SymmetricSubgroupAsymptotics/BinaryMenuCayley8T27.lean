import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T27

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T27

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 64) : Fin (8^8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 858613 else 874993) else (if i.val < 3 then 989653 else 1006033)) else (if i.val < 6 then (if i.val < 5 then 1906933 else 1923313) else (if i.val < 7 then 2037973 else 2054353))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2206526 else 2222906) else (if i.val < 11 then 2337566 else 2353946)) else (if i.val < 14 then (if i.val < 13 then 3254846 else 3271226) else (if i.val < 15 then 3385886 else 3402266)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 4472167 else 4488547) else (if i.val < 19 then 4603207 else 4619587)) else (if i.val < 22 then (if i.val < 21 then 5520487 else 5536867) else (if i.val < 23 then 5651527 else 5667907))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6852524 else 6868904) else (if i.val < 27 then 6983564 else 6999944)) else (if i.val < 30 then (if i.val < 29 then 7900844 else 7917224) else (if i.val < 31 then 8031884 else 8048264))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 9245173 else 9261553) else (if i.val < 35 then 9376213 else 9392593)) else (if i.val < 38 then (if i.val < 37 then 10293493 else 10309873) else (if i.val < 39 then 10424533 else 10440913))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10593086 else 10609466) else (if i.val < 43 then 10724126 else 10740506)) else (if i.val < 46 then (if i.val < 45 then 11641406 else 11657786) else (if i.val < 47 then 11772446 else 11788826)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 12858727 else 12875107) else (if i.val < 51 then 12989767 else 13006147)) else (if i.val < 54 then (if i.val < 53 then 13907047 else 13923427) else (if i.val < 55 then 14038087 else 14054467))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 15239084 else 15255464) else (if i.val < 59 then 15370124 else 15386504)) else (if i.val < 62 then (if i.val < 61 then 16287404 else 16303784) else (if i.val < 63 then 16418444 else 16434824))))))
private def ranks (i : Fin 64) : ℕ :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 39) else (if i.val < 3 then 38 else 2)) else (if i.val < 6 then (if i.val < 5 then 54 else 45) else (if i.val < 7 then 44 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 8) else (if i.val < 11 then 60 else 11)) else (if i.val < 14 then (if i.val < 13 then 50 else 5) else (if i.val < 15 then 55 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 28) else (if i.val < 19 then 16 else 20)) else (if i.val < 22 then (if i.val < 21 then 15 else 19) else (if i.val < 23 then 10 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 51 else 43) else (if i.val < 27 then 42 else 33)) else (if i.val < 30 then (if i.val < 29 then 41 else 32) else (if i.val < 31 then 30 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 56 else 48) else (if i.val < 35 then 47 else 4)) else (if i.val < 38 then (if i.val < 37 then 59 else 53) else (if i.val < 39 then 52 else 6))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 62 else 14) else (if i.val < 43 then 63 else 18)) else (if i.val < 46 then (if i.val < 45 then 58 else 9) else (if i.val < 47 then 61 else 12)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 34 else 40) else (if i.val < 51 then 25 else 31)) else (if i.val < 54 then (if i.val < 53 then 23 else 29) else (if i.val < 55 then 17 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 37) else (if i.val < 59 then 36 else 27)) else (if i.val < 62 then (if i.val < 61 then 35 else 26) else (if i.val < 63 then 24 else 0))))))
private def parents (i : Fin 64) : Fin 64 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 59) else (if i.val < 3 then 61 else 63)) else (if i.val < 6 then (if i.val < 5 then 25 else 27) else (if i.val < 7 then 29 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 33 else 35) else (if i.val < 11 then 37 else 39)) else (if i.val < 14 then (if i.val < 13 then 1 else 3) else (if i.val < 15 then 5 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 41 else 43) else (if i.val < 19 then 45 else 47)) else (if i.val < 22 then (if i.val < 21 then 9 else 11) else (if i.val < 23 then 13 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 51) else (if i.val < 27 then 53 else 55)) else (if i.val < 30 then (if i.val < 29 then 17 else 19) else (if i.val < 31 then 21 else 63))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 56 else 58) else (if i.val < 35 then 60 else 3)) else (if i.val < 38 then (if i.val < 37 then 24 else 26) else (if i.val < 39 then 28 else 7))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 32 else 9) else (if i.val < 43 then 36 else 11)) else (if i.val < 46 then (if i.val < 45 then 0 else 13) else (if i.val < 47 then 4 else 15)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 17) else (if i.val < 51 then 18 else 19)) else (if i.val < 54 then (if i.val < 53 then 20 else 21) else (if i.val < 55 then 22 else 23))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 48 else 50) else (if i.val < 59 then 52 else 54)) else (if i.val < 62 then (if i.val < 61 then 16 else 18) else (if i.val < 63 then 20 else 63))))))
private def letters (i : Fin 64) : Fin 2 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 1) else (if i.val < 19 then 1 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 1) else (if i.val < 23 then 1 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 1) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 1 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 1 else 1) else (if i.val < 35 then 1 else 0)) else (if i.val < 38 then (if i.val < 37 then 1 else 1) else (if i.val < 39 then 1 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 1 else 0) else (if i.val < 43 then 1 else 0)) else (if i.val < 46 then (if i.val < 45 then 1 else 0) else (if i.val < 47 then 1 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 0 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 1 else 1) else (if i.val < 59 then 1 else 1)) else (if i.val < 62 then (if i.val < 61 then 1 else 1) else (if i.val < 63 then 1 else 0))))))
private def nextRow (i : Fin 64) (j : Fin 2) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[32,44] else #[33,12]) else (if i.val < 3 then #[34,45] else #[35,13])) else (if i.val < 6 then (if i.val < 5 then #[36,46] else #[37,14]) else (if i.val < 7 then #[38,47] else #[39,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[40,52] else #[41,20]) else (if i.val < 11 then #[42,53] else #[43,21])) else (if i.val < 14 then (if i.val < 13 then #[44,54] else #[45,22]) else (if i.val < 15 then #[46,55] else #[47,23])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[48,60] else #[49,28]) else (if i.val < 19 then #[50,61] else #[51,29])) else (if i.val < 22 then (if i.val < 21 then #[52,62] else #[53,30]) else (if i.val < 23 then #[54,63] else #[55,31]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[56,36] else #[57,4]) else (if i.val < 27 then #[58,37] else #[59,5])) else (if i.val < 30 then (if i.val < 29 then #[60,38] else #[61,6]) else (if i.val < 31 then #[62,39] else #[63,7]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,40] else #[1,8]) else (if i.val < 35 then #[2,41] else #[3,9])) else (if i.val < 38 then (if i.val < 37 then #[4,42] else #[5,10]) else (if i.val < 39 then #[6,43] else #[7,11]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[8,48] else #[9,16]) else (if i.val < 43 then #[10,49] else #[11,17])) else (if i.val < 46 then (if i.val < 45 then #[12,50] else #[13,18]) else (if i.val < 47 then #[14,51] else #[15,19])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[16,56] else #[17,24]) else (if i.val < 51 then #[18,57] else #[19,25])) else (if i.val < 54 then (if i.val < 53 then #[20,58] else #[21,26]) else (if i.val < 55 then #[22,59] else #[23,27]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[24,32] else #[25,0]) else (if i.val < 59 then #[26,33] else #[27,1])) else (if i.val < 62 then (if i.val < 61 then #[28,34] else #[29,2]) else (if i.val < 63 then #[30,35] else #[31,3])))))) : Array (Fin 64))[j.val]!
private def prevRow (i : Fin 64) (j : Fin 2) : Fin 64 :=
  ((if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[32,57] else #[33,59]) else (if i.val < 3 then #[34,61] else #[35,63])) else (if i.val < 6 then (if i.val < 5 then #[36,25] else #[37,27]) else (if i.val < 7 then #[38,29] else #[39,31]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[40,33] else #[41,35]) else (if i.val < 11 then #[42,37] else #[43,39])) else (if i.val < 14 then (if i.val < 13 then #[44,1] else #[45,3]) else (if i.val < 15 then #[46,5] else #[47,7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[48,41] else #[49,43]) else (if i.val < 19 then #[50,45] else #[51,47])) else (if i.val < 22 then (if i.val < 21 then #[52,9] else #[53,11]) else (if i.val < 23 then #[54,13] else #[55,15]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[56,49] else #[57,51]) else (if i.val < 27 then #[58,53] else #[59,55])) else (if i.val < 30 then (if i.val < 29 then #[60,17] else #[61,19]) else (if i.val < 31 then #[62,21] else #[63,23]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[0,56] else #[1,58]) else (if i.val < 35 then #[2,60] else #[3,62])) else (if i.val < 38 then (if i.val < 37 then #[4,24] else #[5,26]) else (if i.val < 39 then #[6,28] else #[7,30]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[8,32] else #[9,34]) else (if i.val < 43 then #[10,36] else #[11,38])) else (if i.val < 46 then (if i.val < 45 then #[12,0] else #[13,2]) else (if i.val < 47 then #[14,4] else #[15,6])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[16,40] else #[17,42]) else (if i.val < 51 then #[18,44] else #[19,46])) else (if i.val < 54 then (if i.val < 53 then #[20,8] else #[21,10]) else (if i.val < 55 then #[22,12] else #[23,14]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[24,48] else #[25,50]) else (if i.val < 59 then #[26,52] else #[27,54])) else (if i.val < 62 then (if i.val < 61 then #[28,16] else #[29,18]) else (if i.val < 63 then #[30,20] else #[31,22])))))) : Array (Fin 64))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T27
