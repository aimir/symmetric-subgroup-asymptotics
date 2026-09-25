import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T22

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T22

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,2,1,4,3,6,5,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,2,1,4,3,6,5,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,2,1,4,3,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,2,1,4,3,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator4 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,2,1,3,4,6,5,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,2,1,3,4,6,5,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 5) : Equiv.Perm (Fin 8) :=
  (if j.val < 2 then (if j.val < 1 then generator0 else generator1) else (if j.val < 3 then generator2 else (if j.val < 4 then generator3 else generator4)))

private def codes (i : Fin 32) : Fin (8^8) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1521751 else 1525391) else (if i.val < 3 then 1751183 else 1754711)) else (if i.val < 6 then (if i.val < 5 then 3038266 else 3042242) else (if i.val < 7 then 3268034 else 3271226))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5135809 else 5139001) else (if i.val < 11 then 5364793 else 5368769)) else (if i.val < 14 then (if i.val < 13 then 6623092 else 6648236) else (if i.val < 15 then 6852524 else 6877556)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8720299 else 8745331) else (if i.val < 19 then 8949619 else 8974763)) else (if i.val < 22 then (if i.val < 21 then 10720486 else 10724126) else (if i.val < 23 then 12326174 else 12329702))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12817693 else 12821221) else (if i.val < 27 then 14423269 else 14426909)) else (if i.val < 30 then (if i.val < 29 then 16201864 else 16205392) else (if i.val < 31 then 16431184 else 16434824)))))
private def ranks (i : Fin 32) : ℕ :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 8) else (if i.val < 3 then 9 else 21)) else (if i.val < 6 then (if i.val < 5 then 25 else 12) else (if i.val < 7 then 11 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 15) else (if i.val < 11 then 18 else 28)) else (if i.val < 14 then (if i.val < 13 then 14 else 26) else (if i.val < 15 then 3 else 13)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 7) else (if i.val < 19 then 29 else 20)) else (if i.val < 22 then (if i.val < 21 then 22 else 10) else (if i.val < 23 then 30 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 27 else 31) else (if i.val < 27 then 19 else 24)) else (if i.val < 30 then (if i.val < 29 then 17 else 5) else (if i.val < 31 then 4 else 0)))))
private def parents (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 31 else 0) else (if i.val < 3 then 0 else 1)) else (if i.val < 6 then (if i.val < 5 then 6 else 7) else (if i.val < 7 then 7 else 31))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 30) else (if i.val < 11 then 29 else 9)) else (if i.val < 14 then (if i.val < 13 then 14 else 15) else (if i.val < 15 then 31 else 14)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 0) else (if i.val < 19 then 16 else 17)) else (if i.val < 22 then (if i.val < 21 then 21 else 7) else (if i.val < 23 then 20 else 21))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 27) else (if i.val < 27 then 8 else 6)) else (if i.val < 30 then (if i.val < 29 then 30 else 31) else (if i.val < 31 then 31 else 31)))))
private def letters (i : Fin 32) : Fin 5 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 4 else 4)) else (if i.val < 6 then (if i.val < 5 then 4 else 4) else (if i.val < 7 then 3 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 1 else 4)) else (if i.val < 14 then (if i.val < 13 then 4 else 4) else (if i.val < 15 then 2 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 3 else 2) else (if i.val < 23 then 4 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 4) else (if i.val < 27 then 2 else 2)) else (if i.val < 30 then (if i.val < 29 then 4 else 4) else (if i.val < 31 then 3 else 0)))))
private def nextRow (i : Fin 32) (j : Fin 5) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[31,8,17,1,2] else #[30,6,15,0,3]) else (if i.val < 3 then #[29,5,19,3,0] else #[28,11,13,2,1])) else (if i.val < 6 then (if i.val < 5 then #[11,28,25,5,6] else #[10,2,23,4,7]) else (if i.val < 7 then #[9,1,27,7,4] else #[8,31,21,6,5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[7,0,26,9,10] else #[6,30,20,8,11]) else (if i.val < 11 then #[5,29,24,11,8] else #[4,3,22,10,9])) else (if i.val < 14 then (if i.val < 13 then #[19,24,29,13,14] else #[18,22,3,12,15]) else (if i.val < 15 then #[17,21,31,15,12] else #[16,27,1,14,13])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[15,20,30,17,18] else #[14,26,0,16,19]) else (if i.val < 19 then #[13,25,28,19,16] else #[12,23,2,18,17])) else (if i.val < 22 then (if i.val < 21 then #[27,16,9,21,22] else #[26,14,7,20,23]) else (if i.val < 23 then #[25,13,11,23,20] else #[24,19,5,22,21]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[23,12,10,25,26] else #[22,18,4,24,27]) else (if i.val < 27 then #[21,17,8,27,24] else #[20,15,6,26,25])) else (if i.val < 30 then (if i.val < 29 then #[3,4,18,29,30] else #[2,10,12,28,31]) else (if i.val < 31 then #[1,9,16,31,28] else #[0,7,14,30,29]))))) : Array (Fin 32))[j.val]!
private def prevRow (i : Fin 32) (j : Fin 5) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[31,8,17,1,2] else #[30,6,15,0,3]) else (if i.val < 3 then #[29,5,19,3,0] else #[28,11,13,2,1])) else (if i.val < 6 then (if i.val < 5 then #[11,28,25,5,6] else #[10,2,23,4,7]) else (if i.val < 7 then #[9,1,27,7,4] else #[8,31,21,6,5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[7,0,26,9,10] else #[6,30,20,8,11]) else (if i.val < 11 then #[5,29,24,11,8] else #[4,3,22,10,9])) else (if i.val < 14 then (if i.val < 13 then #[19,24,29,13,14] else #[18,22,3,12,15]) else (if i.val < 15 then #[17,21,31,15,12] else #[16,27,1,14,13])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[15,20,30,17,18] else #[14,26,0,16,19]) else (if i.val < 19 then #[13,25,28,19,16] else #[12,23,2,18,17])) else (if i.val < 22 then (if i.val < 21 then #[27,16,9,21,22] else #[26,14,7,20,23]) else (if i.val < 23 then #[25,13,11,23,20] else #[24,19,5,22,21]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[23,12,10,25,26] else #[22,18,4,24,27]) else (if i.val < 27 then #[21,17,8,27,24] else #[20,15,6,26,25])) else (if i.val < 30 then (if i.val < 29 then #[3,4,18,29,30] else #[2,10,12,28,31]) else (if i.val < 31 then #[1,9,16,31,28] else #[0,7,14,30,29]))))) : Array (Fin 32))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 32,
    i ≠ 31 → ranks (parents i) < ranks i := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
private theorem parent_next_checked : ∀ i : Fin 32,
    i ≠ 31 → nextRow (parents i) (letters i) = i := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 32 where
  rows := codes
  identity := 31
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (Fin.addCases (m := 15) (n := 16) (by decide +kernel) (by decide +kernel))

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 32 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 32) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 32 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T22
