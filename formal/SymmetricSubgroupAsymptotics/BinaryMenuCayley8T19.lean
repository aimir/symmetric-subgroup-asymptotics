import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T19

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T19

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
  toFun x := (#[2,1,0,4,5,6,3,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,1,0,6,3,4,5,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 4) : Equiv.Perm (Fin 8) :=
  (if j.val < 2 then (if j.val < 1 then generator0 else generator1) else (if j.val < 3 then generator2 else generator3))

private def codes (i : Fin 32) : Fin (8^8) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 941143 else 1238993) else (if i.val < 3 then 1521751 else 1690577)) else (if i.val < 6 then (if i.val < 5 then 3102904 else 3271226) else (if i.val < 7 then 3554488 else 3851834))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5135809 else 5432903) else (if i.val < 11 then 5716417 else 5884487)) else (if i.val < 14 then (if i.val < 13 then 6529964 else 6583598) else (if i.val < 15 then 6852524 else 8196398)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8433397 else 8745331) else (if i.val < 19 then 9143029 else 10229107)) else (if i.val < 22 then (if i.val < 21 then 10724126 else 10778012) else (if i.val < 23 then 11046686 else 12390812))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12627811 else 12939493) else (if i.val < 27 then 13337443 else 14423269)) else (if i.val < 30 then (if i.val < 29 then 15685642 else 15854216) else (if i.val < 31 then 16137226 else 16434824)))))
private def ranks (i : Fin 32) : ℕ :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 15 else 7) else (if i.val < 3 then 1 else 25)) else (if i.val < 6 then (if i.val < 5 then 26 else 2) else (if i.val < 7 then 9 else 18))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 28) else (if i.val < 11 then 20 else 11)) else (if i.val < 14 then (if i.val < 13 then 19 else 27) else (if i.val < 15 then 3 else 10)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 6) else (if i.val < 19 then 29 else 21)) else (if i.val < 22 then (if i.val < 21 then 8 else 16) else (if i.val < 23 then 22 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 31 else 24) else (if i.val < 27 then 17 else 14)) else (if i.val < 30 then (if i.val < 29 then 4 else 13) else (if i.val < 31 then 23 else 0)))))
private def parents (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 2) else (if i.val < 3 then 31 else 0)) else (if i.val < 6 then (if i.val < 5 then 7 else 31) else (if i.val < 7 then 5 else 6))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 10) else (if i.val < 11 then 11 else 28)) else (if i.val < 14 then (if i.val < 13 then 15 else 12) else (if i.val < 15 then 31 else 14)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 28 else 2) else (if i.val < 19 then 19 else 16)) else (if i.val < 22 then (if i.val < 21 then 5 else 20) else (if i.val < 23 then 29 else 22))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 30 else 0) else (if i.val < 27 then 6 else 8)) else (if i.val < 30 then (if i.val < 29 then 31 else 28) else (if i.val < 31 then 29 else 31)))))
private def letters (i : Fin 32) : Fin 4 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 3) else (if i.val < 3 then 0 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 1) else (if i.val < 7 then 3 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 3) else (if i.val < 11 then 3 else 0)) else (if i.val < 14 then (if i.val < 13 then 3 else 3) else (if i.val < 15 then 2 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 3 else 3)) else (if i.val < 22 then (if i.val < 21 then 2 else 3) else (if i.val < 23 then 2 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 2) else (if i.val < 27 then 2 else 2)) else (if i.val < 30 then (if i.val < 29 then 3 else 3) else (if i.val < 31 then 3 else 0)))))
private def nextRow (i : Fin 32) (j : Fin 4) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[29,10,25,3] else #[6,11,15,0]) else (if i.val < 3 then #[31,8,17,1] else #[4,9,23,2])) else (if i.val < 6 then (if i.val < 5 then #[3,30,18,5] else #[8,31,20,6]) else (if i.val < 7 then #[1,28,26,7] else #[10,29,12,4]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[5,2,27,11] else #[30,3,13,8]) else (if i.val < 11 then #[7,0,19,9] else #[28,1,21,10])) else (if i.val < 14 then (if i.val < 13 then #[19,22,7,13] else #[24,23,9,14]) else (if i.val < 15 then #[17,20,31,15] else #[26,21,1,12])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,26,28,19] else #[14,27,2,16]) else (if i.val < 19 then #[23,24,4,17] else #[12,25,10,18])) else (if i.val < 22 then (if i.val < 21 then #[27,14,5,21] else #[16,15,11,22]) else (if i.val < 23 then #[25,12,29,23] else #[18,13,3,20]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[13,18,30,27] else #[22,19,0,24]) else (if i.val < 27 then #[15,16,6,25] else #[20,17,8,26])) else (if i.val < 30 then (if i.val < 29 then #[11,6,16,29] else #[0,7,22,30]) else (if i.val < 31 then #[9,4,24,31] else #[2,5,14,28]))))) : Array (Fin 32))[j.val]!
private def prevRow (i : Fin 32) (j : Fin 4) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[29,10,25,1] else #[6,11,15,2]) else (if i.val < 3 then #[31,8,17,3] else #[4,9,23,0])) else (if i.val < 6 then (if i.val < 5 then #[3,30,18,7] else #[8,31,20,4]) else (if i.val < 7 then #[1,28,26,5] else #[10,29,12,6]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[5,2,27,9] else #[30,3,13,10]) else (if i.val < 11 then #[7,0,19,11] else #[28,1,21,8])) else (if i.val < 14 then (if i.val < 13 then #[19,22,7,15] else #[24,23,9,12]) else (if i.val < 15 then #[17,20,31,13] else #[26,21,1,14])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[21,26,28,17] else #[14,27,2,18]) else (if i.val < 19 then #[23,24,4,19] else #[12,25,10,16])) else (if i.val < 22 then (if i.val < 21 then #[27,14,5,23] else #[16,15,11,20]) else (if i.val < 23 then #[25,12,29,21] else #[18,13,3,22]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[13,18,30,25] else #[22,19,0,26]) else (if i.val < 27 then #[15,16,6,27] else #[20,17,8,24])) else (if i.val < 30 then (if i.val < 29 then #[11,6,16,31] else #[0,7,22,28]) else (if i.val < 31 then #[9,4,24,29] else #[2,5,14,30]))))) : Array (Fin 32))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T19
