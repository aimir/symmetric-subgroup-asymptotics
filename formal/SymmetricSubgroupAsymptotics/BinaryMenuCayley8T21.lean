import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T21

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T21

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,2,1,4,7,6,5,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,2,1,0,3,6,5,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 32) : Fin (8^8) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 358771 else 473431) else (if i.val < 3 then 1390711 else 1538131)) else (if i.val < 6 then (if i.val < 5 then 2206526 else 2353946) else (if i.val < 7 then 3271226 else 3385886))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5004769 else 5119429) else (if i.val < 11 then 6036709 else 6184129)) else (if i.val < 14 then (if i.val < 13 then 6852524 else 6999944) else (if i.val < 15 then 7917224 else 8031884)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8728951 else 8876371) else (if i.val < 19 then 9793651 else 9908311)) else (if i.val < 22 then (if i.val < 21 then 10609466 else 10724126) else (if i.val < 23 then 11641406 else 11788826))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 13374949 else 13522369) else (if i.val < 27 then 14439649 else 14554309)) else (if i.val < 30 then (if i.val < 29 then 15255464 else 15370124) else (if i.val < 31 then 16287404 else 16434824)))))
private def ranks (i : Fin 32) : ℕ :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 27 else 6) else (if i.val < 3 then 20 else 2)) else (if i.val < 6 then (if i.val < 5 then 5 else 16) else (if i.val < 7 then 3 else 17))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 23 else 9) else (if i.val < 11 then 24 else 8)) else (if i.val < 14 then (if i.val < 13 then 31 else 11) else (if i.val < 15 then 28 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 22) else (if i.val < 19 then 4 else 15)) else (if i.val < 22 then (if i.val < 21 then 21 else 29) else (if i.val < 23 then 18 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 13 else 26) else (if i.val < 27 then 12 else 25)) else (if i.val < 30 then (if i.val < 29 then 19 else 1) else (if i.val < 31 then 14 else 0)))))
private def parents (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 28 else 3) else (if i.val < 3 then 13 else 31)) else (if i.val < 6 then (if i.val < 5 then 29 else 15) else (if i.val < 7 then 31 else 11))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 19 else 6) else (if i.val < 11 then 5 else 3)) else (if i.val < 14 then (if i.val < 13 then 0 else 18) else (if i.val < 15 then 17 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 18 else 30) else (if i.val < 19 then 29 else 15)) else (if i.val < 22 then (if i.val < 21 then 24 else 10) else (if i.val < 23 then 9 else 27))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 22) else (if i.val < 27 then 18 else 7)) else (if i.val < 30 then (if i.val < 29 then 16 else 31) else (if i.val < 31 then 1 else 31)))))
private def letters (i : Fin 32) : Fin 3 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 2 else 2) else (if i.val < 7 then 2 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 2 else 1) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 1) else (if i.val < 19 then 1 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 1) else (if i.val < 23 then 1 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 1) else (if i.val < 27 then 2 else 1)) else (if i.val < 30 then (if i.val < 29 then 1 else 0) else (if i.val < 31 then 1 else 0)))))
private def nextRow (i : Fin 32) (j : Fin 3) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[2,12,27] else #[3,30,9]) else (if i.val < 3 then #[0,29,25] else #[1,15,11])) else (if i.val < 6 then (if i.val < 5 then #[6,24,29] else #[7,10,15]) else (if i.val < 7 then #[4,9,31] else #[5,27,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,4,19] else #[11,22,1]) else (if i.val < 11 then #[8,21,17] else #[9,7,3])) else (if i.val < 14 then (if i.val < 13 then #[14,16,21] else #[15,2,7]) else (if i.val < 15 then #[12,1,23] else #[13,19,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[18,28,24] else #[19,14,10]) else (if i.val < 19 then #[16,13,26] else #[17,31,8])) else (if i.val < 22 then (if i.val < 21 then #[22,8,30] else #[23,26,12]) else (if i.val < 23 then #[20,25,28] else #[21,11,14]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[26,20,16] else #[27,6,2]) else (if i.val < 27 then #[24,5,18] else #[25,23,0])) else (if i.val < 30 then (if i.val < 29 then #[30,0,22] else #[31,18,4]) else (if i.val < 31 then #[28,17,20] else #[29,3,6]))))) : Array (Fin 32))[j.val]!
private def prevRow (i : Fin 32) (j : Fin 3) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[2,28,27] else #[3,14,9]) else (if i.val < 3 then #[0,13,25] else #[1,31,11])) else (if i.val < 6 then (if i.val < 5 then #[6,8,29] else #[7,26,15]) else (if i.val < 7 then #[4,25,31] else #[5,11,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[10,20,19] else #[11,6,1]) else (if i.val < 11 then #[8,5,17] else #[9,23,3])) else (if i.val < 14 then (if i.val < 13 then #[14,0,21] else #[15,18,7]) else (if i.val < 15 then #[12,17,23] else #[13,3,5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[18,12,24] else #[19,30,10]) else (if i.val < 19 then #[16,29,26] else #[17,15,8])) else (if i.val < 22 then (if i.val < 21 then #[22,24,30] else #[23,10,12]) else (if i.val < 23 then #[20,9,28] else #[21,27,14]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[26,4,16] else #[27,22,2]) else (if i.val < 27 then #[24,21,18] else #[25,7,0])) else (if i.val < 30 then (if i.val < 29 then #[30,16,22] else #[31,2,4]) else (if i.val < 31 then #[28,1,20] else #[29,19,6]))))) : Array (Fin 32))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T21
