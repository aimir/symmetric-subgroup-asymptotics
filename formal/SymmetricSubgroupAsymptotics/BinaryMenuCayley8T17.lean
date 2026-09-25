import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T17

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T17

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,3,4,5,6,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,3,4,5,6,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 32) : Fin (8^8) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1006033 else 1174481) else (if i.val < 3 then 1457617 else 1755089)) else (if i.val < 6 then (if i.val < 5 then 3102778 else 3271226) else (if i.val < 7 then 3554362 else 3851834))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5199943 else 5368391) else (if i.val < 11 then 5651527 else 5948999)) else (if i.val < 14 then (if i.val < 13 then 6529964 else 6583724) else (if i.val < 15 then 6852524 else 8196524)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8626933 else 8680693) else (if i.val < 19 then 8949493 else 10293493)) else (if i.val < 22 then (if i.val < 21 then 10724126 else 10777886) else (if i.val < 23 then 11046686 else 12390686))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12821347 else 12875107) else (if i.val < 27 then 13143907 else 14487907)) else (if i.val < 30 then (if i.val < 29 then 15685768 else 15854216) else (if i.val < 31 then 16137352 else 16434824)))))
private def ranks (i : Fin 32) : ℕ :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 14 else 21) else (if i.val < 3 then 27 else 1)) else (if i.val < 6 then (if i.val < 5 then 19 else 26) else (if i.val < 7 then 30 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 29) else (if i.val < 11 then 31 else 6)) else (if i.val < 14 then (if i.val < 13 then 7 else 11) else (if i.val < 15 then 2 else 4)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 17) else (if i.val < 19 then 5 else 8)) else (if i.val < 22 then (if i.val < 21 then 18 else 23) else (if i.val < 23 then 9 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 25 else 28) else (if i.val < 27 then 15 else 20)) else (if i.val < 30 then (if i.val < 29 then 10 else 16) else (if i.val < 31 then 22 else 0)))))
private def parents (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 19 else 23) else (if i.val < 3 then 27 else 31)) else (if i.val < 6 then (if i.val < 5 then 16 else 20) else (if i.val < 7 then 24 else 3))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 21) else (if i.val < 11 then 25 else 7)) else (if i.val < 14 then (if i.val < 13 then 7 else 11) else (if i.val < 15 then 31 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 13) else (if i.val < 19 then 14 else 15)) else (if i.val < 22 then (if i.val < 21 then 16 else 17) else (if i.val < 23 then 18 else 19))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 20 else 21) else (if i.val < 27 then 22 else 23)) else (if i.val < 30 then (if i.val < 29 then 18 else 22) else (if i.val < 31 then 26 else 31)))))
private def letters (i : Fin 32) : Fin 2 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 1 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 1 else 1) else (if i.val < 31 then 1 else 0)))))
private def nextRow (i : Fin 32) (j : Fin 2) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,19] else #[5,23]) else (if i.val < 3 then #[6,27] else #[7,15])) else (if i.val < 6 then (if i.val < 5 then #[8,16] else #[9,20]) else (if i.val < 7 then #[10,24] else #[11,12]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[28,17] else #[29,21]) else (if i.val < 11 then #[30,25] else #[31,13])) else (if i.val < 14 then (if i.val < 13 then #[16,7] else #[17,11]) else (if i.val < 15 then #[18,31] else #[19,3])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[20,4] else #[21,8]) else (if i.val < 19 then #[22,28] else #[23,0])) else (if i.val < 22 then (if i.val < 21 then #[24,5] else #[25,9]) else (if i.val < 23 then #[26,29] else #[27,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[12,6] else #[13,10]) else (if i.val < 27 then #[14,30] else #[15,2])) else (if i.val < 30 then (if i.val < 29 then #[0,18] else #[1,22]) else (if i.val < 31 then #[2,26] else #[3,14]))))) : Array (Fin 32))[j.val]!
private def prevRow (i : Fin 32) (j : Fin 2) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[28,19] else #[29,23]) else (if i.val < 3 then #[30,27] else #[31,15])) else (if i.val < 6 then (if i.val < 5 then #[0,16] else #[1,20]) else (if i.val < 7 then #[2,24] else #[3,12]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[4,17] else #[5,21]) else (if i.val < 11 then #[6,25] else #[7,13])) else (if i.val < 14 then (if i.val < 13 then #[24,7] else #[25,11]) else (if i.val < 15 then #[26,31] else #[27,3])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[12,4] else #[13,8]) else (if i.val < 19 then #[14,28] else #[15,0])) else (if i.val < 22 then (if i.val < 21 then #[16,5] else #[17,9]) else (if i.val < 23 then #[18,29] else #[19,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[20,6] else #[21,10]) else (if i.val < 27 then #[22,30] else #[23,2])) else (if i.val < 30 then (if i.val < 29 then #[8,18] else #[9,22]) else (if i.val < 31 then #[10,26] else #[11,14]))))) : Array (Fin 32))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T17
