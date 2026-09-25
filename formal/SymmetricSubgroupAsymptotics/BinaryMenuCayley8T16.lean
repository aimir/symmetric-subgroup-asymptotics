import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T16

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T16

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 32) : Fin (8^8) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 874993 else 989653) else (if i.val < 3 then 1906933 else 2054353)) else (if i.val < 6 then (if i.val < 5 then 2206526 else 2353946) else (if i.val < 7 then 3271226 else 3385886))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4488547 else 4603207) else (if i.val < 11 then 5520487 else 5667907)) else (if i.val < 14 then (if i.val < 13 then 6852524 else 6999944) else (if i.val < 15 then 7917224 else 8031884)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9245173 else 9392593) else (if i.val < 19 then 10309873 else 10424533)) else (if i.val < 22 then (if i.val < 21 then 10609466 else 10724126) else (if i.val < 23 then 11641406 else 11788826))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12858727 else 13006147) else (if i.val < 27 then 13923427 else 14038087)) else (if i.val < 30 then (if i.val < 29 then 15255464 else 15370124) else (if i.val < 31 then 16287404 else 16434824)))))
private def ranks (i : Fin 32) : ℕ :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 6) else (if i.val < 3 then 3 else 2)) else (if i.val < 6 then (if i.val < 5 then 8 else 5) else (if i.val < 7 then 9 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 16) else (if i.val < 11 then 20 else 17)) else (if i.val < 14 then (if i.val < 13 then 18 else 25) else (if i.val < 15 then 28 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 29) else (if i.val < 19 then 31 else 30)) else (if i.val < 22 then (if i.val < 21 then 11 else 7) else (if i.val < 23 then 12 else 19))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 15 else 22) else (if i.val < 27 then 13 else 21)) else (if i.val < 30 then (if i.val < 29 then 1 else 27) else (if i.val < 31 then 24 else 0)))))
private def parents (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 2) else (if i.val < 3 then 28 else 31)) else (if i.val < 6 then (if i.val < 5 then 0 else 3) else (if i.val < 7 then 5 else 4))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 6) else (if i.val < 11 then 20 else 8)) else (if i.val < 14 then (if i.val < 13 then 8 else 11) else (if i.val < 15 then 25 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 15) else (if i.val < 19 then 29 else 30)) else (if i.val < 22 then (if i.val < 21 then 1 else 2) else (if i.val < 23 then 21 else 20))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 26) else (if i.val < 27 then 21 else 22)) else (if i.val < 30 then (if i.val < 29 then 31 else 10) else (if i.val < 31 then 24 else 31)))))
private def letters (i : Fin 32) : Fin 2 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 1 else 1)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 1 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 1) else (if i.val < 19 then 1 else 1)) else (if i.val < 22 then (if i.val < 21 then 1 else 1) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 0) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 0 else 1) else (if i.val < 31 then 1 else 0)))))
private def nextRow (i : Fin 32) (j : Fin 2) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,4] else #[2,20]) else (if i.val < 3 then #[1,21] else #[0,5])) else (if i.val < 6 then (if i.val < 5 then #[7,24] else #[6,8]) else (if i.val < 7 then #[5,9] else #[4,25]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,12] else #[10,28]) else (if i.val < 11 then #[9,29] else #[8,13])) else (if i.val < 14 then (if i.val < 13 then #[15,16] else #[14,0]) else (if i.val < 15 then #[13,1] else #[12,17])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[19,22] else #[18,6]) else (if i.val < 19 then #[17,7] else #[16,23])) else (if i.val < 22 then (if i.val < 21 then #[23,10] else #[22,26]) else (if i.val < 23 then #[21,27] else #[20,11]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,30] else #[26,14]) else (if i.val < 27 then #[25,15] else #[24,31])) else (if i.val < 30 then (if i.val < 29 then #[31,2] else #[30,18]) else (if i.val < 31 then #[29,19] else #[28,3]))))) : Array (Fin 32))[j.val]!
private def prevRow (i : Fin 32) (j : Fin 2) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,13] else #[2,14]) else (if i.val < 3 then #[1,28] else #[0,31])) else (if i.val < 6 then (if i.val < 5 then #[7,0] else #[6,3]) else (if i.val < 7 then #[5,17] else #[4,18]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,5] else #[10,6]) else (if i.val < 11 then #[9,20] else #[8,23])) else (if i.val < 14 then (if i.val < 13 then #[15,8] else #[14,11]) else (if i.val < 15 then #[13,25] else #[12,26])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[19,12] else #[18,15]) else (if i.val < 19 then #[17,29] else #[16,30])) else (if i.val < 22 then (if i.val < 21 then #[23,1] else #[22,2]) else (if i.val < 23 then #[21,16] else #[20,19]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,4] else #[26,7]) else (if i.val < 27 then #[25,21] else #[24,22])) else (if i.val < 30 then (if i.val < 29 then #[31,9] else #[30,10]) else (if i.val < 31 then #[29,24] else #[28,27]))))) : Array (Fin 32))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T16
