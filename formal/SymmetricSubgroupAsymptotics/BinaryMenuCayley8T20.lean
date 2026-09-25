import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T20

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T20

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 32) : Fin (8^8) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 858613 else 1006033) else (if i.val < 3 then 1923313 else 2037973)) else (if i.val < 6 then (if i.val < 5 then 2206526 else 2353946) else (if i.val < 7 then 3271226 else 3385886))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4472167 else 4619587) else (if i.val < 11 then 5536867 else 5651527)) else (if i.val < 14 then (if i.val < 13 then 6852524 else 6999944) else (if i.val < 15 then 7917224 else 8031884)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9261553 else 9376213) else (if i.val < 19 then 10293493 else 10440913)) else (if i.val < 22 then (if i.val < 21 then 10609466 else 10724126) else (if i.val < 23 then 11641406 else 11788826))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12875107 else 12989767) else (if i.val < 27 then 13907047 else 14054467)) else (if i.val < 30 then (if i.val < 29 then 15255464 else 15370124) else (if i.val < 31 then 16287404 else 16434824)))))
private def ranks (i : Fin 32) : ℕ :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 2) else (if i.val < 3 then 4 else 6)) else (if i.val < 6 then (if i.val < 5 then 14 else 9) else (if i.val < 7 then 5 else 8))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 17 else 19) else (if i.val < 11 then 16 else 10)) else (if i.val < 14 then (if i.val < 13 then 26 else 22) else (if i.val < 15 then 25 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 31 else 29) else (if i.val < 19 then 30 else 28)) else (if i.val < 22 then (if i.val < 21 then 18 else 12) else (if i.val < 23 then 7 else 11))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 20 else 13) else (if i.val < 27 then 21 else 15)) else (if i.val < 30 then (if i.val < 29 then 1 else 27) else (if i.val < 31 then 24 else 0)))))
private def parents (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 28 else 31) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 7 else 6) else (if i.val < 7 then 1 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 11 else 23) else (if i.val < 11 then 5 else 6)) else (if i.val < 14 then (if i.val < 13 then 24 else 27) else (if i.val < 15 then 9 else 10)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 29 else 30) else (if i.val < 19 then 12 else 15)) else (if i.val < 22 then (if i.val < 21 then 23 else 22) else (if i.val < 23 then 0 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 22) else (if i.val < 27 then 25 else 7)) else (if i.val < 30 then (if i.val < 29 then 31 else 26) else (if i.val < 31 then 8 else 31)))))
private def letters (i : Fin 32) : Fin 2 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 1 else 1)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 1) else (if i.val < 19 then 1 else 1)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 1 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 1 else 1) else (if i.val < 27 then 0 else 1)) else (if i.val < 30 then (if i.val < 29 then 0 else 1) else (if i.val < 31 then 1 else 0)))))
private def nextRow (i : Fin 32) (j : Fin 2) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,22] else #[2,6]) else (if i.val < 3 then #[1,7] else #[0,23])) else (if i.val < 6 then (if i.val < 5 then #[7,26] else #[6,10]) else (if i.val < 7 then #[5,11] else #[4,27]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,30] else #[10,14]) else (if i.val < 11 then #[9,15] else #[8,31])) else (if i.val < 14 then (if i.val < 13 then #[15,18] else #[14,2]) else (if i.val < 15 then #[13,3] else #[12,19])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[19,4] else #[18,20]) else (if i.val < 19 then #[17,21] else #[16,5])) else (if i.val < 22 then (if i.val < 21 then #[23,8] else #[22,24]) else (if i.val < 23 then #[21,25] else #[20,9]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,12] else #[26,28]) else (if i.val < 27 then #[25,29] else #[24,13])) else (if i.val < 30 then (if i.val < 29 then #[31,0] else #[30,16]) else (if i.val < 31 then #[29,17] else #[28,1]))))) : Array (Fin 32))[j.val]!
private def prevRow (i : Fin 32) (j : Fin 2) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[3,28] else #[2,31]) else (if i.val < 3 then #[1,13] else #[0,14])) else (if i.val < 6 then (if i.val < 5 then #[7,16] else #[6,19]) else (if i.val < 7 then #[5,1] else #[4,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[11,20] else #[10,23]) else (if i.val < 11 then #[9,5] else #[8,6])) else (if i.val < 14 then (if i.val < 13 then #[15,24] else #[14,27]) else (if i.val < 15 then #[13,9] else #[12,10])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[19,29] else #[18,30]) else (if i.val < 19 then #[17,12] else #[16,15])) else (if i.val < 22 then (if i.val < 21 then #[23,17] else #[22,18]) else (if i.val < 23 then #[21,0] else #[20,3]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,21] else #[26,22]) else (if i.val < 27 then #[25,4] else #[24,7])) else (if i.val < 30 then (if i.val < 29 then #[31,25] else #[30,26]) else (if i.val < 31 then #[29,8] else #[28,11]))))) : Array (Fin 32))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T20
