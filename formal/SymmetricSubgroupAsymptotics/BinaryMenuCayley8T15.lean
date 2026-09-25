import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate 8T15

Generated from the original menu permutations by export_lean_menu_cayley.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryMenuCayley8T15

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,4,3,2,1,0,7,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,4,3,2,1,0,7,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 32) : Fin (8^8) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 342391 else 989653) else (if i.val < 3 then 1407091 else 2054353)) else (if i.val < 6 then (if i.val < 5 then 2353946 else 2739128) else (if i.val < 7 then 3385886 else 3771068))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4488547 else 5135809) else (if i.val < 11 then 5520487 else 6167749)) else (if i.val < 14 then (if i.val < 13 then 6467342 else 6852524) else (if i.val < 15 then 7532042 else 7917224)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 8859991 else 9245173) else (if i.val < 19 then 9924691 else 10309873)) else (if i.val < 22 then (if i.val < 21 then 10609466 else 11256728) else (if i.val < 23 then 11641406 else 12288668))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 13006147 else 13391329) else (if i.val < 27 then 14038087 else 14423269)) else (if i.val < 30 then (if i.val < 29 then 14722862 else 15370124) else (if i.val < 31 then 15787562 else 16434824)))))
private def ranks (i : Fin 32) : ℕ :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 5) else (if i.val < 3 then 29 else 1)) else (if i.val < 6 then (if i.val < 5 then 4 else 26) else (if i.val < 7 then 12 else 22))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 11 else 19) else (if i.val < 11 then 25 else 8)) else (if i.val < 14 then (if i.val < 13 then 15 else 24) else (if i.val < 15 then 31 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 28 else 17) else (if i.val < 19 then 20 else 7)) else (if i.val < 22 then (if i.val < 21 then 14 else 18) else (if i.val < 23 then 30 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 27 else 10) else (if i.val < 27 then 21 else 3)) else (if i.val < 30 then (if i.val < 29 then 6 else 2) else (if i.val < 31 then 16 else 0)))))
private def parents (i : Fin 32) : Fin 32 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 4 else 3) else (if i.val < 3 then 0 else 31)) else (if i.val < 6 then (if i.val < 5 then 3 else 8) else (if i.val < 7 then 4 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 4 else 11) else (if i.val < 11 then 8 else 29)) else (if i.val < 14 then (if i.val < 13 then 1 else 8) else (if i.val < 15 then 12 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 19) else (if i.val < 19 then 23 else 29)) else (if i.val < 22 then (if i.val < 21 then 1 else 11) else (if i.val < 23 then 20 else 27))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6 else 27) else (if i.val < 27 then 23 else 31)) else (if i.val < 30 then (if i.val < 29 then 3 else 31) else (if i.val < 31 then 28 else 31)))))
private def letters (i : Fin 32) : Fin 3 :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 2 else 1) else (if i.val < 3 then 1 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 2) else (if i.val < 7 then 1 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 1 else 2)) else (if i.val < 14 then (if i.val < 13 then 2 else 0) else (if i.val < 15 then 1 else 2)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 2 else 1) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 1 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 1) else (if i.val < 27 then 2 else 2)) else (if i.val < 30 then (if i.val < 29 then 2 else 1) else (if i.val < 31 then 1 else 0)))))
private def nextRow (i : Fin 32) (j : Fin 3) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[28,2,4] else #[20,3,12]) else (if i.val < 3 then #[12,0,20] else #[4,1,28])) else (if i.val < 6 then (if i.val < 5 then #[8,6,0] else #[0,7,8]) else (if i.val < 7 then #[24,4,16] else #[16,5,24]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,10,5] else #[5,11,13]) else (if i.val < 11 then #[29,8,21] else #[21,9,29])) else (if i.val < 14 then (if i.val < 13 then #[25,14,1] else #[17,15,9]) else (if i.val < 15 then #[9,12,17] else #[1,13,25])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[30,18,6] else #[22,19,14]) else (if i.val < 19 then #[14,16,22] else #[6,17,30])) else (if i.val < 22 then (if i.val < 21 then #[10,22,2] else #[2,23,10]) else (if i.val < 23 then #[26,20,18] else #[18,21,26]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[15,26,7] else #[7,27,15]) else (if i.val < 27 then #[31,24,23] else #[23,25,31])) else (if i.val < 30 then (if i.val < 29 then #[27,30,3] else #[19,31,11]) else (if i.val < 31 then #[11,28,19] else #[3,29,27]))))) : Array (Fin 32))[j.val]!
private def prevRow (i : Fin 32) (j : Fin 3) : Fin 32 :=
  ((if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[5,2,4] else #[15,3,12]) else (if i.val < 3 then #[21,0,20] else #[31,1,28])) else (if i.val < 6 then (if i.val < 5 then #[3,6,0] else #[9,7,8]) else (if i.val < 7 then #[19,4,16] else #[25,5,24]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[4,10,5] else #[14,11,13]) else (if i.val < 11 then #[20,8,21] else #[30,9,29])) else (if i.val < 14 then (if i.val < 13 then #[2,14,1] else #[8,15,9]) else (if i.val < 15 then #[18,12,17] else #[24,13,25])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[7,18,6] else #[13,19,14]) else (if i.val < 19 then #[23,16,22] else #[29,17,30])) else (if i.val < 22 then (if i.val < 21 then #[1,22,2] else #[11,23,10]) else (if i.val < 23 then #[17,20,18] else #[27,21,26]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[6,26,7] else #[12,27,15]) else (if i.val < 27 then #[22,24,23] else #[28,25,31])) else (if i.val < 30 then (if i.val < 29 then #[0,30,3] else #[10,31,11]) else (if i.val < 31 then #[16,28,19] else #[26,29,27]))))) : Array (Fin 32))[j.val]!

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

end SymmetricSubgroupAsymptotics.BinaryMenuCayley8T15
